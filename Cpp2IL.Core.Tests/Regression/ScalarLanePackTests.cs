using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: scalar<->vector lanes - the ARM64 ABI spreads a flat
// float-aggregate argument one lane per register (a Vector3 call argument lives
// in v0.s0, v1.s0, v2.s0). The calling-convention model exposes only the first
// register for the whole parameter, so the sibling lane definitions are
// unreachable and die before type resolution: the vector slot then sees a lone
// scalar and degrades to a diagnosed synthetic default. While the lane
// definitions are still present their producers prove the lane values - the
// operand can be rebuilt as a Vector128Literal or a field-by-field packed local.
public class ScalarLanePackTests
{
    private static InjectedTypeAnalysisContext Vector3(ApplicationAnalysisContext app)
    {
        var vector = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "UnityEngine", "Vector3", app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        var offset = 0;
        foreach (var name in new[] { "x", "y", "z" })
        {
            vector.Fields.Add(new InjectedFieldAnalysisContext(name, app.SystemTypes.SystemSingleType,
                R.FieldAttributes.Public, vector, offset));
            offset += 4;
        }

        return vector;
    }

    private static MethodAnalysisContext Echo(ApplicationAnalysisContext app, ModuleDefinition module,
        InjectedTypeAnalysisContext vector)
    {
        var vectorDef = vector.GetExtraData<TypeDefinition>("AsmResolverType")!;
        foreach (var field in vector.Fields.OfType<InjectedFieldAnalysisContext>())
        {
            var fieldDefinition = new FieldDefinition(field.Name, FieldAttributes.Public,
                new FieldSignature(module.CorLibTypeFactory.Single));
            vectorDef.Fields.Add(fieldDefinition);
            field.PutExtraData("AsmResolverField", fieldDefinition);
        }

        var vectorSig = vectorDef.ToTypeSignature();
        var ctorDef = new MethodDefinition(".ctor",
            MethodAttributes.Public | MethodAttributes.HideBySig | MethodAttributes.SpecialName
                | MethodAttributes.RuntimeSpecialName,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void,
                [module.CorLibTypeFactory.Single, module.CorLibTypeFactory.Single,
                    module.CorLibTypeFactory.Single]));
        vectorDef.Methods.Add(ctorDef);
        var ctor = vector.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig | R.MethodAttributes.SpecialName
                | R.MethodAttributes.RTSpecialName,
            app.SystemTypes.SystemSingleType, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemSingleType);
        ctor.PutExtraData("AsmResolverMethod", ctorDef);

        var holder = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Library", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var holderDef = new TypeDefinition("Tests", "Library",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(holderDef);
        holder.PutExtraData("AsmResolverType", holderDef);
        var echoDef = new MethodDefinition("Echo",
            MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.HideBySig,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [vectorSig]));
        holderDef.Methods.Add(echoDef);
        var echo = holder.InjectMethodContext("Echo", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static | R.MethodAttributes.HideBySig,
            vector);
        echo.PutExtraData("AsmResolverMethod", echoDef);
        return echo;
    }

    [Test]
    public void ConstantLanesRebuildVectorArgument()
    {
        // `fmov s0, wzr; fmov s1, wzr; fmov s2, wzr; bl Echo` - each lane is a
        // proven zero, so the argument is `new Vector3(0f, 0f, 0f)`, not a
        // scalar coerced into the vector slot.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = Vector3(app);
        var module = new ModuleDefinition("LanePack.dll");
        SeedCorLibTypes(app, module, vector, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemSingleType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType);
        var echo = Echo(app, module, vector);

        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new Register(null, "V0"), new Immediate(0)),
            new(1, OpCode.Move, new Register(null, "V1"), new Immediate(0)),
            new(2, OpCode.Move, new Register(null, "V2"), new Immediate(0)),
            new(3, OpCode.CallVoid, echo, new Register(null, "V0")),
            new(4, OpCode.Return)], []);
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph!);

        LocalVariables.CreateAll(caller);
        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Newobj
                    && i.Operand is IMethodDescriptor named
                    && named.Name?.ToString() == ".ctor"), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand is IMethodDescriptor named
                    && named.Name?.ToString() == "Echo"), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr && i.Operand is string text
                    && text.Contains("synthetic default value")), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void ScalarLanesPackVectorArgumentFieldByField()
    {
        // `ldr s0, [holder]; ldr s1, [holder+4]; ldr s2, [holder+8]; bl Echo` -
        // the lanes are resolved field reads, so the argument is a local whose
        // x, y and z fields each get their proven lane store.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = Vector3(app);
        var module = new ModuleDefinition("LanePack.dll");
        SeedCorLibTypes(app, module, vector, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemSingleType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType);
        var echo = Echo(app, module, vector);
        var holder = new LocalVariable("holder", new Register(null, "holder"), vector);
        var fields = vector.Fields.OfType<InjectedFieldAnalysisContext>().ToList();

        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new Register(null, "V0"), new FieldReference(fields[0], holder, 0)),
            new(1, OpCode.Move, new Register(null, "V1"), new FieldReference(fields[1], holder, 4)),
            new(2, OpCode.Move, new Register(null, "V2"), new FieldReference(fields[2], holder, 8)),
            new(6, OpCode.CallVoid, echo, new Register(null, "V0")),
            new(7, OpCode.Return)], [holder]);
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph!);

        LocalVariables.CreateAll(caller);
        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            var stores = il.Where(i => i.OpCode == CilOpCodes.Stfld).ToList();
            Assert.That(stores, Has.Count.EqualTo(3),
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(stores.Select(i => (i.Operand as IFieldDescriptor)?.Name?.ToString())
                    .Order(), Is.EqualTo(new[] { "x", "y", "z" }),
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand is IMethodDescriptor named
                    && named.Name?.ToString() == "Echo"), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr && i.Operand is string text
                    && text.Contains("synthetic default value")), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void OutParameterLaneStoreKeepsDiagnostic()
    {
        // `str s0, [result.x]` writes only lane x of an `out Vector3` referent.
        // Splitting the vector source to lane x would let the emitter collapse
        // the unspellable leaf into a partial member write `result.x = vec.x` -
        // legal C# only when every lane of `result` ends up assigned, otherwise
        // CS0177 control never emitted. The destination stays unproven and keeps
        // control's `Inaccessible field store` diagnostic.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = Vector3(app);
        var module = new ModuleDefinition("LanePack.dll");
        SeedCorLibTypes(app, module, vector, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemSingleType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType);
        Echo(app, module, vector);
        var fields = vector.Fields.OfType<InjectedFieldAnalysisContext>().ToList();
        var mValue = new InjectedFieldAnalysisContext("m_value",
            app.SystemTypes.SystemSingleType, R.FieldAttributes.Private,
            app.SystemTypes.SystemSingleType, 0);
        var outLocal = new LocalVariable("result", new Register(0, "X0"),
            new ByRefTypeAnalysisContext(vector));
        var vectorLocal = new LocalVariable("vec", new Register(8, "X8"), vector);

        var callerType = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "OutStore", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = callerType.InjectMethodContext("Run", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static,
            new ByRefTypeAnalysisContext(vector));
        caller.Parameters[0].Attributes = R.ParameterAttributes.Out;
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move,
                new FieldReference(mValue, outLocal, 0, [fields[0]]), vectorLocal),
            new Instruction(1, OpCode.Return)]);
        caller.Locals = [outLocal, vectorLocal];
        caller.ParameterOperands = [new Register(0, "X0")];
        caller.AnalysisWarnings = [];
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph);

        var type = new TypeDefinition("Tests", "OutStore", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var vectorSig = vector.GetExtraData<TypeDefinition>("AsmResolverType")!.ToTypeSignature();
        var method = new MethodDefinition("Run",
            MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.HideBySig,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
                [vectorSig.MakeByReferenceType()]));
        type.Methods.Add(method);

        LocalVariables.CreateAll(caller);
        // CreateAll rebuilds ParameterLocals from registers the CFG reaches; in
        // a real method the out parameter's local is named back into it.
        caller.ParameterLocals = [outLocal];
        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr && i.Operand is string text
                    && text.Contains("Inaccessible field store")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Throw), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld
                    && (i.Operand as IFieldDescriptor)?.Name?.ToString() == "x"), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void UnspellableLaneLeafKeepsNamedConversion()
    {
        // `fmov s5, v.x` where the `x` member leaf cannot be spelled (a private
        // storage member under a likewise private container): the Single slot
        // still gets its default, but the note names the operand conversion -
        // "No legal conversion from UnityEngine.Vector3 operand to
        // System.Single slot" - instead of an anonymous slot fill.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = Vector3(app);
        var module = new ModuleDefinition("LanePack.dll");
        SeedCorLibTypes(app, module, vector, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemSingleType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType);
        Echo(app, module, vector);
        var container = new InjectedFieldAnalysisContext("x",
            app.SystemTypes.SystemSingleType, R.FieldAttributes.Private, vector, 0);
        var mValue = new InjectedFieldAnalysisContext("m_value",
            app.SystemTypes.SystemSingleType, R.FieldAttributes.Private,
            app.SystemTypes.SystemSingleType, 0);
        var vecLocal = new LocalVariable("vec", new Register(0, "X8"), vector);
        var dstLocal = new LocalVariable("dst", new Register(0, "V0"),
            app.SystemTypes.SystemSingleType);

        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, dstLocal, new FieldReference(mValue, vecLocal, 0, [container])),
            new(1, OpCode.Return)], [vecLocal, dstLocal]);
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph!);

        LocalVariables.CreateAll(caller);
        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr && i.Operand is string text
                    && text.Contains("No legal conversion from UnityEngine.Vector3 operand"
                        + " to System.Single slot")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr && i.Operand is string text
                    && text.Contains("Operand slot of type System.Single filled")), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }
}
