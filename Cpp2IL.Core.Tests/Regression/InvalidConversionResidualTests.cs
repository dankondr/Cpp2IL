using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Model.CustomAttributes;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: compile bucket invalid-conversion - residual shapes after
// the isinst-behind-Il2CppClass and vector-binop clusters (castle-recovery#122).
//
// `isinst`/`castclass` require an object reference; a value type, pointer or
// managed pointer operand is a lifter mistype of the native register, so the
// cast slot takes a diagnosed default rather than invalid IL. A vector op
// result stored into a scalar-contract local must be coerced before the store
// or the raw call result lands in a Double/Single slot. A ref struct generic
// instance (e.g. ReadOnlySpan<T>) carries IsByRefLike only on its definition -
// box/unbox on the instance is illegal IL. An untyped local defined only by
// calls takes the call return type; a numeric consumer is a use-site view, not
// a definition.
public class InvalidConversionResidualTests
{
    private static InjectedTypeAnalysisContext InjectWidget(ApplicationAnalysisContext app)
        => new(app.AssembliesByName["UnityEngine.CoreModule"], "Tests", "Widget",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);

    // A caller with one declared parameter: ldarg sites keep the declared
    // parameter type even when the only use is a cast source, which is where
    // `ldarg <scalar>; isinst T` escapes the cast-source slot typing.
    private static (MethodAnalysisContext caller, MethodDefinition method) ParamCaller(
        ApplicationAnalysisContext app, ModuleDefinition module,
        TypeAnalysisContext parameterType, string parameterName,
        TypeSignature parameterSignature,
        System.Collections.Generic.List<Instruction> instructions,
        System.Collections.Generic.List<LocalVariable> locals)
    {
        var callerType = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "CastCaller", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = new InjectedMethodAnalysisContext(callerType, "Run",
            app.SystemTypes.SystemVoidType, R.MethodAttributes.Public | R.MethodAttributes.Static,
            [parameterType], [parameterName]);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        caller.Locals = locals;
        caller.ParameterLocals = locals.Take(1).ToList();
        caller.AnalysisWarnings = [];
        var type = new TypeDefinition("Tests", "CastCaller",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [parameterSignature]));
        method.ParameterDefinitions.Add(new ParameterDefinition(1, parameterName, 0));
        type.Methods.Add(method);
        return (caller, method);
    }

    private static void AssertCastDroppedToDefault(MethodDefinition method, CilOpCode opcode)
    {
        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == opcode), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text
                    && text.Contains("not an object reference")), Is.True,
                "the dropped cast stays an explicit diagnostic");
        });
    }

    [Test]
    public void IsInstOnIntArgumentEmitsDiagnosedDefault()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var widget = InjectWidget(app);
        var index = new LocalVariable("index", new Register(null, "x0"))
            { Type = app.SystemTypes.SystemInt32Type };
        var slot = new LocalVariable("slot", new Register(null, "v0")) { Type = widget };
        var module = new ModuleDefinition("Casts.dll");
        SeedCorLibTypes(app, module, widget, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ParamCaller(app, module, app.SystemTypes.SystemInt32Type, "index",
            module.CorLibTypeFactory.Int32,
            [new(0, OpCode.Move, slot, new ReferenceCast(index, widget, nullOnFailure: true)),
             new(1, OpCode.Return)],
            [index, slot]);

        IlGenerator.GenerateIl(caller, method);

        AssertCastDroppedToDefault(method, CilOpCodes.Isinst);
    }

    [Test]
    public void IsInstOnInferredArgumentLocalEmitsDiagnosedDefault()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var widget = InjectWidget(app);
        var index = new LocalVariable("index", new Register(null, "x0"))
            { Type = app.SystemTypes.SystemInt32Type };
        // Copy propagation erased the argument's defining instruction and left
        // only this argument-register local: LoadLocal resolves it to `ldarg
        // index` because Int32 matches exactly one declared parameter, so its
        // emitted stack type is the parameter type, not a cast-source Object.
        var scratch = new LocalVariable("scratch", new Register(null, "x1_v4"))
            { Type = app.SystemTypes.SystemInt32Type };
        var slot = new LocalVariable("slot", new Register(null, "v0")) { Type = widget };
        var module = new ModuleDefinition("Casts.dll");
        SeedCorLibTypes(app, module, widget, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ParamCaller(app, module, app.SystemTypes.SystemInt32Type, "index",
            module.CorLibTypeFactory.Int32,
            [new(0, OpCode.Move, slot, new ReferenceCast(scratch, widget, nullOnFailure: true)),
             new(1, OpCode.Return)],
            [index, scratch, slot]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            AssertCastDroppedToDefault(method, CilOpCodes.Isinst);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldarg
                    || i.OpCode.ToString().Contains("ldarg")), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void IsInstOnEnumArgumentEmitsDiagnosedDefault()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var mscorlib = app.AssembliesByName["mscorlib"];
        var enumBase = mscorlib.GetTypeByFullName("System.Enum")
            ?? new InjectedTypeAnalysisContext(mscorlib, "System", "Enum",
                app.SystemTypes.SystemValueTypeType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var choice = new InjectedTypeAnalysisContext(mscorlib, "Tests", "Choice",
            enumBase, R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        var widget = InjectWidget(app);
        var language = new LocalVariable("language", new Register(null, "x0")) { Type = choice };
        var slot = new LocalVariable("slot", new Register(null, "v0")) { Type = widget };
        var module = new ModuleDefinition("Casts.dll");
        SeedCorLibTypes(app, module, widget, choice,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var choiceSig = choice.GetExtraData<TypeDefinition>("AsmResolverType")!.ToTypeSignature();
        var (caller, method) = ParamCaller(app, module, choice, "language", choiceSig,
            [new(0, OpCode.Move, slot, new ReferenceCast(language, widget, nullOnFailure: true)),
             new(1, OpCode.Return)],
            [language, slot]);

        IlGenerator.GenerateIl(caller, method);

        AssertCastDroppedToDefault(method, CilOpCodes.Isinst);
    }

    [Test]
    public void CastclassOnPointerOperandEmitsDiagnosedDefault()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var widget = InjectWidget(app);
        var pointer = new LocalVariable("pointer", new Register(null, "x0"))
            { Type = new PointerTypeAnalysisContext(app.SystemTypes.SystemInt32Type) };
        var slot = new LocalVariable("slot", new Register(null, "v0")) { Type = widget };
        var module = new ModuleDefinition("Casts.dll");
        SeedCorLibTypes(app, module, widget, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemIntPtrType,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ParamCaller(app, module, app.SystemTypes.SystemIntPtrType, "pointer",
            module.CorLibTypeFactory.IntPtr,
            [new(0, OpCode.Move, slot, new ReferenceCast(pointer, widget)),
             new(1, OpCode.Return)],
            [pointer, slot]);

        IlGenerator.GenerateIl(caller, method);

        AssertCastDroppedToDefault(method, CilOpCodes.Castclass);
    }

    [Test]
    public void ByRefLikeGenericInstanceIntoObjectSlotDefaultsInsteadOfBoxing()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var mscorlib = app.AssembliesByName["mscorlib"];
        var attribute = new InjectedTypeAnalysisContext(mscorlib,
            "System.Runtime.CompilerServices", "IsByRefLikeAttribute",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class | R.TypeAttributes.Sealed);
        var attributeCtor = attribute.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig
                | R.MethodAttributes.SpecialName | R.MethodAttributes.RTSpecialName);
        var refStructDef = new InjectedTypeAnalysisContext(mscorlib, "Tests", "ByRefBuffer`1",
            app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        refStructDef.CustomAttributes = [new AnalyzedCustomAttribute(attributeCtor)];
        // The instance carries no custom attributes of its own; IsByRefLike
        // lives on the definition, so the instance must resolve through it.
        var instance = new GenericInstanceTypeAnalysisContext(refStructDef,
            [app.SystemTypes.SystemByteType]);
        var span = new LocalVariable("span", new Register(null, "span")) { Type = instance };
        var slot = new LocalVariable("slot", new Register(null, "slot"))
            { Type = app.SystemTypes.SystemObjectType };
        var module = new ModuleDefinition("RefStruct.dll");
        SeedCorLibTypes(app, module, refStructDef, app.SystemTypes.SystemByteType,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, span),
            new(1, OpCode.Return)], [span, slot]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Box), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text
                    && text.Contains("Ref struct cannot cross")), Is.True,
                "the dropped ref struct must stay an explicit diagnostic");
        });
    }

    [Test]
    public void VectorOpResultIntoScalarSlotEmitsDiagnosedDefault()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "UnityEngine", "Vector3", app.SystemTypes.SystemValueTypeType, R.TypeAttributes.Public);
        var vec = new LocalVariable("vec", new Register(null, "vec")) { Type = vector };
        var scalar = new LocalVariable("scalar", new Register(null, "scalar"))
            { Type = app.SystemTypes.SystemSingleType };
        // The result register was smeared to Double by a numeric consumer -
        // the vector operand still proves the operator's result is a vector.
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemDoubleType };
        var module = new ModuleDefinition("VectorOps.dll");
        SeedCorLibTypes(app, module, vector, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        var vectorDef = vector.GetExtraData<TypeDefinition>("AsmResolverType")!;
        var vectorSig = vectorDef.ToTypeSignature();
        var opDef = new MethodDefinition("op_Multiply",
            MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.SpecialName
                | MethodAttributes.HideBySig,
            MethodSignature.CreateStatic(vectorSig, [vectorSig, module.CorLibTypeFactory.Single]));
        vectorDef.Methods.Add(opDef);
        var opMultiply = vector.InjectMethodContext("op_Multiply", vector,
            R.MethodAttributes.Public | R.MethodAttributes.Static | R.MethodAttributes.SpecialName
                | R.MethodAttributes.HideBySig,
            vector, app.SystemTypes.SystemSingleType);
        opMultiply.PutExtraData("AsmResolverMethod", opDef);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Multiply, result, vec, scalar),
            new(1, OpCode.Return)], [vec, scalar, result]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString().Contains("op_Multiply") == true), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            // The vector result cannot land in a Double slot: the call result
            // is dropped and the slot takes a diagnosed default instead of an
            // unverifiable stloc.
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Pop), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr && i.Operand is string text
                    && text.Contains("synthetic default value")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void UntypedCallResultLocalTakesCallReturnType()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var producer = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Producer", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var produce = producer.InjectMethodContext("Produce", app.SystemTypes.SystemStringType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig);
        var holder = new LocalVariable("holder", new Register(null, "holder")) { Type = producer };
        // Untyped local defined only by the call; its `& 1` consumer would
        // otherwise smear the slot to Int32 and the `stloc` of the String
        // result would be unverifiable.
        var result = new LocalVariable("result", new Register(null, "result"));
        var masked = new LocalVariable("masked", new Register(null, "masked"))
            { Type = app.SystemTypes.SystemInt32Type };
        var module = new ModuleDefinition("Calls.dll");
        SeedCorLibTypes(app, module, producer, app.SystemTypes.SystemStringType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        var producerDef = producer.GetExtraData<TypeDefinition>("AsmResolverType")!;
        var produceDef = new MethodDefinition("Produce",
            MethodAttributes.Public | MethodAttributes.HideBySig,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.String));
        producerDef.Methods.Add(produceDef);
        produce.PutExtraData("AsmResolverMethod", produceDef);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Call, produce, result, holder),
            new(1, OpCode.And, masked, result, new Immediate(1)),
            new(2, OpCode.Return)], [holder, result, masked]);

        IlGenerator.GenerateIl(caller, method);

        var localTypes = method.CilMethodBody!.LocalVariables
            .Select(local => local.VariableType.FullName)
            .ToList();
        Assert.That(localTypes, Has.Some.Contains("String"),
            () => string.Join(", ", localTypes));
    }
}
