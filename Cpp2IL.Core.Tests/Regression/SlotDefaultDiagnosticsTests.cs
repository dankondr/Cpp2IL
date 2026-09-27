using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: default-substitution diagnostics (castle-recovery#90).
// A slot load that can never satisfy its contract substitutes default(contract)
// or a fabricated local address. These substitutions used to be silent, so the
// method read as clean output; every such site must now emit the
// codeverify-visible decompiler-issue call (ldstr <Diagnostic> + call) that
// counts the method as incomplete.
public class SlotDefaultDiagnosticsTests
{
    private static InjectedTypeAnalysisContext InjectStruct(ApplicationAnalysisContext app, string name) =>
        new(app.AssembliesByName["mscorlib"], "Tests", name,
            app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);

    [Test]
    public void UnloadableOperandIntoStructSlotEmitsSubstitutionDiagnostic()
    {
        // A literal can never fill a non-primitive value-type slot, so
        // LoadOperandIntoSlot substitutes default(Struct) for it.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var structType = InjectStruct(app, "Point");
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = structType };
        var module = new ModuleDefinition("StructSlot.dll");
        SeedCorLibTypes(app, module, structType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, new Immediate(4)),
            new(1, OpCode.Return)], [slot]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("synthetic default")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call), Is.True,
                "the diagnostic must be an emitted call, not just a string");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initobj), Is.True,
                "the substituted slot still carries the struct default");
        });
    }

    [Test]
    public void LiteralIntoRefSlotEmitsSubstitutionDiagnostic()
    {
        // A literal cannot produce a managed pointer; the ref/out slot gets the
        // address of a fresh zero-initialized local.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var structType = InjectStruct(app, "PointRef");
        var slot = new LocalVariable("slot", new Register(null, "slot"))
            { Type = new ByRefTypeAnalysisContext(structType) };
        var module = new ModuleDefinition("RefSlot.dll");
        SeedCorLibTypes(app, module, structType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, new Immediate(4)),
            new(1, OpCode.Return)], [slot]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("substituting")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call), Is.True,
                "the diagnostic must be an emitted call, not just a string");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldloca), Is.True,
                "the substituted ref slot still carries a local address");
        });
    }

    [Test]
    public void CtorPrologueDiagnosticRunsAfterBaseConstructorCall()
    {
        // The synthesized base-ctor prologue fills a missing argument with a
        // default; the diagnostic must land after the call — a note in front of
        // it stops the decompiler folding the constructor initializer and the
        // body comes out referencing an uncallable `base._002Ector(...)`.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];
        var baseType = new InjectedTypeAnalysisContext(assembly, "Tests", "Base",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var derived = new InjectedTypeAnalysisContext(assembly, "Tests", "Derived",
            baseType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var baseCtor = baseType.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public, app.SystemTypes.SystemInt32Type);
        var caller = derived.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public);
        caller.ControlFlowGraph = new ISILControlFlowGraph([new(0, OpCode.Return)]);
        caller.Locals = [];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];

        var module = new ModuleDefinition("CtorPrologue.dll");
        var baseTypeDef = new TypeDefinition("Tests", "Base",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(baseTypeDef);
        var baseCtorDef = new MethodDefinition(".ctor",
            MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.Int32]));
        baseTypeDef.Methods.Add(baseCtorDef);
        baseCtor.PutExtraData("AsmResolverMethod", baseCtorDef);
        var derivedTypeDef = new TypeDefinition("Tests", "Derived",
            TypeAttributes.Public | TypeAttributes.Class, baseTypeDef.ToTypeReference());
        module.TopLevelTypes.Add(derivedTypeDef);
        var method = new MethodDefinition(".ctor",
            MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        derivedTypeDef.Methods.Add(method);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il[0].OpCode, Is.EqualTo(CilOpCodes.Ldarg_0),
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il[1].OpCode, Is.EqualTo(CilOpCodes.Ldc_I4_0));
            Assert.That(il[2].OpCode, Is.EqualTo(CilOpCodes.Call),
                "the base-ctor call keeps the head position so it stays a constructor initializer");
            Assert.That(il[3].OpCode, Is.EqualTo(CilOpCodes.Ldstr));
            Assert.That(il[4].OpCode, Is.EqualTo(CilOpCodes.Call),
                "the diagnostic pair follows the base-ctor call");
            Assert.That(il[^1].OpCode, Is.EqualTo(CilOpCodes.Ret));
        });
    }

    [Test]
    public void UnhoistedConstructorCallDiagnosticRunsAfterBaseCall()
    {
        // A base-ctor call whose arguments are not live at entry is not hoisted
        // to the prologue; it emits through the ordinary call path. The same
        // constraint applies: diagnostics recorded while materializing its
        // operands must follow the `call`, or the decompiler emits an
        // uncallable `base._002Ector(...)` reference.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var baseType = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Base", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var derived = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Derived", baseType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var baseCtor = baseType.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public, app.SystemTypes.SystemStringType);
        var caller = derived.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public);
        var thisLocal = new LocalVariable("this", new Register(null, "this"), derived) { IsThis = true };
        caller.Locals = [thisLocal];
        caller.ParameterLocals = [thisLocal];
        caller.AnalysisWarnings = [];
        // A metadata-pointer operand cannot fill a string parameter slot, and
        // its non-live shape keeps the call unhoisted in the instruction stream.
        var klass = new RuntimeClassTypeAnalysisContext(derived,
            app.SystemTypes.SystemObjectType.DeclaringAssembly);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, baseCtor, thisLocal, klass),
            new(1, OpCode.Return)]);

        var module = new ModuleDefinition("CtorInPlace.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemStringType);
        var baseTypeDef = new TypeDefinition("Tests", "Base",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(baseTypeDef);
        baseType.PutExtraData("AsmResolverType", baseTypeDef);
        var baseCtorDef = new MethodDefinition(".ctor",
            MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.String]));
        baseTypeDef.Methods.Add(baseCtorDef);
        baseCtor.PutExtraData("AsmResolverMethod", baseCtorDef);
        var derivedTypeDef = new TypeDefinition("Tests", "Derived",
            TypeAttributes.Public | TypeAttributes.Class, baseTypeDef.ToTypeReference());
        module.TopLevelTypes.Add(derivedTypeDef);
        derived.PutExtraData("AsmResolverType", derivedTypeDef);
        var method = new MethodDefinition(".ctor",
            MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        derivedTypeDef.Methods.Add(method);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var baseCallIndex = il.ToList().FindIndex(i =>
            i.OpCode == CilOpCodes.Call && ReferenceEquals(i.Operand, baseCtorDef));
        Assert.Multiple(() =>
        {
            Assert.That(baseCallIndex, Is.GreaterThanOrEqualTo(0),
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il[baseCallIndex + 1].OpCode, Is.EqualTo(CilOpCodes.Ldstr),
                "the metadata pointer could not fill the string slot; its diagnostic follows the call");
            Assert.That(il[baseCallIndex + 2].OpCode, Is.EqualTo(CilOpCodes.Call));
            Assert.That(il[^1].OpCode, Is.EqualTo(CilOpCodes.Ret));
        });
    }
}
