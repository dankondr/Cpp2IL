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

// Recovery cluster: value-type slot defaults (castle-recovery#135).
// A field load whose declared member access does not cover the caller used to
// substitute default(field type). The binary proves the access, and the emitted
// member is widened to match (MemberAccessibility.EnsureAccessible), so the
// real load is emitted - except on frozen runtime assemblies, whose stubs
// mirror the real surface and must keep declared access.
public class CrossAssemblyFieldAccessTests
{
    private static (MethodAnalysisContext caller, MethodDefinition method) InjectedCaller(
        ApplicationAnalysisContext app, ModuleDefinition module, string ns,
        System.Collections.Generic.List<Instruction> instructions,
        System.Collections.Generic.List<LocalVariable> locals,
        TypeAnalysisContext returnType, TypeSignature returnSignature)
    {
        var consumer = app.InjectAssembly("Recovered.Consumer");
        var callerType = new InjectedTypeAnalysisContext(consumer, ns, "Caller",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = callerType.InjectMethodContext("Run", returnType,
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        caller.Locals = locals;
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var type = new TypeDefinition(ns, "Caller", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(returnSignature));
        type.Methods.Add(method);
        return (caller, method);
    }

    [Test]
    public void PrivateStaticFieldInOtherAssemblyEmitsRealLoad()
    {
        // The binary proves the load; the only obstacle is that the field's declared
        // access is private to another (non-runtime) assembly. Emitting the ldsfld
        // widens the copied definition, so the value-type slot gets the real value.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;

        var owner = app.InjectAssembly("Recovered.Owner").InjectType("Tests", "Owner",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var field = owner.InjectFieldContext("secret", app.SystemTypes.SystemInt32Type,
            R.FieldAttributes.Private | R.FieldAttributes.Static);

        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemInt32Type };
        var module = new ModuleDefinition("FieldAccess.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType);
        var ownerDefinition = new TypeDefinition("Tests", "Owner",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(ownerDefinition);
        var fieldDefinition = new FieldDefinition("secret",
            FieldAttributes.Private | FieldAttributes.Static,
            new FieldSignature(module.CorLibTypeFactory.Int32));
        ownerDefinition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);

        var (caller, method) = InjectedCaller(app, module, "Tests", [
            new(0, OpCode.Move, result, new FieldReference(field, result, 0)),
            new(1, OpCode.Return, result)], [result],
            app.SystemTypes.SystemInt32Type, module.CorLibTypeFactory.Int32);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldsfld
                    && i.Operand is IFieldDescriptor descriptor && descriptor.Name == "secret"), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("synthetic default")), Is.False,
                "the proven load must not be replaced by a default substitution");
            Assert.That(fieldDefinition.Attributes & FieldAttributes.FieldAccessMask,
                Is.EqualTo(FieldAttributes.Public),
                "the emitted field is widened to the access the reference needs");
        });
    }

    [Test]
    public void PrivateStaticCorlibFieldKeepsDefaultSubstitution()
    {
        // Runtime-assembly stubs mirror the real surface, so a private mscorlib
        // field cannot be widened. The slot still gets an honest diagnosed default.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;

        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "Tests", "CorlibOwner", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var field = owner.InjectFieldContext("secret", app.SystemTypes.SystemInt32Type,
            R.FieldAttributes.Private | R.FieldAttributes.Static);

        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemInt32Type };
        var module = new ModuleDefinition("FieldAccessFrozen.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType);
        var ownerDefinition = new TypeDefinition("Tests", "CorlibOwner",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(ownerDefinition);
        var fieldDefinition = new FieldDefinition("secret",
            FieldAttributes.Private | FieldAttributes.Static,
            new FieldSignature(module.CorLibTypeFactory.Int32));
        ownerDefinition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);

        var (caller, method) = InjectedCaller(app, module, "Tests", [
            new(0, OpCode.Move, result, new FieldReference(field, result, 0)),
            new(1, OpCode.Return, result)], [result],
            app.SystemTypes.SystemInt32Type, module.CorLibTypeFactory.Int32);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("synthetic default")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldsfld), Is.False,
                "the frozen surface cannot widen, so no real load is emitted");
        });
    }

    [Test]
    public void AutoPropertyBackingFieldKeepsDiagnosedDefault()
    {
        // ILSpy folds a `<P>k__BackingField` member into its auto-property, so no
        // widened access lets the decompiled reference spell it. Widening the
        // member anyway would trade the honest diagnosed default for
        // CS1061/CS0103 errors, so the site keeps the default and the note names
        // the backing field.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;

        var owner = app.InjectAssembly("Recovered.Owner").InjectType("Tests", "Owner",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var field = owner.InjectFieldContext("<Counter>k__BackingField", app.SystemTypes.SystemInt32Type,
            R.FieldAttributes.Private | R.FieldAttributes.Static);

        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemInt32Type };
        var module = new ModuleDefinition("FieldAccessBacking.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType);
        var ownerDefinition = new TypeDefinition("Tests", "Owner",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(ownerDefinition);
        var fieldDefinition = new FieldDefinition("<Counter>k__BackingField",
            FieldAttributes.Private | FieldAttributes.Static,
            new FieldSignature(module.CorLibTypeFactory.Int32));
        ownerDefinition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);

        var (caller, method) = InjectedCaller(app, module, "Tests", [
            new(0, OpCode.Move, result, new FieldReference(field, result, 0)),
            new(1, OpCode.Return, result)], [result],
            app.SystemTypes.SystemInt32Type, module.CorLibTypeFactory.Int32);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("compiler-generated backing field")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldsfld), Is.False,
                "the folded backing field is unspellable, so no real load is emitted");
            Assert.That(fieldDefinition.Attributes & FieldAttributes.FieldAccessMask,
                Is.EqualTo(FieldAttributes.Private),
                "the unspellable member is not widened");
        });
    }
}
