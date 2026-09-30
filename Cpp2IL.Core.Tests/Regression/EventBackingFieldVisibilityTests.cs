using System;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.OutputFormats;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: duplicate-definition (CS0102). A field-like event compiles
// to a private backing field plus public accessors, and il2cpp metadata keeps
// the field's private declaration. Emitting a descriptor for a referenced field
// widens it to public so recovered IL can name it - correct when a foreign body
// proved a direct access, but a backing field only ever touched inside its own
// type must keep its declared access so decompilers fold the pair back into
// `event T E;` instead of emitting field and event as duplicate definitions.
public class EventBackingFieldVisibilityTests
{
    private static ApplicationAnalysisContext LoadApp()
    {
        Cpp2IlApi.ResetInternalState();
        return TestGameLoader.LoadSimple2022Game();
    }

    private static (InjectedAssemblyAnalysisContext context, ModuleDefinition module) AddAssembly(
        ApplicationAnalysisContext app, string name)
    {
        var module = new ModuleDefinition($"{name}.dll");
        var definition = new AssemblyDefinition(name, new Version(1, 0, 0, 0));
        definition.Modules.Add(module);
        var context = app.InjectAssembly(name);
        context.PutExtraData("AsmResolverAssembly", definition);
        return (context, module);
    }

    private static (InjectedTypeAnalysisContext context, TypeDefinition emitted) AddType(
        AssemblyAnalysisContext assembly, ModuleDefinition module, string name)
    {
        var context = assembly.InjectType("Recovered", name, assembly.AppContext.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var emitted = new TypeDefinition("Recovered", name, TypeAttributes.Public | TypeAttributes.Class)
        {
            BaseType = module.CorLibTypeFactory.Object.Type
        };
        module.TopLevelTypes.Add(emitted);
        context.PutExtraData("AsmResolverType", emitted);
        return (context, emitted);
    }

    // A static field-like event `StateChanged`: declared-private backing field,
    // public accessors, and an emitted FieldDefinition widened to public as
    // MemberAccessibility.EnsureAccessible would have left it after a body
    // emitted a reference.
    private static FieldDefinition AddFieldLikeEvent(
        InjectedTypeAnalysisContext type, TypeDefinition emittedType, ModuleDefinition module)
    {
        var eventType = type.AppContext.SystemTypes.SystemObjectType;
        var adder = type.InjectMethodContext("add_StateChanged",
            type.AppContext.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, [eventType]);
        var remover = type.InjectMethodContext("remove_StateChanged",
            type.AppContext.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, [eventType]);
        var fieldContext = type.InjectFieldContext("StateChanged", eventType,
            R.FieldAttributes.Private | R.FieldAttributes.Static);
        type.InjectEventContext("StateChanged", eventType, adder, remover, null, R.EventAttributes.None);

        var emitted = new FieldDefinition("StateChanged",
            FieldAttributes.Public | FieldAttributes.Static,
            new FieldSignature(module.CorLibTypeFactory.Object));
        emittedType.Fields.Add(emitted);
        fieldContext.PutExtraData("AsmResolverField", emitted);
        return emitted;
    }

    private static void AddStaticBody(TypeDefinition emittedType, string name,
        params CilInstruction[] instructions)
    {
        var method = new MethodDefinition(name,
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(emittedType.DeclaringModule!.CorLibTypeFactory.Void, []));
        emittedType.Methods.Add(method);
        var body = new CilMethodBody();
        method.CilMethodBody = body;
        foreach (var instruction in instructions)
            body.Instructions.Add(instruction);
        body.Instructions.Add(CilOpCodes.Ret);
    }

    private static FieldAttributes AccessOf(FieldDefinition field) =>
        field.Attributes & FieldAttributes.FieldAccessMask;

    // Invoked through reflection so this fixture still compiles - and fails the
    // assertions below - on a tree where the restore pass does not exist yet.
    private static void RunBackingFieldRestore(ApplicationAnalysisContext app)
    {
        var pass = typeof(AsmResolverDllOutputFormatIlRecovery).GetMethod(
            "RestoreFieldLikeEventBackingFields",
            R.BindingFlags.Static | R.BindingFlags.NonPublic | R.BindingFlags.Public);
        Assert.That(pass, Is.Not.Null, "the backing-field access restore pass exists");
        pass!.Invoke(null, [app]);
    }

    // Every emitted reference sits inside the declaring type's private scope, so
    // the promotion was never needed: declared private access comes back.
    [Test]
    public void SameTypeOnlyReferencesRestoreDeclaredPrivate()
    {
        var app = LoadApp();
        var (asm, module) = AddAssembly(app, "Recovered.Events");
        var (type, emittedType) = AddType(asm, module, "Notifier");
        var field = AddFieldLikeEvent(type, emittedType, module);
        Assert.That(AccessOf(field), Is.EqualTo(FieldAttributes.Public), "precondition: promoted");

        // Recovered accessor shape: a MemberReference on the declaring type.
        AddStaticBody(emittedType, "add_StateChanged",
            new CilInstruction(CilOpCodes.Ldsfld,
                new MemberReference(emittedType, "StateChanged", field.Signature!)),
            new CilInstruction(CilOpCodes.Pop));
        // Recovered raise site: the FieldDefinition operand itself.
        AddStaticBody(emittedType, "Raise",
            new CilInstruction(CilOpCodes.Ldsfld, field),
            new CilInstruction(CilOpCodes.Pop));

        RunBackingFieldRestore(app);

        Assert.That(AccessOf(field), Is.EqualTo(FieldAttributes.Private));
    }

    // A type nested inside the declaring type shares its private scope, so its
    // references do not stop the restore.
    [Test]
    public void NestedTypeReferenceStillRestoresDeclaredPrivate()
    {
        var app = LoadApp();
        var (asm, module) = AddAssembly(app, "Recovered.Events");
        var (type, emittedType) = AddType(asm, module, "Notifier");
        var field = AddFieldLikeEvent(type, emittedType, module);

        var nestedEmitted = new TypeDefinition("Recovered", "Nested",
            TypeAttributes.NestedPublic | TypeAttributes.Class)
        {
            BaseType = module.CorLibTypeFactory.Object.Type
        };
        emittedType.NestedTypes.Add(nestedEmitted);
        AddStaticBody(nestedEmitted, "Touch",
            new CilInstruction(CilOpCodes.Ldsfld, field),
            new CilInstruction(CilOpCodes.Pop));

        RunBackingFieldRestore(app);

        Assert.That(AccessOf(field), Is.EqualTo(FieldAttributes.Private));
    }

    // A body on an unrelated type touched the field directly (an inlined
    // accessor in the native code): the widened access is what keeps that
    // reference legal, so it stays.
    [Test]
    public void ForeignTypeReferenceKeepsWidenedAccess()
    {
        var app = LoadApp();
        var (asm, module) = AddAssembly(app, "Recovered.Events");
        var (type, emittedType) = AddType(asm, module, "Notifier");
        var field = AddFieldLikeEvent(type, emittedType, module);
        var (_, subscriberEmitted) = AddType(asm, module, "Subscriber");

        AddStaticBody(subscriberEmitted, "Hook",
            new CilInstruction(CilOpCodes.Ldsfld,
                new MemberReference(emittedType, "StateChanged", field.Signature!)),
            new CilInstruction(CilOpCodes.Pop));

        RunBackingFieldRestore(app);

        Assert.That(AccessOf(field), Is.EqualTo(FieldAttributes.Public));
    }
}
