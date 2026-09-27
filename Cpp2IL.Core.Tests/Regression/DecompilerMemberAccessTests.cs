using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.OutputFormats;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: decompiler-generated members (#79). The lifted IL names
// storage no C# identifier can spell — enum value__, <X>k__BackingField, and a
// duplicated base-ctor call that decompiles as base._002Ector() — which leaves
// CS0117/CS1061 in the recovered source even though the access itself is honest.
public class DecompilerMemberAccessTests
{
    private static ModuleDefinition NewModule(out AssemblyDefinition assembly)
    {
        assembly = new AssemblyDefinition("Tests", new System.Version(1, 0, 0, 0));
        var module = new ModuleDefinition("Tests.dll");
        assembly.Modules.Add(module);
        return module;
    }

    private static MethodDefinition AddBodyMethod(TypeDefinition type, string name,
        MethodSignature signature)
    {
        var method = new MethodDefinition(name,
            MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.HideBySig, signature);
        method.CilMethodBody = new CilMethodBody { InitializeLocals = true };
        type.Methods.Add(method);
        return method;
    }

    [Test]
    public void EnumUnderlyingFieldAccessEmitsObjectOps()
    {
        var module = NewModule(out _);
        var corlib = module.CorLibTypeFactory;
        var enumType = new TypeDefinition("Ns", "Kind",
            TypeAttributes.Public | TypeAttributes.Sealed,
            corlib.CorLibScope.CreateTypeReference("System", "Enum"));
        var valueField = new FieldDefinition("value__",
            FieldAttributes.Public | FieldAttributes.SpecialName | FieldAttributes.RuntimeSpecialName,
            new FieldSignature(corlib.Int32));
        enumType.Fields.Add(valueField);
        module.TopLevelTypes.Add(enumType);

        var methods = new TypeDefinition("Ns", "Ops",
            TypeAttributes.Public | TypeAttributes.Class,
            corlib.CorLibScope.CreateTypeReference("System", "Object"));
        module.TopLevelTypes.Add(methods);

        var load = AddBodyMethod(methods, "Load",
            MethodSignature.CreateStatic(corlib.Int32, new[] { enumType.ToTypeSignature(module.RuntimeContext) }));
        load.CilMethodBody!.Instructions.Add(new CilInstruction(CilOpCodes.Ldarga, load.Parameters[0]));
        load.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ldfld, valueField));
        load.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ret));

        var store = AddBodyMethod(methods, "Store",
            MethodSignature.CreateStatic(corlib.Void,
                new[] { enumType.ToTypeSignature(module.RuntimeContext), corlib.Int32 }));
        store.CilMethodBody!.Instructions.Add(new CilInstruction(CilOpCodes.Ldarga, store.Parameters[0]));
        store.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ldarg_1));
        store.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Stfld, valueField));
        store.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ret));

        // A struct field that merely shares the name must keep its honest access:
        // only an enum's underlying slot can be re-expressed as the enum itself.
        var structType = new TypeDefinition("Ns", "Plain",
            TypeAttributes.Public | TypeAttributes.Sealed,
            corlib.CorLibScope.CreateTypeReference("System", "ValueType"));
        var plainField = new FieldDefinition("value__", FieldAttributes.Public,
            new FieldSignature(corlib.Int32));
        structType.Fields.Add(plainField);
        module.TopLevelTypes.Add(structType);
        var plain = AddBodyMethod(methods, "LoadPlain",
            MethodSignature.CreateStatic(corlib.Int32, new[] { structType.ToTypeSignature(module.RuntimeContext) }));
        plain.CilMethodBody!.Instructions.Add(new CilInstruction(CilOpCodes.Ldarga, plain.Parameters[0]));
        plain.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ldfld, plainField));
        plain.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ret));

        DecompilerMemberAccessRewrites.Apply(load);
        DecompilerMemberAccessRewrites.Apply(store);
        DecompilerMemberAccessRewrites.Apply(plain);

        Assert.Multiple(() =>
        {
            Assert.That(load.CilMethodBody.Instructions[1].OpCode, Is.EqualTo(CilOpCodes.Ldobj));
            Assert.That(load.CilMethodBody.Instructions[1].Operand, Is.SameAs(enumType));
            Assert.That(store.CilMethodBody.Instructions[2].OpCode, Is.EqualTo(CilOpCodes.Stobj));
            Assert.That(store.CilMethodBody.Instructions[2].Operand, Is.SameAs(enumType));
            Assert.That(plain.CilMethodBody.Instructions[1].OpCode, Is.EqualTo(CilOpCodes.Ldfld));
        });
    }

    private static (TypeDefinition owner, FieldDefinition backingField, MethodDefinition getter,
        MethodDefinition setter) NewAutoProperty(ModuleDefinition module, bool privateSetter)
    {
        var corlib = module.CorLibTypeFactory;
        var owner = new TypeDefinition("Ns", "Holder",
            TypeAttributes.Public | TypeAttributes.Class,
            corlib.CorLibScope.CreateTypeReference("System", "Object"));
        var backingField = new FieldDefinition("<Size>k__BackingField", FieldAttributes.Private,
            new FieldSignature(corlib.Int32));
        owner.Fields.Add(backingField);
        var getter = new MethodDefinition("get_Size",
            MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.HideBySig,
            MethodSignature.CreateInstance(corlib.Int32));
        var setter = new MethodDefinition("set_Size",
            (privateSetter ? MethodAttributes.Private : MethodAttributes.Public)
                | MethodAttributes.SpecialName | MethodAttributes.HideBySig,
            MethodSignature.CreateInstance(corlib.Void, new[] { corlib.Int32 }));
        owner.Methods.Add(getter);
        owner.Methods.Add(setter);
        owner.Properties.Add(new PropertyDefinition("Size", PropertyAttributes.None,
            PropertySignature.CreateInstance(corlib.Int32)) { GetMethod = getter, SetMethod = setter });
        module.TopLevelTypes.Add(owner);
        return (owner, backingField, getter, setter);
    }

    [Test]
    public void BackingFieldAccessEmitsAccessorCall()
    {
        var module = NewModule(out _);
        var corlib = module.CorLibTypeFactory;
        var (owner, backingField, getter, setter) = NewAutoProperty(module, privateSetter: false);

        var callerType = new TypeDefinition("Ns", "Caller",
            TypeAttributes.Public | TypeAttributes.Class,
            corlib.CorLibScope.CreateTypeReference("System", "Object"));
        module.TopLevelTypes.Add(callerType);
        var store = AddBodyMethod(callerType, "SetSize",
            MethodSignature.CreateStatic(corlib.Void,
                new[] { owner.ToTypeSignature(module.RuntimeContext), corlib.Int32 }));
        store.CilMethodBody!.Instructions.Add(new CilInstruction(CilOpCodes.Ldarg_0));
        store.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ldarg_1));
        store.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Stfld, backingField));
        store.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ret));
        var load = AddBodyMethod(callerType, "GetSize",
            MethodSignature.CreateStatic(corlib.Int32, new[] { owner.ToTypeSignature(module.RuntimeContext) }));
        load.CilMethodBody!.Instructions.Add(new CilInstruction(CilOpCodes.Ldarg_0));
        load.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ldfld, backingField));
        load.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ret));

        DecompilerMemberAccessRewrites.Apply(store);
        DecompilerMemberAccessRewrites.Apply(load);

        Assert.Multiple(() =>
        {
            Assert.That(store.CilMethodBody.Instructions[2].OpCode, Is.EqualTo(CilOpCodes.Callvirt));
            Assert.That(store.CilMethodBody.Instructions[2].Operand, Is.SameAs(setter));
            Assert.That(load.CilMethodBody.Instructions[1].OpCode, Is.EqualTo(CilOpCodes.Callvirt));
            Assert.That(load.CilMethodBody.Instructions[1].Operand, Is.SameAs(getter));
        });
    }

    [Test]
    public void InaccessibleSetterKeepsFieldAccess()
    {
        var module = NewModule(out _);
        var corlib = module.CorLibTypeFactory;
        var (owner, backingField, _, _) = NewAutoProperty(module, privateSetter: true);

        // A store from another type may not call a private setter: the raw field
        // store stays, honestly reporting the recoverable gap.
        var callerType = new TypeDefinition("Ns", "Caller",
            TypeAttributes.Public | TypeAttributes.Class,
            corlib.CorLibScope.CreateTypeReference("System", "Object"));
        module.TopLevelTypes.Add(callerType);
        var store = AddBodyMethod(callerType, "SetSize",
            MethodSignature.CreateStatic(corlib.Void,
                new[] { owner.ToTypeSignature(module.RuntimeContext), corlib.Int32 }));
        store.CilMethodBody!.Instructions.Add(new CilInstruction(CilOpCodes.Ldarg_0));
        store.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ldarg_1));
        store.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Stfld, backingField));
        store.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ret));

        // But the same private setter stays legal inside the declaring type.
        var ownStore = new MethodDefinition("Grow",
            MethodAttributes.Public | MethodAttributes.HideBySig,
            MethodSignature.CreateInstance(corlib.Void, new[] { corlib.Int32 }));
        ownStore.CilMethodBody = new CilMethodBody { InitializeLocals = true };
        ownStore.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ldarg_0));
        ownStore.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ldarg_1));
        ownStore.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Stfld, backingField));
        ownStore.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ret));
        owner.Methods.Add(ownStore);

        DecompilerMemberAccessRewrites.Apply(store);
        DecompilerMemberAccessRewrites.Apply(ownStore);

        Assert.Multiple(() =>
        {
            Assert.That(store.CilMethodBody.Instructions[2].OpCode, Is.EqualTo(CilOpCodes.Stfld));
            Assert.That(ownStore.CilMethodBody.Instructions[2].OpCode, Is.EqualTo(CilOpCodes.Callvirt));
        });
    }

    [Test]
    public void NestedTypeInDerivedClassCallsProtectedAccessor()
    {
        var module = NewModule(out _);
        var corlib = module.CorLibTypeFactory;
        var (owner, backingField, _, setter) = NewAutoProperty(module, privateSetter: false);
        setter.IsPublic = false;
        setter.IsFamily = true;

        var derived = new TypeDefinition("Ns", "DerivedHolder",
            TypeAttributes.Public | TypeAttributes.Class, owner);
        module.TopLevelTypes.Add(derived);
        // Async state machines surface as nested types; a nested type of a
        // derived class may use a protected accessor through a receiver typed
        // at the derived class.
        var machine = new TypeDefinition("", "Machine", TypeAttributes.NestedPublic, null);
        derived.NestedTypes.Add(machine);
        var run = AddBodyMethod(machine, "Run",
            MethodSignature.CreateStatic(corlib.Void,
                new[] { derived.ToTypeSignature(module.RuntimeContext), corlib.Int32 }));
        run.CilMethodBody!.Instructions.Add(new CilInstruction(CilOpCodes.Ldarg_0));
        run.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ldarg_1));
        // The field reference names the declaring base type even though the
        // receiver (the state machine's <>4__this field) is typed at DerivedHolder.
        run.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Stfld, backingField));
        run.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ret));

        DecompilerMemberAccessRewrites.Apply(run);

        Assert.Multiple(() =>
        {
            Assert.That(run.CilMethodBody.Instructions[2].OpCode, Is.EqualTo(CilOpCodes.Callvirt));
            Assert.That(run.CilMethodBody.Instructions[2].Operand is IMethodDescriptor m
                && m.Name?.Value == "set_Size");
        });
    }

    [Test]
    public void AccessorBodyKeepsItsFieldAccess()
    {
        var module = NewModule(out _);
        var corlib = module.CorLibTypeFactory;
        var (_, backingField, _, setter) = NewAutoProperty(module, privateSetter: false);

        // Rewriting the setter's own store into a call would make it recurse.
        setter.CilMethodBody = new CilMethodBody { InitializeLocals = true };
        setter.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ldarg_0));
        setter.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ldarg_1));
        setter.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Stfld, backingField));
        setter.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ret));

        DecompilerMemberAccessRewrites.Apply(setter);

        Assert.That(setter.CilMethodBody.Instructions[2].OpCode, Is.EqualTo(CilOpCodes.Stfld));
    }

    private static InjectedTypeAnalysisContext InjectType(ApplicationAnalysisContext app,
        string name, TypeAnalysisContext baseType) =>
        new(app.AssembliesByName["UnityEngine.CoreModule"], "Tests", name, baseType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);

    [Test]
    public void StubCtorDoesNotDuplicateBaseCall()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var widget = InjectType(app, "Widget", app.SystemTypes.SystemObjectType);
        var ctorContext = widget.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig
                | R.MethodAttributes.SpecialName | R.MethodAttributes.RTSpecialName);

        var module = NewModule(out _);
        var corlib = module.CorLibTypeFactory;
        var type = new TypeDefinition("Tests", "Widget",
            TypeAttributes.Public | TypeAttributes.Class,
            corlib.CorLibScope.CreateTypeReference("System", "Object"));
        module.TopLevelTypes.Add(type);
        var ctor = new MethodDefinition(".ctor",
            MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.RuntimeSpecialName
                | MethodAttributes.HideBySig,
            MethodSignature.CreateInstance(corlib.Void));
        type.Methods.Add(ctor);
        ctor.CilMethodBody = new CilMethodBody();
        // The stubber already seeds `this` when it can bind a base .ctor; the
        // initializer must not insert a second call ahead of it.
        var baseCtor = corlib.CorLibScope.CreateTypeReference("System", "Object")
            .CreateMemberReference(".ctor", MethodSignature.CreateInstance(corlib.Void));
        ctor.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        ctor.CilMethodBody.Instructions.Add(CilOpCodes.Call, baseCtor);
        ctor.CilMethodBody.Instructions.Add(CilOpCodes.Ret);

        AsmResolverDllOutputFormat.EnsureCtorInitialized(ctor, ctorContext);

        Assert.That(
            ctor.CilMethodBody.Instructions.Count(i =>
                i.OpCode == CilOpCodes.Call && i.Operand is IMethodDescriptor { Name.Value: ".ctor" }),
            Is.EqualTo(1),
            () => string.Join("\n", ctor.CilMethodBody.Instructions.Select(i => i.ToString())));
    }

    [Test]
    public void StubCtorWithoutBaseCallStillInitializes()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;

        // The guard is scoped to .ctor calls: an unrelated call must not look
        // like `this` is already initialized.
        var baseType = InjectType(app, "Base", app.SystemTypes.SystemObjectType);
        baseType.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig
                | R.MethodAttributes.SpecialName | R.MethodAttributes.RTSpecialName);
        var derived = InjectType(app, "Derived", baseType);
        var ctorContext = derived.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig
                | R.MethodAttributes.SpecialName | R.MethodAttributes.RTSpecialName);

        var module = NewModule(out _);
        var corlib = module.CorLibTypeFactory;
        var baseDef = new TypeDefinition("Tests", "Base",
            TypeAttributes.Public | TypeAttributes.Class,
            corlib.CorLibScope.CreateTypeReference("System", "Object"));
        module.TopLevelTypes.Add(baseDef);
        var type = new TypeDefinition("Tests", "Derived",
            TypeAttributes.Public | TypeAttributes.Class, baseDef);
        module.TopLevelTypes.Add(type);
        var ctor = new MethodDefinition(".ctor",
            MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.RuntimeSpecialName
                | MethodAttributes.HideBySig,
            MethodSignature.CreateInstance(corlib.Void));
        type.Methods.Add(ctor);
        ctor.CilMethodBody = new CilMethodBody();
        var nop = corlib.CorLibScope.CreateTypeReference("System", "Console")
            .CreateMemberReference("WriteLine", MethodSignature.CreateStatic(corlib.Void, new[] { corlib.String }));
        ctor.CilMethodBody.Instructions.Add(CilOpCodes.Ldnull);
        ctor.CilMethodBody.Instructions.Add(CilOpCodes.Call, nop);
        ctor.CilMethodBody.Instructions.Add(CilOpCodes.Ret);

        AsmResolverDllOutputFormat.EnsureCtorInitialized(ctor, ctorContext);

        Assert.Multiple(() =>
        {
            Assert.That(ctor.CilMethodBody.Instructions[0].OpCode, Is.EqualTo(CilOpCodes.Ldarg_0));
            Assert.That(ctor.CilMethodBody.Instructions[1].OpCode, Is.EqualTo(CilOpCodes.Call));
            Assert.That(ctor.CilMethodBody.Instructions[1].Operand is IMethodDescriptor { Name.Value: ".ctor" });
        });
    }
}
