using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.OutputFormats;
using LibCpp2IL.BinaryStructures;
using NUnit.Framework;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

public class SetterOnlyAutoPropertyTests
{
    // il2cpp strips accessor MethodDefs the binary never calls: a
    // compiler-generated auto-property can arrive with only its setter
    // surviving, which decompiles to `{ set; }` - not valid C# (CS8051). The
    // `<X>k__BackingField` proves the original was `{ get; set; }`, so the
    // getter is restored against that field at property emission time.
    [Test]
    public void SetterOnlyAutoPropertyGetsGetterBack()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];

        var holderType = assembly.InjectType("Tests", "AutoPropertyHolder",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        holderType.InjectFieldContext("<InstanceValue>k__BackingField",
            app.SystemTypes.SystemInt32Type, R.FieldAttributes.Private);
        var setter = holderType.InjectMethodContext("set_InstanceValue",
            app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig | R.MethodAttributes.SpecialName,
            app.SystemTypes.SystemInt32Type);
        holderType.InjectPropertyContext("InstanceValue",
            app.SystemTypes.SystemInt32Type, null, setter, R.PropertyAttributes.None);

        var assemblies = new AsmResolverDllOutputFormatEmpty().BuildAssemblies(app);
        var module = assemblies.First(a => a.Name == assembly.Name.ToString()).ManifestModule!;

        var emittedType = module.GetAllTypes().First(t => t.FullName == "Tests.AutoPropertyHolder");
        var emittedProperty = emittedType.Properties.Single(p => p.Name == "InstanceValue");
        var backingField = emittedType.Fields.Single(f => f.Name == "<InstanceValue>k__BackingField");
        Assert.Multiple(() =>
        {
            Assert.That(emittedProperty.SetMethod, Is.SameAs(
                emittedType.Methods.Single(m => m.Name == "set_InstanceValue")),
                "the surviving setter must stay the property's set accessor");
            Assert.That(emittedProperty.GetMethod?.IsPublic, Is.True,
                "the restored getter must mirror the setter's visibility");
            Assert.That(emittedProperty.GetMethod!.Attributes
                .HasFlag(AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.HideBySig
                    | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.SpecialName),
                Is.True, "the restored getter must carry accessor flags");
        });

        var il = emittedProperty.GetMethod!.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Select(i => i.OpCode.Code), Is.EqualTo(
                new[] { CilCode.Ldarg_0, CilCode.Ldfld, CilCode.Ret }),
                "the restored getter body must read the backing field");
            Assert.That(il[1].Operand, Is.SameAs(backingField),
                "the restored getter must read the property's backing field");
        });
    }

    [Test]
    public void StaticSetterOnlyAutoPropertyGetsGetterBack()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];

        var holderType = assembly.InjectType("Tests", "StaticAutoPropertyHolder",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        holderType.InjectFieldContext("<StaticValue>k__BackingField",
            app.SystemTypes.SystemInt32Type,
            R.FieldAttributes.Private | R.FieldAttributes.Static);
        var setter = holderType.InjectMethodContext("set_StaticValue",
            app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static
                | R.MethodAttributes.HideBySig | R.MethodAttributes.SpecialName,
            app.SystemTypes.SystemInt32Type);
        holderType.InjectPropertyContext("StaticValue",
            app.SystemTypes.SystemInt32Type, null, setter, R.PropertyAttributes.None);

        var assemblies = new AsmResolverDllOutputFormatEmpty().BuildAssemblies(app);
        var module = assemblies.First(a => a.Name == assembly.Name.ToString()).ManifestModule!;

        var emittedType = module.GetAllTypes().First(t => t.FullName == "Tests.StaticAutoPropertyHolder");
        var emittedProperty = emittedType.Properties.Single(p => p.Name == "StaticValue");
        var backingField = emittedType.Fields.Single(f => f.Name == "<StaticValue>k__BackingField");

        var il = emittedProperty.GetMethod!.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(emittedProperty.GetMethod!.IsStatic, Is.True);
            Assert.That(il.Select(i => i.OpCode.Code), Is.EqualTo(
                new[] { CilCode.Ldsfld, CilCode.Ret }),
                "the restored static getter body must read the static backing field");
            Assert.That(il[0].Operand, Is.SameAs(backingField));
        });
    }

    // Without a <X>k__BackingField there is no proof the original was an
    // auto-property, so a getter must not be invented: the property stays
    // setter-only.
    [Test]
    public void SetterOnlyPropertyWithoutBackingFieldStaysAsIs()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];

        var holderType = assembly.InjectType("Tests", "WriteOnlyHolder",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var setter = holderType.InjectMethodContext("set_WrittenValue",
            app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig | R.MethodAttributes.SpecialName,
            app.SystemTypes.SystemInt32Type);
        holderType.InjectPropertyContext("WrittenValue",
            app.SystemTypes.SystemInt32Type, null, setter, R.PropertyAttributes.None);

        var assemblies = new AsmResolverDllOutputFormatEmpty().BuildAssemblies(app);
        var module = assemblies.First(a => a.Name == assembly.Name.ToString()).ManifestModule!;

        var emittedType = module.GetAllTypes().First(t => t.FullName == "Tests.WriteOnlyHolder");
        var emittedProperty = emittedType.Properties.Single(p => p.Name == "WrittenValue");
        Assert.Multiple(() =>
        {
            Assert.That(emittedProperty.GetMethod, Is.Null,
                "a setter-only property with no backing field must keep no getter");
            Assert.That(emittedType.Methods.Any(m => m.Name == "get_WrittenValue"), Is.False,
                "no getter method may be synthesized without a backing field");
        });
    }

    // An indexer's setter carries the index parameters before `value`, so it
    // can never be an auto-property even if a like-named backing field exists.
    [Test]
    public void SetterOnlyIndexerStaysAsIs()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];

        var holderType = assembly.InjectType("Tests", "IndexerHolder",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        holderType.InjectFieldContext("<Item>k__BackingField",
            app.SystemTypes.SystemInt32Type, R.FieldAttributes.Private);
        var setter = holderType.InjectMethodContext("set_Item",
            app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig | R.MethodAttributes.SpecialName,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemInt32Type);
        holderType.InjectPropertyContext("Item",
            app.SystemTypes.SystemInt32Type, null, setter, R.PropertyAttributes.None);

        var assemblies = new AsmResolverDllOutputFormatEmpty().BuildAssemblies(app);
        var module = assemblies.First(a => a.Name == assembly.Name.ToString()).ManifestModule!;

        var emittedType = module.GetAllTypes().First(t => t.FullName == "Tests.IndexerHolder");
        var emittedProperty = emittedType.Properties.Single(p => p.Name == "Item");
        Assert.Multiple(() =>
        {
            Assert.That(emittedProperty.GetMethod, Is.Null,
                "an indexer is never an auto-property and must keep no getter");
            Assert.That(emittedType.Methods.Any(m => m.Name == "get_Item"), Is.False);
        });
    }

    // An explicit-interface property is named `I.Prop`; C# forbids explicit
    // implementations as auto-properties, so a stripped getter on one can
    // never be evidenced by a backing field (the interface holds none) and
    // the surviving accessor pair already decompiles legally. Restoration
    // must leave it alone.
    [Test]
    public void ExplicitInterfacePropertyStaysSetterOnly()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];

        var iface = assembly.InjectType("Tests", "IMirror", null,
            R.TypeAttributes.Public | R.TypeAttributes.Interface | R.TypeAttributes.Abstract);
        var ifaceGetter = iface.InjectMethodContext("get_Value",
            app.SystemTypes.SystemInt32Type,
            R.MethodAttributes.Public | R.MethodAttributes.Abstract | R.MethodAttributes.Virtual
                | R.MethodAttributes.HideBySig | R.MethodAttributes.SpecialName);
        var ifaceSetter = iface.InjectMethodContext("set_Value",
            app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Abstract | R.MethodAttributes.Virtual
                | R.MethodAttributes.HideBySig | R.MethodAttributes.SpecialName,
            app.SystemTypes.SystemInt32Type);
        iface.InjectPropertyContext("Value", app.SystemTypes.SystemInt32Type,
            ifaceGetter, ifaceSetter, R.PropertyAttributes.None);

        var impl = assembly.InjectType("Tests", "MirrorImpl",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        impl.InterfaceContexts.Add(iface);
        impl.InjectFieldContext("<Tests.IMirror.Value>k__BackingField",
            app.SystemTypes.SystemInt32Type, R.FieldAttributes.Private);
        var setter = impl.InjectMethodContext("Tests.IMirror.set_Value",
            app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Private | R.MethodAttributes.Final | R.MethodAttributes.Virtual
                | R.MethodAttributes.NewSlot | R.MethodAttributes.HideBySig | R.MethodAttributes.SpecialName,
            app.SystemTypes.SystemInt32Type);
        setter.Overrides.Add(ifaceSetter);
        impl.InjectPropertyContext("Tests.IMirror.Value",
            app.SystemTypes.SystemInt32Type, null, setter, R.PropertyAttributes.None);

        var assemblies = new AsmResolverDllOutputFormatEmpty().BuildAssemblies(app);
        var module = assemblies.First(a => a.Name == assembly.Name.ToString()).ManifestModule!;

        var emittedImpl = module.GetAllTypes().First(t => t.FullName == "Tests.MirrorImpl");
        var emittedProperty = emittedImpl.Properties.Single(p => p.Name == "Tests.IMirror.Value");
        Assert.Multiple(() =>
        {
            Assert.That(emittedProperty.GetMethod, Is.Null,
                "an explicit-interface property can never be an auto-property, so no getter may be invented");
            Assert.That(emittedImpl.Methods.Any(m =>
                    m.Name?.ToString() == "Tests.IMirror.get_Value"), Is.False);
            Assert.That(emittedImpl.MethodImplementations.Any(mi =>
                    mi.Body == emittedProperty.SetMethod
                    && mi.Declaration?.Name?.ToString() == "set_Value"),
                Is.True,
                "the surviving setter must keep its interface implementation row");
        });
    }

    // On a generic declaring type the compiler emits `ldfld` against the
    // type's own generic instance (a TypeSpec), never the bare typedef; any
    // other operand is invalid IL.
    [Test]
    public void RestoredGetterOnGenericTypeReferencesSelfInstance()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];

        var holder = assembly.InjectType("Tests", "GenericHolder`1",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var paramT = new GenericParameterTypeAnalysisContext("T", 0,
            Il2CppTypeEnum.IL2CPP_TYPE_VAR, 0, holder);
        holder.GenericParameters.Add(paramT);
        var backingField = holder.InjectFieldContext("<Value>k__BackingField",
            paramT, R.FieldAttributes.Private);
        var setter = holder.InjectMethodContext("set_Value",
            app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig | R.MethodAttributes.SpecialName,
            paramT);
        holder.InjectPropertyContext("Value", paramT, null, setter,
            R.PropertyAttributes.None);

        var assemblies = new AsmResolverDllOutputFormatEmpty().BuildAssemblies(app);
        var module = assemblies.First(a => a.Name == assembly.Name.ToString()).ManifestModule!;

        var emittedType = module.GetAllTypes().First(t => t.FullName == "Tests.GenericHolder`1");
        var getter = emittedType.Methods.FirstOrDefault(m => m.Name == "get_Value");
        Assert.That(getter, Is.Not.Null);

        var ldfld = getter!.CilMethodBody!.Instructions.Single(i => i.OpCode == CilOpCodes.Ldfld);
        Assert.Multiple(() =>
        {
            Assert.That(ldfld.Operand, Is.InstanceOf<MemberReference>());
            var declaringType = ((MemberReference)ldfld.Operand!).DeclaringType;
            Assert.That(declaringType, Is.InstanceOf<TypeSpecification>()
                .With.Property("Signature").InstanceOf<GenericInstanceTypeSignature>());
        });
    }
}
