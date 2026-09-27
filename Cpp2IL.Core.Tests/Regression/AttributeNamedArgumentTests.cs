using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Model.CustomAttributes;
using Cpp2IL.Core.OutputFormats;
using NUnit.Framework;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

public class AttributeNamedArgumentTests
{
    // il2cpp strips accessor MethodDefs the binary never calls: a property used
    // as a custom-attribute named argument keeps its setter (the runtime
    // assigns through it) but loses the getter. The emitted blob still carries
    // it as a property named argument, so the recovered attribute typedef must
    // expose a public readable and writable member by that name.
    [Test]
    public void NamedArgumentSetOnlyPropertyGetsGetterBack()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];

        var attributeType = assembly.InjectType("Tests", "SetOnlyNamedAttribute",
            app.SystemTypes.SystemAttributeType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var field = attributeType.InjectFieldContext("NamedField",
            app.SystemTypes.SystemStringType, R.FieldAttributes.Public);
        attributeType.InjectFieldContext("<NamedProperty>k__BackingField",
            app.SystemTypes.SystemInt32Type, R.FieldAttributes.Private);
        var setter = attributeType.InjectMethodContext("set_NamedProperty",
            app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig | R.MethodAttributes.SpecialName,
            app.SystemTypes.SystemInt32Type);
        var property = attributeType.InjectPropertyContext("NamedProperty",
            app.SystemTypes.SystemInt32Type, null, setter, R.PropertyAttributes.None);
        var constructor = attributeType.InjectMethodContext(".ctor",
            app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.SpecialName
                | R.MethodAttributes.RTSpecialName | R.MethodAttributes.HideBySig);

        var holder = assembly.InjectType("Tests", "NamedArgumentHolder",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        holder.AnalyzeCustomAttributeData();
        holder.CustomAttributes ??= [];
        var attribute = new AnalyzedCustomAttribute(constructor);
        attribute.Fields.Add(new(field,
            new CustomAttributePrimitiveParameter("named", attribute, CustomAttributeParameterKind.Field, 0)));
        attribute.Properties.Add(new(property,
            new CustomAttributePrimitiveParameter(42, attribute, CustomAttributeParameterKind.Property, 0)));
        holder.CustomAttributes.Add(attribute);

        var assemblies = new AsmResolverDllOutputFormatEmpty().BuildAssemblies(app);
        var module = assemblies.First(a => a.Name == assembly.Name.ToString()).ManifestModule!;

        var emittedAttribute = module.GetAllTypes()
            .First(t => t.FullName == "Tests.NamedArgumentHolder")
            .CustomAttributes.Single();
        var namedArguments = emittedAttribute.Signature!.NamedArguments;
        Assert.Multiple(() =>
        {
            Assert.That(namedArguments.Any(n => n.MemberName?.ToString() == "NamedField"
                && n.MemberType == CustomAttributeArgumentMemberType.Field), Is.True,
                "blob must carry NamedField as a field named argument");
            Assert.That(namedArguments.Any(n => n.MemberName?.ToString() == "NamedProperty"
                && n.MemberType == CustomAttributeArgumentMemberType.Property), Is.True,
                "blob must carry NamedProperty as a property named argument");
        });

        var emittedType = module.GetAllTypes().First(t => t.FullName == "Tests.SetOnlyNamedAttribute");
        var emittedField = emittedType.Fields.Single(f => f.Name == "NamedField");
        Assert.That(emittedField.Attributes
            & (FieldAttributes.InitOnly | FieldAttributes.Literal), Is.EqualTo((FieldAttributes)0),
            "named field argument must be writable");

        var emittedProperty = emittedType.Properties.Single(p => p.Name == "NamedProperty");
        Assert.Multiple(() =>
        {
            Assert.That(emittedProperty.SetMethod?.IsPublic, Is.True,
                "named property argument must keep its public setter");
            Assert.That(emittedProperty.GetMethod?.IsPublic, Is.True,
                "named property argument must get a public getter back");
            Assert.That(emittedProperty.GetMethod!.CilMethodBody, Is.Not.Null);
        });
    }

    // Without a <Name>k__BackingField there is no proof the original was an
    // auto-property, so the missing accessor must not be invented: the property
    // stays setter-only and a warning is logged instead.
    [Test]
    public void SetOnlyPropertyWithoutBackingFieldStaysAsIs()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];

        var attributeType = assembly.InjectType("Tests", "BareSetOnlyAttribute",
            app.SystemTypes.SystemAttributeType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var setter = attributeType.InjectMethodContext("set_NamedProperty",
            app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig | R.MethodAttributes.SpecialName,
            app.SystemTypes.SystemInt32Type);
        var property = attributeType.InjectPropertyContext("NamedProperty",
            app.SystemTypes.SystemInt32Type, null, setter, R.PropertyAttributes.None);
        var constructor = attributeType.InjectMethodContext(".ctor",
            app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.SpecialName
                | R.MethodAttributes.RTSpecialName | R.MethodAttributes.HideBySig);

        var holder = assembly.InjectType("Tests", "BareSetOnlyHolder",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        holder.AnalyzeCustomAttributeData();
        holder.CustomAttributes ??= [];
        var attribute = new AnalyzedCustomAttribute(constructor);
        attribute.Properties.Add(new(property,
            new CustomAttributePrimitiveParameter(42, attribute, CustomAttributeParameterKind.Property, 0)));
        holder.CustomAttributes.Add(attribute);

        var assemblies = new AsmResolverDllOutputFormatEmpty().BuildAssemblies(app);
        var module = assemblies.First(a => a.Name == assembly.Name.ToString()).ManifestModule!;

        var emittedType = module.GetAllTypes().First(t => t.FullName == "Tests.BareSetOnlyAttribute");
        var emittedProperty = emittedType.Properties.Single(p => p.Name == "NamedProperty");
        Assert.Multiple(() =>
        {
            Assert.That(emittedProperty.GetMethod, Is.Null,
                "a setter-only named-argument property with no backing field must keep no getter");
            Assert.That(emittedType.Methods.Any(m => m.Name == "get_NamedProperty"), Is.False,
                "no getter method may be synthesized without a backing field");
        });
    }
}
