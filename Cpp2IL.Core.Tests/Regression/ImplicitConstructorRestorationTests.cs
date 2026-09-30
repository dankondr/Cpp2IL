using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Model.CustomAttributes;
using Cpp2IL.Core.OutputFormats;
using NUnit.Framework;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: `member-signature-mismatch` (castle-recovery#95). The
// emitted-side shape fixed here is attribute blob encoding; the stripped-.ctor
// shape is not Cpp2IL's to restore (see tests below).
public class ImplicitConstructorRestorationTests
{
    private static ApplicationAnalysisContext LoadApp()
    {
        Cpp2IlApi.ResetInternalState();
        return TestGameLoader.LoadSimple2022Game();
    }

    private static ModuleDefinition Build(ApplicationAnalysisContext app, string assemblyName) =>
        new AsmResolverDllOutputFormatEmpty().BuildAssemblies(app)
            .First(a => a.Name == assemblyName).ManifestModule!;

    // Zero-.ctor class typedefs are the IL2CPP-stripped shape: the metadata no
    // longer shows whether the source had an implicit .ctor or an explicit one
    // that was stripped, so emitting any .ctor invents a member. The typedef
    // must come back exactly as recorded — no synthesized constructor.
    [Test]
    public void ZeroCtorClassIsEmittedWithoutConstructor()
    {
        var app = LoadApp();
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];

        var baseType = assembly.InjectType("Tests", "CtorlessBase",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        assembly.InjectType("Tests", "CtorlessDerived", baseType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);

        var module = Build(app, assembly.Name);

        Assert.Multiple(() =>
        {
            Assert.That(module.GetAllTypes().First(t => t.FullName == "Tests.CtorlessBase")
                .Methods.Any(m => m.Name == ".ctor"), Is.False,
                "a zero-.ctor typedef must not gain a synthesized .ctor");
            Assert.That(module.GetAllTypes().First(t => t.FullName == "Tests.CtorlessDerived")
                .Methods.Any(m => m.Name == ".ctor"), Is.False);
        });
    }

    // A typeof(x) argument written into an object-typed attribute parameter must
    // carry the boxed-type tag (SERIALIZATION_TYPE_TYPE); without it the blob
    // reads as a bare SerString and decompilers cannot decode the attribute at
    // all ("Could not decode attribute arguments").
    [Test]
    public void TypeArgumentInObjectSlotIsBoxed()
    {
        var app = LoadApp();
        var assembly = app.AssembliesByName["UnityEngine.CoreModule"];

        var attributeType = assembly.InjectType("Tests", "TypeBoxedAttribute",
            app.SystemTypes.SystemAttributeType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var constructor = attributeType.InjectMethodContext(".ctor",
            app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.SpecialName
                | R.MethodAttributes.RTSpecialName | R.MethodAttributes.HideBySig,
            app.SystemTypes.SystemObjectType);

        var holder = assembly.InjectType("Tests", "TypeBoxedHolder",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        holder.AnalyzeCustomAttributeData();
        holder.CustomAttributes ??= [];
        var attribute = new AnalyzedCustomAttribute(constructor);
        attribute.ConstructorParameters.Add(new CustomAttributeTypeParameter(
            app.SystemTypes.SystemStringType, attribute, CustomAttributeParameterKind.ConstructorParam, 0));
        holder.CustomAttributes.Add(attribute);

        var module = Build(app, assembly.Name);

        var argument = module.GetAllTypes().First(t => t.FullName == "Tests.TypeBoxedHolder")
            .CustomAttributes.Single().Signature!.FixedArguments.Single();
        Assert.Multiple(() =>
        {
            Assert.That(argument.ArgumentType.IsTypeOf("System", "Object"), Is.True,
                "the declared parameter type stays object");
            Assert.That(argument.Element, Is.InstanceOf<BoxedArgument>(),
                "a Type value in an object slot must be a BoxedArgument so the blob carries its tag");
            var boxed = (BoxedArgument)argument.Element!;
            Assert.That(boxed.Type.IsTypeOf("System", "Type"), Is.True,
                "the boxed tag is SERIALIZATION_TYPE_TYPE");
            Assert.That((boxed.Value as TypeSignature)?.FullName, Is.EqualTo("System.String"));
        });
    }
}
