using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.OutputFormats;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: unpaired operators (CS0216 in the recovered compile tree).
// IL2CPP managed-code stripping removes the partner of a required operator pair
// (e.g. op_Inequality next to op_Equality) from global-metadata.dat, so the
// recovered assembly can honestly carry only one side. These tests pin the
// emission contract: every op_* declared in the metadata is emitted verbatim —
// name, signature arity and the specialname bit — and no partner is fabricated.
public class UnpairedOperatorEmissionTests
{
    private static bool IsOperator(MethodAnalysisContext method) =>
        method.Definition is not null && method.Name.StartsWith("op_");

    private static bool IsOperator(MethodDefinition method) =>
        method.Name is not null && method.Name.ToString().StartsWith("op_");

    private static List<(string Name, int ParamCount, bool SpecialName)> DeclaredOperators(TypeAnalysisContext typeContext) =>
        typeContext.Methods
            .Where(IsOperator)
            .Select(m => (m.Name, m.Parameters.Count, (m.Attributes & R.MethodAttributes.SpecialName) != 0))
            .OrderBy(m => m.Name).ThenBy(m => m.Item2).ThenBy(m => m.Item3)
            .ToList();

    private static List<(string Name, int ParamCount, bool SpecialName)> EmittedOperators(TypeDefinition type) =>
        type.Methods
            .Where(IsOperator)
            .Select(m => (m.Name!.ToString(), m.Signature!.ParameterTypes.Count, m.Attributes.HasFlag(MethodAttributes.SpecialName)))
            .OrderBy(m => m.Item1).ThenBy(m => m.Item2).ThenBy(m => m.Item3)
            .ToList();

    [Test]
    public void EveryTypeEmitsExactlyItsDeclaredOperators()
    {
        var appContext = TestGameLoader.LoadSimple2019Game();
        new AsmResolverDllOutputFormatEmpty().BuildAssemblies(appContext);

        var declaredTotal = 0;

        Assert.Multiple(() =>
        {
            foreach (var typeContext in appContext.Assemblies.SelectMany(a => a.Types))
            {
                var emittedType = typeContext.GetExtraData<TypeDefinition>("AsmResolverType");
                if (emittedType is null)
                    continue;

                var declared = DeclaredOperators(typeContext);
                var emitted = EmittedOperators(emittedType);
                declaredTotal += declared.Count;

                Assert.That(emitted, Is.EqualTo(declared),
                    $"Emitted op_* set of {typeContext.FullName} differs from the metadata-declared set");
            }
        });

        // Sanity: the fixture really does carry operator methods to compare.
        Assert.That(declaredTotal, Is.GreaterThan(0));
    }

    [Test]
    public void PairedOperatorsEmitBothPartners()
    {
        var appContext = TestGameLoader.LoadSimple2019Game();
        new AsmResolverDllOutputFormatEmpty().BuildAssemblies(appContext);

        var vector3 = appContext.Assemblies
            .SelectMany(a => a.Types)
            .Single(t => t.FullName == "UnityEngine.Vector3");
        var emittedType = vector3.GetExtraData<TypeDefinition>("AsmResolverType")!;

        var equality = emittedType.Methods.Where(m => m.Name == "op_Equality").ToList();
        var inequality = emittedType.Methods.Where(m => m.Name == "op_Inequality").ToList();

        Assert.Multiple(() =>
        {
            Assert.That(equality, Has.Count.EqualTo(1));
            Assert.That(inequality, Has.Count.EqualTo(1));
            Assert.That(equality[0].Attributes.HasFlag(MethodAttributes.SpecialName), Is.True);
            Assert.That(inequality[0].Attributes.HasFlag(MethodAttributes.SpecialName), Is.True);
        });
    }

    [Test]
    public void LoneOperatorEmitsWithoutFabricatedPartner()
    {
        var appContext = TestGameLoader.LoadSimple2019Game();
        new AsmResolverDllOutputFormatEmpty().BuildAssemblies(appContext);

        var dateTime = appContext.Assemblies
            .SelectMany(a => a.Types)
            .Single(t => t.FullName == "System.DateTime");
        var emittedType = dateTime.GetExtraData<TypeDefinition>("AsmResolverType")!;

        // Fixture sanity: the metadata itself declares the survivor only.
        var declared = DeclaredOperators(dateTime);
        Assert.Multiple(() =>
        {
            Assert.That(declared.Any(m => m.Name == "op_Equality"), Is.True,
                "fixture drift: System.DateTime no longer carries a lone op_Equality");
            Assert.That(declared.Any(m => m.Name == "op_Inequality"), Is.False,
                "fixture drift: System.DateTime gained op_Inequality in metadata");
        });

        var emittedEquality = emittedType.Methods.Where(m => m.Name == "op_Equality").ToList();
        var emittedInequality = emittedType.Methods.Where(m => m.Name == "op_Inequality").ToList();

        Assert.Multiple(() =>
        {
            // The surviving operator is emitted with its specialname bit.
            Assert.That(emittedEquality, Has.Count.EqualTo(declared.Count(m => m.Name == "op_Equality")));
            Assert.That(emittedEquality.All(m => m.Attributes.HasFlag(MethodAttributes.SpecialName)), Is.True);
            // The stripped partner is not invented.
            Assert.That(emittedInequality, Is.Empty);
        });
    }
}
