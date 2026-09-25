using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Tests;


public class GenericTypeArgsTests
{
    private ApplicationAnalysisContext _ctx = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _ctx = TestGameLoader.LoadSimple2022Game();
    }

    // Generic-instance types actually referenced in the fixture (field types — List<T>, Dictionary<K,V>, …).
    private System.Collections.Generic.List<GenericInstanceTypeAnalysisContext> GenericInstances()
        => _ctx.Assemblies.SelectMany(a => a.Types)
            .SelectMany(t => t.Fields.Select(f => f.FieldType))
            .OfType<GenericInstanceTypeAnalysisContext>()
            .ToList();

    [Test]
    public void Fixture_has_generic_instances()
    {
        Assert.That(GenericInstances(), Is.Not.Empty);
    }

    [Test]
    public void GetTypeName_appends_the_argument_list()
    {
        foreach (var gi in GenericInstances())
        {
            var name = CsFileUtils.GetTypeName(gi);

            Assert.That(name, Does.Contain("<").And.Contain(">"), name);
            Assert.That(name, Does.Not.Contain("`"),
                $"CLR generic arity marker should not be rendered: {name}");

            // the argument text is exactly each argument's own GetTypeName, comma-joined
            var expectedArgs = string.Join(", ", gi.GenericArguments.Select(CsFileUtils.GetTypeName));
            Assert.That(name, Does.EndWith("<" + expectedArgs + ">"), name);
        }
    }

    [Test]
    public void Open_generic_uses_its_parameters_as_rgctx_arguments()
    {
        var definition = _ctx.AssembliesByName["mscorlib"]
            .GetTypeByFullName("System.Collections.Generic.List`1")!;
        var instance = new GenericInstanceTypeAnalysisContext(definition, [_ctx.SystemTypes.SystemStringType]);

        Assert.Multiple(() =>
        {
            Assert.That(RgctxResolver.TypeArgumentsFor(definition), Is.EqualTo(definition.GenericParameters));
            Assert.That(RgctxResolver.TypeArgumentsFor(instance), Is.EqualTo(instance.GenericArguments));
        });
    }
}
