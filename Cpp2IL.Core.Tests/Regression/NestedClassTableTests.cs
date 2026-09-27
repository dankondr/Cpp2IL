using System.Collections.Generic;
using System.IO;
using System.Linq;
using AsmResolver;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Builder;
using AsmResolver.PE;
using AsmResolver.PE.DotNet.Metadata;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.OutputFormats;

namespace Cpp2IL.Core.Tests.Regression;

// castle-recovery#53 — every emitted NestedClass row must be unique per nested
// typedef and have an enclosing index inside the TypeDef table.
public class NestedClassTableTests
{
    [Test]
    public void EmittedNestedClassRowsAreInRangeAndUnique()
    {
        var appContext = TestGameLoader.LoadSimple2019Game();

        var assemblies = new AsmResolverDllOutputFormatDefault().BuildAssemblies(appContext);

        foreach (var assembly in assemblies)
        {
            using MemoryStream stream = new();
            assembly.WriteManifest(stream, new ManagedPEImageBuilder(ThrowErrorListener.Instance));

            var image = PEImage.FromBytes(stream.ToArray());
            var tables = image.DotNetDirectory!.Metadata!.GetStream<TablesStream>();
            var typeDefCount = tables.GetTable<TypeDefinitionRow>(TableIndex.TypeDef).Count;
            var nestedRows = tables.GetTable<NestedClassRow>(TableIndex.NestedClass);

            var seen = new HashSet<uint>();
            foreach (var row in nestedRows)
            {
                Assert.That(row.EnclosingClass, Is.InRange(1u, (uint)typeDefCount),
                    $"{assembly.Name}: NestedClass row ({row.NestedClass}, {row.EnclosingClass}) exceeds TypeDef count {typeDefCount}");
                Assert.That(row.NestedClass, Is.InRange(1u, (uint)typeDefCount),
                    $"{assembly.Name}: NestedClass row ({row.NestedClass}, {row.EnclosingClass}) has out-of-range nested index");
                Assert.That(seen.Add(row.NestedClass), Is.True,
                    $"{assembly.Name}: duplicate NestedClass row for nested typedef {row.NestedClass}");
            }
        }
    }

    [Test]
    public void NestedTypeListedUnderAnotherParentIsEmittedOnlyUnderItsDeclaringType()
    {
        var appContext = TestGameLoader.LoadSimple2019Game();

        var hostAssembly = appContext.AssembliesByName["UnityEngine.CoreModule"];
        var hosts = hostAssembly.TopLevelTypes
            .Where(t => t.Name != "<Module>" && t is not InjectedTypeAnalysisContext)
            .Take(2)
            .ToList();
        Assert.That(hosts, Has.Count.EqualTo(2));
        var host = hosts[0];
        var otherHost = hosts[1];

        var nested = host.InjectNestedType("RegressionNestedProbe", appContext.SystemTypes.SystemObjectType);
        // il2cpp metadata can list a nested type under more than one parent;
        // the context's DeclaringType keeps pointing at its real parent, so the
        // stray listing must not produce a second typedef.
        otherHost.NestedTypes.Add(nested);

        var assemblies = new AsmResolverDllOutputFormatDefault().BuildAssemblies(appContext);
        var module = assemblies.First(a => a.Name == "UnityEngine.CoreModule").ManifestModule!;

        var emitted = module.GetAllTypes().Where(t => t.Name == "RegressionNestedProbe").ToList();
        Assert.That(emitted, Has.Count.EqualTo(1));
        Assert.That(emitted[0].DeclaringType?.Name, Is.EqualTo(host.Name));
    }
}
