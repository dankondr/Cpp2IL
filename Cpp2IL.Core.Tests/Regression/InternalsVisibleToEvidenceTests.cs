using System.Linq;
using AsmResolver.DotNet;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.OutputFormats;
using NUnit.Framework;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// castle-recovery#125 — blanket InternalsVisibleTo grants exposed every
// emitted internal type to every consumer. Two packages that compile the same
// internal polyfill privately (the real collision: separate NuGet libraries
// each carrying an internal NotNullWhenAttribute) then presented both copies
// to a consumer that names the type through the runtime library — CS0433.
// Grants are now emitted only where the friend's own emitted metadata
// demonstrably touches the grantor's internals, so an internal type stays
// hidden from consumers that never referenced it.
public class InternalsVisibleToEvidenceTests
{
    private static string[] Grants(AssemblyDefinition grantor)
        => grantor.CustomAttributes
            .Where(a => a.Constructor?.DeclaringType?.Name == "InternalsVisibleToAttribute")
            .Select(a => a.Signature?.FixedArguments.FirstOrDefault().Element?.ToString())
            .Where(arg => arg is not null)
            .ToArray()!;

    [Test]
    public void GrantRequiresInternalAccessEvidence()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();

        // Two packages carrying an internal polyfill under the same name - the
        // collision shape from the real compile.
        var packageA = app.InjectAssembly("Recovered.PackageA");
        var packageB = app.InjectAssembly("Recovered.PackageB");
        // A consumer that never touches either package's internals: under the
        // blanket grant it still saw both polyfill copies.
        app.InjectAssembly("Recovered.Consumer");
        // A consumer that demonstrably touches packageA's internals.
        var internalUser = app.InjectAssembly("Recovered.InternalUser");

        var markerA = packageA.InjectType("Polyfill", "SharedMarker",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.NotPublic | R.TypeAttributes.Class | R.TypeAttributes.Sealed);
        packageB.InjectType("Polyfill", "SharedMarker",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.NotPublic | R.TypeAttributes.Class | R.TypeAttributes.Sealed);

        // A private field keeps the reference private, so the type stays
        // internal and the field's signature is the only access evidence.
        var holder = internalUser.InjectType("Recovered", "Holder",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        holder.InjectFieldContext("marker", markerA,
            R.FieldAttributes.Private | R.FieldAttributes.Static);

        var assemblies = new AsmResolverDllOutputFormatIlRecovery().BuildAssemblies(app);
        var grantsA = Grants(assemblies.Single(a => a.Name == "Recovered.PackageA"));
        var grantsB = Grants(assemblies.Single(a => a.Name == "Recovered.PackageB"));

        // No internal access: no grant, so neither polyfill copy is visible.
        Assert.That(grantsA, Has.None.EqualTo("Recovered.Consumer"));
        Assert.That(grantsB, Has.None.EqualTo("Recovered.Consumer"));

        // The one exercised edge keeps its grant.
        Assert.That(grantsA, Has.Some.EqualTo("Recovered.InternalUser"));
        Assert.That(grantsB, Has.None.EqualTo("Recovered.InternalUser"));
    }
}
