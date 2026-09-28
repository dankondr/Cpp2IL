using System;
using System.Linq;
using AsmResolver.DotNet;
using Cpp2IL.Core.OutputFormats;
using NUnit.Framework;

namespace Cpp2IL.Core.Tests.Regression;

// castle-recovery#96 — the compile bucket internals-visible-to-key-mismatch
// (CS0281) fires wherever a keyed InternalsVisibleTo grant meets a recompiled
// output whose public key is empty (the recovered source compiles unsigned).
// Corpus inspection (183 emitted assemblies, 1,079 resolvable assembly
// references) found zero disagreement authored by Cpp2IL: every emitted
// definition carries byte-identical public key material to the il2cpp
// metadata, and every reference token matches its definition. The mismatches
// come from keyed grants — real metadata grants restored verbatim, and the
// synthetic sibling grants the recovery output injects — satisfying an
// unsigned recompile. Those are satisfied by the compile driver signing the
// output with the recovered key, not by Cpp2IL emitting different identity.
//
// This test pins the two invariants the classification rests on, so a future
// change that makes a grant disagree with the emitted friend's identity (or
// drops the key from an emitted definition) is caught here. It asserts current
// behaviour; if the emission semantics change on purpose, flip the assertions.
public class InternalsVisibleToKeyGrantTests
{
    private static string GrantArgument(AssemblyDefinition grantor, string friendName)
        => grantor.CustomAttributes
            .Where(a => a.Constructor?.DeclaringType?.Name == "InternalsVisibleToAttribute")
            .Select(a => a.Signature?.FixedArguments.FirstOrDefault().Element?.ToString())
            .SingleOrDefault(arg => arg == friendName || arg is not null && arg.StartsWith(friendName + ",", StringComparison.Ordinal))!;

    [Test]
    public void SyntheticGrantNamesExactlyTheEmittedFriendsKey()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();

        // Synthetic identities: an unsigned friend and a friend whose metadata
        // (stand-in: injected override) carries a public key and the matching
        // PublicKey assembly flag.
        var signedKey = Enumerable.Range(0, 160).Select(i => (byte)(i * 7 + 1)).ToArray();
        app.InjectAssembly("Recovered.UnsignedFriend");
        app.InjectAssembly("Recovered.SignedFriend",
            flags: (uint)AsmResolver.PE.DotNet.Metadata.Tables.AssemblyAttributes.PublicKey,
            publicKey: signedKey);

        var assemblies = new AsmResolverDllOutputFormatIlRecovery().BuildAssemblies(app);
        var unsignedFriend = assemblies.Single(a => a.Name == "Recovered.UnsignedFriend");
        var signedFriend = assemblies.Single(a => a.Name == "Recovered.SignedFriend");

        // The emitted definition keeps the full public key the metadata
        // carried, and stays flagged strong-named.
        Assert.That(signedFriend.PublicKey, Is.EqualTo(signedKey),
            "emitted definition dropped or changed the metadata public key");
        Assert.That(signedFriend.Attributes.HasFlag(
                AsmResolver.PE.DotNet.Metadata.Tables.AssemblyAttributes.PublicKey), Is.True,
            "emitted definition lost the PublicKey flag");

        var expectedGrant = "Recovered.SignedFriend, PublicKey="
            + string.Concat(signedKey.Select(b => b.ToString("x2")));

        // Every unkeyed sibling grantor emits the unkeyed friend bare and the
        // keyed friend with exactly the key its emitted definition claims. A
        // keyed grantor cannot name an unsigned friend (CS1726 under a signed
        // recompile), so it emits grants to keyed friends only.
        foreach (var grantor in assemblies.Where(a =>
                     a != unsignedFriend && a != signedFriend && a.Modules.Count > 0))
        {
            var grantorKeyed = grantor.PublicKey is { Length: > 0 };
            Assert.That(GrantArgument(grantor, "Recovered.UnsignedFriend"),
                grantorKeyed ? Is.Null : Is.EqualTo("Recovered.UnsignedFriend"),
                $"{grantor.Name}: unsigned friend gained a key suffix");
            Assert.That(GrantArgument(grantor, "Recovered.SignedFriend"),
                Is.EqualTo(expectedGrant),
                $"{grantor.Name}: keyed grant disagrees with the emitted identity");
        }
    }
}
