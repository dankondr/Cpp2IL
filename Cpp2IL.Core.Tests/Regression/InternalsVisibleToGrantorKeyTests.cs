using System;
using System.Linq;
using AsmResolver.DotNet;
using Cpp2IL.Core.OutputFormats;
using NUnit.Framework;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// castle-recovery#110 — a strong-named assembly cannot grant InternalsVisibleTo
// to an unsigned friend: when the compile driver public-signs the recovered
// outputs with their recovered keys (castle-recovery#102), every unkeyed friend
// name on a keyed grantor is a CS1726. The synthetic sibling grants must list
// only keyed friends on keyed grantors; unkeyed grantors are unchanged.
// castle-recovery#125 — grants are also evidence-driven (only friends whose
// emitted metadata touches the grantor's internals receive one), so this test
// sets up the exercised edge on every grantor/friend pair before asserting the
// key rules.
public class InternalsVisibleToGrantorKeyTests
{
    private static string[] Grants(AssemblyDefinition grantor)
        => grantor.CustomAttributes
            .Where(a => a.Constructor?.DeclaringType?.Name == "InternalsVisibleToAttribute")
            .Select(a => a.Signature?.FixedArguments.FirstOrDefault().Element?.ToString())
            .Where(arg => arg is not null)
            .ToArray()!;

    [Test]
    public void KeyedGrantorGrantsOnlyKeyedFriends()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();

        // Synthetic identities: a keyed and an unkeyed grantor, a keyed and an
        // unkeyed friend — covering all four grantor/friend key combinations.
        var grantorKey = Enumerable.Range(0, 160).Select(i => (byte)(i * 7 + 1)).ToArray();
        var friendKey = Enumerable.Range(0, 160).Select(i => (byte)(i * 13 + 3)).ToArray();
        const uint keyFlag = (uint)AsmResolver.PE.DotNet.Metadata.Tables.AssemblyAttributes.PublicKey;
        var keyedGrantor = app.InjectAssembly("Recovered.KeyedGrantor", flags: keyFlag, publicKey: grantorKey);
        var unkeyedGrantor = app.InjectAssembly("Recovered.UnkeyedGrantor");
        var keyedFriend = app.InjectAssembly("Recovered.KeyedFriend", flags: keyFlag, publicKey: friendKey);
        var unkeyedFriend = app.InjectAssembly("Recovered.UnkeyedFriend");

        // Grants follow internal-access evidence: each grantor carries an
        // internal type each friend privately references, so every
        // grantor/friend pair is exercised before the key rules apply.
        var keyedDep = keyedGrantor.InjectType("Recovered", "KeyedGrantorDep",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.NotPublic | R.TypeAttributes.Class | R.TypeAttributes.Sealed);
        var unkeyedDep = unkeyedGrantor.InjectType("Recovered", "UnkeyedGrantorDep",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.NotPublic | R.TypeAttributes.Class | R.TypeAttributes.Sealed);
        foreach (var friend in new[] { keyedFriend, unkeyedFriend })
        {
            var holder = friend.InjectType("Recovered", "Deps",
                app.SystemTypes.SystemObjectType,
                R.TypeAttributes.Public | R.TypeAttributes.Class);
            holder.InjectFieldContext("keyedDep", keyedDep,
                R.FieldAttributes.Private | R.FieldAttributes.Static);
            holder.InjectFieldContext("unkeyedDep", unkeyedDep,
                R.FieldAttributes.Private | R.FieldAttributes.Static);
        }

        var assemblies = new AsmResolverDllOutputFormatIlRecovery().BuildAssemblies(app);
        var keyedGrantorEmitted = assemblies.Single(a => a.Name == "Recovered.KeyedGrantor");
        var unkeyedGrantorEmitted = assemblies.Single(a => a.Name == "Recovered.UnkeyedGrantor");

        var keyedFriendGrant = "Recovered.KeyedFriend, PublicKey="
            + string.Concat(friendKey.Select(b => b.ToString("x2")));

        // Keyed → keyed: the grant stays, named with the friend's recovered key.
        // Keyed → unkeyed: no grant — every name on a strong-named grantor
        // carries a PublicKey, so no unkeyed friend (and no invented key).
        var keyedGrants = Grants(keyedGrantorEmitted);
        Assert.That(keyedGrants, Has.Some.EqualTo(keyedFriendGrant),
            "keyed grantor dropped its keyed friend");
        Assert.That(keyedGrants, Has.All.Contains("PublicKey="),
            "keyed grantor emitted an unkeyed friend name");
        Assert.That(keyedGrants, Has.None.EqualTo("Recovered.UnkeyedFriend"),
            "keyed grantor granted to an unkeyed friend");

        // Unkeyed → keyed and unkeyed → unkeyed: byte-for-byte unchanged —
        // the keyed friend is named with its key, the unkeyed friend bare.
        var unkeyedGrants = Grants(unkeyedGrantorEmitted);
        Assert.That(unkeyedGrants, Has.Some.EqualTo(keyedFriendGrant),
            "unkeyed grantor lost the keyed friend's full key");
        Assert.That(unkeyedGrants, Has.Some.EqualTo("Recovered.UnkeyedFriend"),
            "unkeyed grantor lost the bare unkeyed friend name");
    }
}
