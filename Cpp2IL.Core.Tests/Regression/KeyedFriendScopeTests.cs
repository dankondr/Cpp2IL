using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using LibCpp2IL.Metadata;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// castle-recovery#124 — the emitted friend scope must model the signing world
// the recovered assemblies recompile in: keyed assemblies are public-signed
// with their recovered keys, so a keyed grantor's synthetic InternalsVisibleTo
// grants bind for keyed friends only. The old model answered for unsigned
// output (a keyed friend could never be named, an unkeyed one always could),
// which is backwards in both directions: an unkeyed consumer's reference to a
// keyed grantor's internal member stayed internal (CS0122 on recompile), and a
// keyed friend's reference widened it to public though its grant binds. The
// same relation governs overrides: an unkeyed assembly overriding a keyed
// grantor's protected internal member must drop to protected, while a keyed
// friend must keep protected internal.
public class KeyedFriendScopeTests
{
    private static readonly byte[] GrantorKey =
        Enumerable.Range(0, 160).Select(i => (byte)(i * 7 + 1)).ToArray();
    private static readonly byte[] FriendKey =
        Enumerable.Range(0, 160).Select(i => (byte)(i * 13 + 3)).ToArray();
    private const uint KeyFlag = (uint)AssemblyAttributes.PublicKey;

    private static ApplicationAnalysisContext LoadApp()
    {
        Cpp2IlApi.ResetInternalState();
        return TestGameLoader.LoadSimple2022Game();
    }

    private static AssemblyAnalysisContext InjectSibling(ApplicationAnalysisContext app,
        string name, byte[]? publicKey)
    {
        var assembly = publicKey is null
            ? app.InjectAssembly(name)
            : app.InjectAssembly(name, flags: KeyFlag, publicKey: publicKey);
        // SharesEmittedInternals answers for the emitted sibling set, which is
        // every recovered (metadata-backed) assembly; a bare definition marks
        // the injected context as one of them.
        assembly.Definition = new Il2CppAssemblyDefinition();
        return assembly;
    }

    private static (InjectedTypeAnalysisContext context, TypeDefinition emitted) AddType(
        AssemblyAnalysisContext assembly, ModuleDefinition module,
        string name, TypeAnalysisContext? baseType, TypeDefinition? emittedBase = null)
    {
        var context = assembly.InjectType("Recovered", name, baseType,
            R.TypeAttributes.NotPublic | R.TypeAttributes.Class);
        var emitted = new TypeDefinition("Recovered", name,
            TypeAttributes.NotPublic | TypeAttributes.Class)
        {
            BaseType = emittedBase ?? module.CorLibTypeFactory.Object.Type
        };
        module.TopLevelTypes.Add(emitted);
        context.PutExtraData("AsmResolverType", emitted);
        return (context, emitted);
    }

    private static (InjectedMethodAnalysisContext context, MethodDefinition emitted) AddMethod(
        InjectedTypeAnalysisContext type, TypeDefinition emittedType, ModuleDefinition module,
        string name, R.MethodAttributes attributes)
    {
        var context = type.InjectMethodContext(name, type.AppContext.SystemTypes.SystemVoidType,
            attributes, []);
        var emitted = new MethodDefinition(name, (MethodAttributes)context.Attributes,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        emittedType.Methods.Add(emitted);
        context.PutExtraData("AsmResolverMethod", emitted);
        return (context, emitted);
    }

    private static MethodAttributes AccessOf(MethodDefinition method) =>
        method.Attributes & MethodAttributes.MemberAccessMask;

    private static TypeAttributes VisibilityOf(TypeDefinition type) =>
        type.Attributes & TypeAttributes.VisibilityMask;

    private static void WithSharedInternals(System.Action body)
    {
        AccessibilityExtensions.EmittedInternalsAreShared = true;
        try
        {
            body();
        }
        finally
        {
            AccessibilityExtensions.EmittedInternalsAreShared = false;
        }
    }

    // The binary shows an unkeyed consumer calling a keyed grantor's internal
    // member: no grant can carry that access (a keyed grantor never names an
    // unkeyed friend), so the member and its declaring type must emit public.
    [Test]
    public void UnkeyedFriendReferenceWidensKeyedGrantorMemberToPublic()
    {
        var app = LoadApp();
        var grantor = InjectSibling(app, "Recovered.KeyedGrantor", GrantorKey);
        var consumer = InjectSibling(app, "Recovered.UnkeyedFriend", null);
        var grantorModule = new ModuleDefinition("KeyedGrantor.dll");
        var (owner, ownerEmitted) = AddType(grantor, grantorModule,
            "Owner", app.SystemTypes.SystemObjectType);
        var (caller, _) = AddType(consumer, new ModuleDefinition("UnkeyedFriend.dll"),
            "Caller", app.SystemTypes.SystemObjectType);
        var (member, memberEmitted) = AddMethod(owner, ownerEmitted, grantorModule,
            "Work", R.MethodAttributes.Assembly | R.MethodAttributes.HideBySig);

        WithSharedInternals(() =>
        {
            using (MemberAccessibility.EmittingFrom(caller))
                MemberAccessibility.EnsureAccessible(memberEmitted, member);
        });

        Assert.Multiple(() =>
        {
            Assert.That(AccessOf(memberEmitted), Is.EqualTo(MethodAttributes.Public),
                "the unkeyed consumer has no grant - the member must be public to compile");
            Assert.That(VisibilityOf(ownerEmitted), Is.EqualTo(TypeAttributes.Public));
        });
    }

    // A keyed friend re-signs with its recovered key, so the keyed grantor's
    // grant binds and internal suffices: the same reference must not widen the
    // member past the access the friend scope already carries.
    [Test]
    public void KeyedFriendReferenceStopsAtInternalOnKeyedGrantor()
    {
        var app = LoadApp();
        var grantor = InjectSibling(app, "Recovered.KeyedGrantor", GrantorKey);
        var consumer = InjectSibling(app, "Recovered.KeyedFriend", FriendKey);
        var grantorModule = new ModuleDefinition("KeyedGrantor.dll");
        var (owner, ownerEmitted) = AddType(grantor, grantorModule,
            "Owner", app.SystemTypes.SystemObjectType);
        var (caller, _) = AddType(consumer, new ModuleDefinition("KeyedFriend.dll"),
            "Caller", app.SystemTypes.SystemObjectType);
        var (member, memberEmitted) = AddMethod(owner, ownerEmitted, grantorModule,
            "Work", R.MethodAttributes.Assembly | R.MethodAttributes.HideBySig);

        WithSharedInternals(() =>
        {
            using (MemberAccessibility.EmittingFrom(caller))
                MemberAccessibility.EnsureAccessible(memberEmitted, member);
        });

        Assert.Multiple(() =>
        {
            Assert.That(AccessOf(memberEmitted), Is.EqualTo(MethodAttributes.Assembly),
                "the bound grant makes internal sufficient - widening to public is gratuitous");
            Assert.That(VisibilityOf(ownerEmitted), Is.EqualTo(TypeAttributes.NotPublic));
        });
    }

    private static void FamOrAssemChain(
        ApplicationAnalysisContext app,
        AssemblyAnalysisContext grantor, ModuleDefinition grantorModule,
        AssemblyAnalysisContext derivedAsm, ModuleDefinition derivedModule,
        out MethodDefinition baseMethod, out InjectedMethodAnalysisContext derived)
    {
        var (baseType, baseEmitted) = AddType(grantor, grantorModule,
            "ChainBase", app.SystemTypes.SystemObjectType);
        var (derivedType, derivedEmitted) = AddType(derivedAsm, derivedModule,
            "ChainDerived", baseType, baseEmitted);

        const R.MethodAttributes baseFlags = R.MethodAttributes.FamORAssem | R.MethodAttributes.Virtual
            | R.MethodAttributes.HideBySig | R.MethodAttributes.NewSlot;
        var (_, emittedBase) = AddMethod(baseType, baseEmitted, grantorModule, "Tick", baseFlags);
        var (derivedCtx, _) = AddMethod(derivedType, derivedEmitted, derivedModule, "Tick",
            R.MethodAttributes.FamORAssem | R.MethodAttributes.Virtual | R.MethodAttributes.HideBySig);
        baseMethod = emittedBase;
        derived = derivedCtx;
    }

    private static AssemblyAnalysisContext EmittedGrantor(ApplicationAnalysisContext app,
        string name, byte[]? publicKey)
    {
        var grantor = InjectSibling(app, name, publicKey);
        grantor.PutExtraData("AsmResolverAssembly",
            new AssemblyDefinition(name, new System.Version(1, 0, 0)));
        return grantor;
    }

    // An unkeyed assembly cannot see the internal half of a keyed grantor's
    // protected internal base, so C# admits only the protected override.
    [Test]
    public void UnkeyedOverrideDropsInternalOverKeyedFamOrAssemBase()
    {
        var app = LoadApp();
        var grantor = EmittedGrantor(app, "Recovered.KeyedGrantor", GrantorKey);
        var derivedAsm = InjectSibling(app, "Recovered.UnkeyedFriend", null);
        FamOrAssemChain(app, grantor, new ModuleDefinition("KeyedGrantor.dll"),
            derivedAsm, new ModuleDefinition("UnkeyedFriend.dll"),
            out var baseMethod, out var derived);

        WithSharedInternals(() => MemberAccessibility.NormalizeEmittedOverrideAccess(derived));

        Assert.Multiple(() =>
        {
            Assert.That(AccessOf(baseMethod), Is.EqualTo(MethodAttributes.FamilyOrAssembly),
                "the keyed grantor's base keeps its declared access");
            Assert.That(AccessOf(derived.GetExtraData<MethodDefinition>("AsmResolverMethod")!),
                Is.EqualTo(MethodAttributes.Family),
                "the unkeyed override drops internal - the grant set cannot carry it");
        });
    }

    // A keyed friend sees the internal half through its bound grant, so it
    // keeps protected internal - the only override access C# accepts.
    [Test]
    public void KeyedOverrideKeepsFamOrAssemOverKeyedBase()
    {
        var app = LoadApp();
        var grantor = EmittedGrantor(app, "Recovered.KeyedGrantor", GrantorKey);
        var derivedAsm = InjectSibling(app, "Recovered.KeyedFriend", FriendKey);
        FamOrAssemChain(app, grantor, new ModuleDefinition("KeyedGrantor.dll"),
            derivedAsm, new ModuleDefinition("KeyedFriend.dll"),
            out var baseMethod, out var derived);

        WithSharedInternals(() => MemberAccessibility.NormalizeEmittedOverrideAccess(derived));

        Assert.Multiple(() =>
        {
            Assert.That(AccessOf(baseMethod), Is.EqualTo(MethodAttributes.FamilyOrAssembly));
            Assert.That(AccessOf(derived.GetExtraData<MethodDefinition>("AsmResolverMethod")!),
                Is.EqualTo(MethodAttributes.FamilyOrAssembly),
                "the keyed override keeps protected internal - its grant binds");
        });
    }

    // An unkeyed grantor names every sibling (its grant list carries no key
    // constraint), so the keyed override keeps protected internal.
    [Test]
    public void UnkeyedGrantorSharesInternalsWithKeyedOverride()
    {
        var app = LoadApp();
        var grantor = EmittedGrantor(app, "Recovered.UnkeyedGrantor", null);
        var derivedAsm = InjectSibling(app, "Recovered.KeyedFriend", FriendKey);
        FamOrAssemChain(app, grantor, new ModuleDefinition("UnkeyedGrantor.dll"),
            derivedAsm, new ModuleDefinition("KeyedFriend.dll"),
            out _, out var derived);

        WithSharedInternals(() => MemberAccessibility.NormalizeEmittedOverrideAccess(derived));

        Assert.That(AccessOf(derived.GetExtraData<MethodDefinition>("AsmResolverMethod")!),
            Is.EqualTo(MethodAttributes.FamilyOrAssembly),
            "an unkeyed grantor's internals reach every friend, keyed or not");
    }

    // The all-unkeyed pairing is unchanged: internals are shared and the
    // override keeps protected internal.
    [Test]
    public void UnkeyedPairingKeepsFamOrAssem()
    {
        var app = LoadApp();
        var grantor = EmittedGrantor(app, "Recovered.UnkeyedGrantor", null);
        var derivedAsm = InjectSibling(app, "Recovered.UnkeyedFriend", null);
        FamOrAssemChain(app, grantor, new ModuleDefinition("UnkeyedGrantor.dll"),
            derivedAsm, new ModuleDefinition("UnkeyedFriend.dll"),
            out _, out var derived);

        WithSharedInternals(() => MemberAccessibility.NormalizeEmittedOverrideAccess(derived));

        Assert.That(AccessOf(derived.GetExtraData<MethodDefinition>("AsmResolverMethod")!),
            Is.EqualTo(MethodAttributes.FamilyOrAssembly));
    }
}
