using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: override-accessibility-mismatch (CS0507). Emitting a
// descriptor for a referenced method relaxes it to public so recovered IL can
// name it; relaxing one link of an override chain without the others makes the
// decompiled override change accessibility relative to its base. Promotion must
// move the whole chain together, and a chain rooted in a frozen runtime-assembly
// surface must keep its declared - already legal - access instead.
public class OverrideChainAccessibilityTests
{
    private static ApplicationAnalysisContext LoadApp()
    {
        Cpp2IlApi.ResetInternalState();
        return TestGameLoader.LoadSimple2022Game();
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

    private static (InjectedTypeAnalysisContext context, TypeDefinition emitted) AddType(
        AssemblyAnalysisContext assembly, ModuleDefinition module,
        string name, TypeAnalysisContext? baseType, TypeDefinition? emittedBase = null)
    {
        var context = assembly.InjectType("Recovered", name, baseType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var emitted = new TypeDefinition("Recovered", name, TypeAttributes.Public | TypeAttributes.Class)
        {
            BaseType = emittedBase ?? module.CorLibTypeFactory.Object.Type
        };
        module.TopLevelTypes.Add(emitted);
        context.PutExtraData("AsmResolverType", emitted);
        return (context, emitted);
    }

    private static MethodAttributes AccessOf(MethodDefinition method) =>
        method.Attributes & MethodAttributes.MemberAccessMask;

    private static void AssertLegalOverrideAccess(MethodDefinition @override, MethodDefinition baseMethod)
    {
        var overrideAccess = AccessOf(@override);
        var baseAccess = AccessOf(baseMethod);
        var sameAssembly = @override.DeclaringModule == baseMethod.DeclaringModule;
        var legal = overrideAccess == baseAccess
            || (!sameAssembly && baseAccess == MethodAttributes.FamilyOrAssembly
                && overrideAccess == MethodAttributes.Family);
        Assert.That(legal, Is.True,
            $"{@override.DeclaringType?.FullName}.{@override.Name} ({overrideAccess}) is not a legal override of "
            + $"{baseMethod.DeclaringType?.FullName}.{baseMethod.Name} ({baseAccess})");
    }

    // Three links in one assembly: widening the leaf must widen base and middle,
    // otherwise the leaf's override changes accessibility relative to its base.
    [Test]
    public void PromotionWidensWholeChainWithinOneAssembly()
    {
        var app = LoadApp();
        var module = new ModuleDefinition("Chain.dll");
        var asm = app.InjectAssembly("Recovered.Chain");
        var (baseType, baseEmitted) = AddType(asm, module, "ChainBase", app.SystemTypes.SystemObjectType);
        var (midType, midEmitted) = AddType(asm, module, "ChainMid", baseType, baseEmitted);
        var (leafType, leafEmitted) = AddType(asm, module, "ChainLeaf", midType, midEmitted);

        const R.MethodAttributes flags = R.MethodAttributes.Family | R.MethodAttributes.Virtual
            | R.MethodAttributes.HideBySig;
        var (_, baseMethod) = AddMethod(baseType, baseEmitted, module, "Act",
            flags | R.MethodAttributes.NewSlot);
        var (_, midMethod) = AddMethod(midType, midEmitted, module, "Act", flags);
        var (leaf, leafMethod) = AddMethod(leafType, leafEmitted, module, "Act", flags);

        MemberAccessibility.EnsureAccessible(leaf);

        Assert.Multiple(() =>
        {
            Assert.That(AccessOf(baseMethod), Is.EqualTo(MethodAttributes.Public));
            Assert.That(AccessOf(midMethod), Is.EqualTo(MethodAttributes.Public));
            AssertLegalOverrideAccess(midMethod, baseMethod);
            AssertLegalOverrideAccess(leafMethod, midMethod);
        });
    }

    // The same promotion applied to the base must reach every override, including
    // ones in a different emitted assembly.
    [Test]
    public void PromotionOfBaseWidensOverridesAcrossAssemblies()
    {
        var app = LoadApp();
        var module = new ModuleDefinition("Base.dll");
        var otherModule = new ModuleDefinition("Derived.dll");
        var baseAsm = app.InjectAssembly("Recovered.BaseAsm");
        var derivedAsm = app.InjectAssembly("Recovered.DerivedAsm");
        var (baseType, baseEmitted) = AddType(baseAsm, module, "RemoteBase", app.SystemTypes.SystemObjectType);
        var (derivedType, derivedEmitted) = AddType(derivedAsm, otherModule, "RemoteDerived", baseType, baseEmitted);

        const R.MethodAttributes flags = R.MethodAttributes.Family | R.MethodAttributes.Virtual
            | R.MethodAttributes.HideBySig;
        var (baseCtx, baseMethod) = AddMethod(baseType, baseEmitted, module, "Work",
            flags | R.MethodAttributes.NewSlot);
        var (_, derivedMethod) = AddMethod(derivedType, derivedEmitted, otherModule, "Work", flags);

        MemberAccessibility.EnsureAccessible(baseCtx);

        Assert.Multiple(() =>
        {
            Assert.That(AccessOf(derivedMethod), Is.EqualTo(MethodAttributes.Public));
            AssertLegalOverrideAccess(derivedMethod, baseMethod);
        });
    }

    // A base in an external runtime assembly keeps its declared surface, so the
    // override must keep its declared access too: promotion there would change
    // accessibility relative to the base the compiler sees.
    [Test]
    public void FrozenRuntimeBaseKeepsChainAtDeclaredAccess()
    {
        var app = LoadApp();
        var module = new ModuleDefinition("Game.dll");
        var runtimeModule = new ModuleDefinition("UnityEngine.RuntimeSurface.dll");
        var runtimeAsm = app.InjectAssembly("UnityEngine.RuntimeSurface");
        var gameAsm = app.InjectAssembly("Recovered.Game");
        var (baseType, baseEmitted) = AddType(runtimeAsm, runtimeModule, "SurfaceBase",
            app.SystemTypes.SystemObjectType);
        var (derivedType, derivedEmitted) = AddType(gameAsm, module, "GameDerived", baseType, baseEmitted);

        const R.MethodAttributes baseFlags = R.MethodAttributes.FamORAssem | R.MethodAttributes.Virtual
            | R.MethodAttributes.HideBySig | R.MethodAttributes.NewSlot;
        var (_, baseMethod) = AddMethod(baseType, baseEmitted, runtimeModule, "Tick", baseFlags);
        // Recovered metadata may still carry the source's protected internal on the
        // override; C# requires the cross-assembly override to drop internal.
        var (derived, derivedMethod) = AddMethod(derivedType, derivedEmitted, module, "Tick",
            R.MethodAttributes.FamORAssem | R.MethodAttributes.Virtual | R.MethodAttributes.HideBySig);

        MemberAccessibility.EnsureAccessible(derived);

        Assert.Multiple(() =>
        {
            Assert.That(AccessOf(baseMethod), Is.EqualTo(MethodAttributes.FamilyOrAssembly),
                "the runtime surface keeps its declared access");
            Assert.That(AccessOf(derivedMethod), Is.EqualTo(MethodAttributes.Family),
                "the override drops internal under a cross-assembly FamORAssem base");
            AssertLegalOverrideAccess(derivedMethod, baseMethod);
        });
    }

    // The recovery output restores InternalsVisibleTo between every emitted
    // assembly and its non-stub siblings, including runtime stubs: under that
    // grant the internal half of a FamORAssem base is visible, so the override
    // must keep FamORAssem instead of dropping to Family.
    [Test]
    public void RestoredInternalsVisibleToKeepsFamOrAssemOverride()
    {
        var app = LoadApp();
        var module = new ModuleDefinition("Game.dll");
        var runtimeModule = new ModuleDefinition("Runtime.dll");
        var runtimeAssembly = new AssemblyDefinition("UnityEngine.RuntimeSurface", new System.Version(1, 0, 0));
        runtimeAssembly.Modules.Add(runtimeModule);
        var runtimeAsm = app.InjectAssembly("UnityEngine.RuntimeSurface");
        runtimeAsm.PutExtraData("AsmResolverAssembly", runtimeAssembly);
        var gameAsm = app.InjectAssembly("Recovered.Game");

        var (baseType, baseEmitted) = AddType(runtimeAsm, runtimeModule, "SurfaceBase",
            app.SystemTypes.SystemObjectType);
        var (derivedType, derivedEmitted) = AddType(gameAsm, module, "GameDerived", baseType, baseEmitted);

        const R.MethodAttributes baseFlags = R.MethodAttributes.FamORAssem | R.MethodAttributes.Virtual
            | R.MethodAttributes.HideBySig | R.MethodAttributes.NewSlot;
        var (_, baseMethod) = AddMethod(baseType, baseEmitted, runtimeModule, "Tick", baseFlags);
        var (derived, derivedMethod) = AddMethod(derivedType, derivedEmitted, module, "Tick",
            R.MethodAttributes.FamORAssem | R.MethodAttributes.Virtual | R.MethodAttributes.HideBySig);

        AccessibilityExtensions.EmittedInternalsAreShared = true;
        try
        {
            MemberAccessibility.EnsureAccessible(derived);
        }
        finally
        {
            AccessibilityExtensions.EmittedInternalsAreShared = false;
        }

        Assert.Multiple(() =>
        {
            Assert.That(AccessOf(baseMethod), Is.EqualTo(MethodAttributes.FamilyOrAssembly));
            Assert.That(AccessOf(derivedMethod), Is.EqualTo(MethodAttributes.FamilyOrAssembly),
                "the override keeps protected internal when the friend's internals are shared");
            AssertLegalOverrideAccess(derivedMethod, baseMethod);
        });
    }

    // The override's declaring type derives from a generic instance; the base
    // member lives on the definition's own base further up.
    [Test]
    public void PromotionReachesOverridesAcrossAGenericInstanceBase()
    {
        var app = LoadApp();
        var module = new ModuleDefinition("Game.dll");
        var asm = app.InjectAssembly("Recovered.Game");
        var (rootType, rootEmitted) = AddType(asm, module, "Root", app.SystemTypes.SystemObjectType);
        var (midDef, midEmitted) = AddType(asm, module, "Mid", rootType, rootEmitted);
        var midInstance = new GenericInstanceTypeAnalysisContext(midDef, [app.SystemTypes.SystemObjectType]);
        var (leafType, leafEmitted) = AddType(asm, module, "Leaf", midInstance);

        const R.MethodAttributes flags = R.MethodAttributes.Family | R.MethodAttributes.Virtual
            | R.MethodAttributes.HideBySig;
        var (_, baseMethod) = AddMethod(rootType, rootEmitted, module, "Draw",
            flags | R.MethodAttributes.NewSlot);
        var (leaf, leafMethod) = AddMethod(leafType, leafEmitted, module, "Draw", flags);

        MemberAccessibility.EnsureAccessible(leaf);

        Assert.Multiple(() =>
        {
            Assert.That(AccessOf(baseMethod), Is.EqualTo(MethodAttributes.Public));
            AssertLegalOverrideAccess(leafMethod, baseMethod);
        });
    }

    // Injected contexts have no il2cpp Definition and no vtable, so the
    // slot-based base lookup cannot run; the signature fallback must still
    // link the chain. Promotion reaching the base proves the link.
    [Test]
    public void OverridesLinkBySignatureWhenMetadataIsAbsent()
    {
        var app = LoadApp();
        var module = new ModuleDefinition("Game.dll");
        var asm = app.InjectAssembly("Recovered.Game");
        var (baseType, baseEmitted) = AddType(asm, module, "MetaBase", app.SystemTypes.SystemObjectType);
        var (derivedType, derivedEmitted) = AddType(asm, module, "MetaDerived", baseType, baseEmitted);

        const R.MethodAttributes flags = R.MethodAttributes.Family | R.MethodAttributes.Virtual
            | R.MethodAttributes.HideBySig;
        var (baseCtx, baseMethod) = AddMethod(baseType, baseEmitted, module, "Ping",
            flags | R.MethodAttributes.NewSlot);
        var (derived, derivedMethod) = AddMethod(derivedType, derivedEmitted, module, "Ping", flags);

        Assert.Multiple(() =>
        {
            Assert.That(baseCtx.Definition, Is.Null);
            Assert.That(derived.Definition, Is.Null, "no metadata - slot resolution cannot run");
        });

        MemberAccessibility.EnsureAccessible(derived);

        Assert.Multiple(() =>
        {
            Assert.That(AccessOf(baseMethod), Is.EqualTo(MethodAttributes.Public),
                "the signature fallback found the base without a vtable");
            AssertLegalOverrideAccess(derivedMethod, baseMethod);
        });
    }

    // A newslot method with the same name starts a new chain and must not be
    // dragged along when a neighbouring chain is promoted.
    [Test]
    public void NewslotMethodIsNotPartOfTheChain()
    {
        var app = LoadApp();
        var module = new ModuleDefinition("Chain.dll");
        var asm = app.InjectAssembly("Recovered.Chain");
        var (baseType, baseEmitted) = AddType(asm, module, "SlotBase", app.SystemTypes.SystemObjectType);
        var (derivedType, derivedEmitted) = AddType(asm, module, "SlotDerived", baseType, baseEmitted);
        var (shadowType, shadowEmitted) = AddType(asm, module, "SlotShadow", derivedType, derivedEmitted);

        const R.MethodAttributes flags = R.MethodAttributes.Family | R.MethodAttributes.Virtual
            | R.MethodAttributes.HideBySig;
        var (_, baseMethod) = AddMethod(baseType, baseEmitted, module, "Render",
            flags | R.MethodAttributes.NewSlot);
        var (derived, derivedMethod) = AddMethod(derivedType, derivedEmitted, module, "Render", flags);
        var (_, shadowMethod) = AddMethod(shadowType, shadowEmitted, module, "Render",
            flags | R.MethodAttributes.NewSlot);

        MemberAccessibility.EnsureAccessible(derived);

        Assert.Multiple(() =>
        {
            Assert.That(AccessOf(derivedMethod), Is.EqualTo(MethodAttributes.Public));
            Assert.That(AccessOf(shadowMethod), Is.EqualTo(MethodAttributes.Family),
                "a newslot member opens a new chain and keeps its declared access");
            AssertLegalOverrideAccess(derivedMethod, baseMethod);
        });
    }
}
