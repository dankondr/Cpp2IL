using System;
using System.Collections.Generic;
using System.Runtime.CompilerServices;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils.AsmResolver;

/// <summary>
/// Makes a copied member usable by recovered IL when native code proved a direct
/// access to metadata-private storage. This is deliberately called only while a
/// descriptor is emitted; it does not broaden untouched metadata.
/// </summary>
internal static class MemberAccessibility
{
    // Populate and body-filling run parallel per assembly, and a method's own
    // EnsureAccessible call can race the one its base member runs later; the
    // lock keeps each chain's normalize read/write atomic.
    private static readonly object NormalizeLock = new();
    public static void EnsureAccessible(FieldDefinition field)
    {
        field.Attributes = (field.Attributes & ~FieldAttributes.FieldAccessMask) | FieldAttributes.Public;
        EnsureDeclaringTypeAccessible(field.DeclaringType);
    }

    public static void EnsureAccessible(MethodDefinition method)
    {
        method.Attributes = (method.Attributes & ~MethodAttributes.MemberAccessMask) | MethodAttributes.Public;
        EnsureDeclaringTypeAccessible(method.DeclaringType);
    }

    /// <summary>
    /// Widens <paramref name="method"/> like <see cref="EnsureAccessible(MethodDefinition)"/>,
    /// but moves the whole override chain in one step. An override's member access must
    /// match its base member's in the recompiled C# (CS0507 otherwise), so widening one
    /// link without the others manufactures exactly that mismatch. Methods sharing the
    /// overridden slot - ancestors through the base-type chain and descendants anywhere
    /// in the application - are promoted together.
    /// </summary>
    /// <remarks>
    /// A chain member whose flags are frozen constrains the chain: members of external
    /// runtime assemblies keep their declared surface so downstream consumers see the
    /// real runtime shape. A frozen member that is already public still lets the chain
    /// promote; a frozen non-public member instead fixes the access its descendants must
    /// carry - the only legal cross-assembly override of <c>protected internal</c> is
    /// <c>protected</c>, of <c>protected</c> is <c>protected</c>, of <c>public</c> is
    /// <c>public</c>. Descendants of a frozen member that cannot be legally overridden at
    /// all (private or assembly-scoped access) keep their declared flags - the metadata
    /// already described a chain C# cannot express.
    /// </remarks>
    public static void EnsureAccessible(MethodAnalysisContext method) => NormalizeChain(method, promoteRoots: true);

    /// <summary>
    /// Same pass as <see cref="EnsureAccessible(MethodAnalysisContext)"/> but without
    /// promotion: run while a method's own <see cref="MethodDefinition"/> is populated,
    /// so an emitted override's flags are legal relative to its base's emitted surface
    /// even when nothing references the member. Chain roots keep their declared access.
    /// </summary>
    internal static void NormalizeEmittedOverrideAccess(MethodAnalysisContext method) =>
        NormalizeChain(method, promoteRoots: false);

    private static void NormalizeChain(MethodAnalysisContext method, bool promoteRoots)
    {
        var required = new Dictionary<MethodAnalysisContext, MethodAttributes>();
        var chain = new HashSet<MethodAnalysisContext>(OverrideChain(method));
        lock (NormalizeLock)
        {
            foreach (var member in chain)
            {
                if (member.GetExtraData<MethodDefinition>("AsmResolverMethod") is not { } emitted
                    || AccessibilityExtensions.IsExternalRuntimeAssembly(member.DeclaringType?.DeclaringAssembly?.Name))
                    continue; // frozen links contribute their declared access via RequiredAccess

                var access = RequiredAccess(member);
                emitted.Attributes = (emitted.Attributes & ~MethodAttributes.MemberAccessMask) | access;
                EnsureDeclaringTypeAccessible(emitted.DeclaringType);
            }
        }

        // The access an override must carry given the effective access of the member
        // it overrides; the same relation the C# compiler enforces for CS0507.
        MethodAttributes RequiredAccess(MethodAnalysisContext member)
        {
            if (required.TryGetValue(member, out var cached))
                return cached;

            var declared = DeclaredAccess(member);
            required[member] = declared; // provisional: breaks corrupted-metadata cycles
            var requiredAccess = declared;
            if (member.GetExtraData<MethodDefinition>("AsmResolverMethod") is not null
                && !AccessibilityExtensions.IsExternalRuntimeAssembly(member.DeclaringType?.DeclaringAssembly?.Name))
            {
                var parent = Canonical(ResolveOverriddenMethod(member));
                requiredAccess = parent != null && chain.Contains(parent)
                    ? RequiredAccess(parent) switch
                    {
                        MethodAttributes.Public => MethodAttributes.Public,
                        // Protected internal stays intact only where the base's
                        // emitted assembly shares its internals with the override's -
                        // the output formats that restore InternalsVisibleTo include
                        // stub assemblies as grantors. Elsewhere C# requires the
                        // override to drop internal.
                        MethodAttributes.FamilyOrAssembly when InternalScopeShared(parent.DeclaringType?.DeclaringAssembly, member) => MethodAttributes.FamilyOrAssembly,
                        MethodAttributes.FamilyOrAssembly or MethodAttributes.Family => MethodAttributes.Family,
                        _ => declared, // unoverridable parent (private/assembly/family-and-assembly): keep declared
                    }
                    // A referenced member (and so its whole chain) must end up public;
                    // populate-time normalization leaves untouched roots at declared.
                    : promoteRoots ? MethodAttributes.Public : declared;
            }

            return required[member] = requiredAccess;
        }
    }

    // Mirrors the friend scope RestoreInternalsVisibleTo emits: every generated
    // assembly carries InternalsVisibleTo to each sibling whose name is not a
    // runtime assembly's, so the internal half of a protected internal base is
    // visible to non-stub overrides and they must keep it.
    private static bool InternalScopeShared(AssemblyAnalysisContext? parentAssembly, MethodAnalysisContext member)
    {
        var memberAssembly = member.DeclaringType?.DeclaringAssembly;
        if (parentAssembly is null || memberAssembly is null)
            return false;
        if (ReferenceEquals(parentAssembly, memberAssembly) || parentAssembly.Name == memberAssembly.Name)
            return true;
        return AccessibilityExtensions.EmittedInternalsAreShared
            && parentAssembly.GetExtraData<AssemblyDefinition>("AsmResolverAssembly") is not null
            && memberAssembly.Name is { } name
            && !AccessibilityExtensions.IsExternalRuntimeAssembly(name)
            // A friend name with a public key yields an InternalsVisibleTo that
            // can never bind, because the emitted assembly is unsigned; internals
            // are effectively not shared with it.
            && memberAssembly.PublicKey is null;
    }

    // Declared access is read off the analysis context, not the emitted
    // definition, so repeated normalization of a member stays idempotent.
    private static MethodAttributes DeclaredAccess(MethodAnalysisContext member) =>
        (MethodAttributes)(member.Attributes & System.Reflection.MethodAttributes.MemberAccessMask);

    private static List<MethodAnalysisContext> OverrideChain(MethodAnalysisContext method)
    {
        var chain = new List<MethodAnalysisContext>();
        var queue = new Queue<MethodAnalysisContext>();
        var seen = new HashSet<MethodAnalysisContext>();
        var children = OverrideChildren(method.AppContext);
        var start = Canonical(method)!;
        seen.Add(start);
        queue.Enqueue(start);
        while (queue.Count > 0)
        {
            var current = queue.Dequeue();
            chain.Add(current);
            if (Canonical(ResolveOverriddenMethod(current)) is { } baseMethod && seen.Add(baseMethod))
                queue.Enqueue(baseMethod);
            if (children.TryGetValue(current, out var overrides))
                foreach (var @override in overrides)
                    if (seen.Add(@override))
                        queue.Enqueue(@override);
        }
        return chain;
    }

    // Concrete generic contexts delegate their flags to the definition's context;
    // the override graph keys everything on the definition.
    private static MethodAnalysisContext? Canonical(MethodAnalysisContext? method) =>
        method is ConcreteGenericMethodAnalysisContext concrete ? concrete.BaseMethodContext : method;

    private static MethodAnalysisContext? ResolveOverriddenMethod(MethodAnalysisContext method)
    {
        if (!method.IsVirtual || method.IsStatic || method.IsNewSlot)
            return null;

        if (method.Definition != null)
        {
            try
            {
                if (Canonical(method.BaseMethod) is { } baseMethod)
                    return baseMethod;
            }
            catch
            {
                // Damaged vtables can defeat slot-based resolution; the signature
                // fallback below still finds the base the override binds to.
            }
        }

        return OverriddenBySignature(method);
    }

    // A virtual method reusing a slot overrides the nearest base member with the
    // same name and signature - the same rule the CLR applies. Used for injected
    // contexts (no metadata, no vtable) and as a fallback for damaged ones.
    private static MethodAnalysisContext? OverriddenBySignature(MethodAnalysisContext method)
    {
        // A generic-instance scope contributes its definition's methods plus a type
        // substitution, and the walk continues at the definition's own base: instances
        // built from raw il2cpp types never populate their own BaseType.
        var substitutions = new List<IReadOnlyList<TypeAnalysisContext>>();
        for (var scope = method.DeclaringType?.BaseType; scope is not null;)
        {
            var container = scope;
            if (scope is GenericInstanceTypeAnalysisContext instance)
            {
                container = instance.GenericType;
                substitutions.Add(instance.GenericArguments);
            }
            foreach (var candidate in container.Methods)
            {
                if (!candidate.IsVirtual || candidate.IsStatic || candidate.Name != method.Name)
                    continue;
                if (SignaturesMatch(candidate, method, substitutions))
                    return candidate;
            }
            scope = container.BaseType;
        }
        return null;
    }

    private static bool SignaturesMatch(MethodAnalysisContext candidate, MethodAnalysisContext method,
        List<IReadOnlyList<TypeAnalysisContext>> substitutions)
    {
        if (candidate.Parameters.Count != method.Parameters.Count
            || candidate.GenericParameters.Count != method.GenericParameters.Count)
            return false;
        for (var i = 0; i < method.Parameters.Count; i++)
        {
            var expected = method.Parameters[i].ParameterType;
            var actual = candidate.Parameters[i].ParameterType;
            // Innermost instantiation first: T_C -> T_D via the deeper scope's args,
            // then T_D -> X via the shallower one.
            for (var s = substitutions.Count - 1; s >= 0; s--)
            {
                try
                {
                    actual = GenericInstantiation.Instantiate(actual, substitutions[s], []);
                }
                catch
                {
                    return false;
                }
            }
            if (actual.FullName != expected.FullName)
                return false;
        }
        return true;
    }

    // Overriding members are found from each method's own base resolution; the
    // reverse index (base -> overriders) is built once per application because a
    // widened base must widen every override derived from it.
    private static readonly ConditionalWeakTable<ApplicationAnalysisContext, Lazy<Dictionary<MethodAnalysisContext, List<MethodAnalysisContext>>>> OverrideChildrenCache = new();

    private static Dictionary<MethodAnalysisContext, List<MethodAnalysisContext>> OverrideChildren(ApplicationAnalysisContext appContext) =>
        OverrideChildrenCache.GetValue(appContext, static app =>
            new Lazy<Dictionary<MethodAnalysisContext, List<MethodAnalysisContext>>>(() => BuildOverrideChildren(app))).Value;

    private static Dictionary<MethodAnalysisContext, List<MethodAnalysisContext>> BuildOverrideChildren(ApplicationAnalysisContext appContext)
    {
        var children = new Dictionary<MethodAnalysisContext, List<MethodAnalysisContext>>();
        foreach (var type in appContext.AllTypes)
        foreach (var method in type.Methods)
        {
            var baseMethod = ResolveOverriddenMethod(method);
            if (baseMethod == null)
                continue;
            if (!children.TryGetValue(baseMethod, out var overrides))
                children[baseMethod] = overrides = [];
            overrides.Add(method);
        }
        return children;
    }

    private static void EnsureDeclaringTypeAccessible(TypeDefinition? type)
    {
        while (type != null)
        {
            var visibility = type.DeclaringType == null
                ? TypeAttributes.Public
                : TypeAttributes.NestedPublic;
            type.Attributes = (type.Attributes & ~TypeAttributes.VisibilityMask) | visibility;
            type = type.DeclaringType;
        }
    }
}
