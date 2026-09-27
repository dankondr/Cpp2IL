using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Threading;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Logging;
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

    /// <summary>
    /// The type whose emitted artifact carries the member reference a widening
    /// answers to. Set per emitted member while the output format writes a body
    /// or member entry, so the widening stops at the least access that reference
    /// needs: nothing inside the member's private enclosing scope, internal
    /// inside the friend scope the recovery output recreates, public only for a
    /// genuinely external reference. Unset keeps the original promote-to-public
    /// behavior, so populate-time references stay conservative.
    /// </summary>
    private static readonly AsyncLocal<TypeAnalysisContext?> ReferencingType = new();

    internal static IDisposable EmittingFrom(TypeAnalysisContext? referencingType)
    {
        var restore = new RestoreReferencingType(ReferencingType.Value);
        ReferencingType.Value = referencingType;
        return restore;
    }

    private sealed class RestoreReferencingType(TypeAnalysisContext? previous) : IDisposable
    {
        public void Dispose() => ReferencingType.Value = previous;
    }

    // How far a member reference emitted in the ambient scope forces a member
    // to widen. The order is weakest first.
    private enum ReferenceScope
    {
        // Caller and member share a private enclosing scope: no widening at all.
        Private,
        // Caller is inside the friend scope the restored InternalsVisibleTo
        // grants, so internal is enough.
        Internal,
        // Caller is outside that scope (or unknown): the member must be public.
        Public,
    }

    private static ReferenceScope RequiredScope(TypeAnalysisContext? memberType)
    {
        if (memberType is null || ReferencingType.Value is not { } referencingType)
            return ReferenceScope.Public;
        if (SharesPrivateScope(memberType, referencingType))
            return ReferenceScope.Private;
        var memberAssembly = memberType.DeclaringAssembly;
        var referencingAssembly = referencingType.DeclaringAssembly;
        if (ReferenceEquals(memberAssembly, referencingAssembly)
            || memberAssembly?.Name is { } memberName && memberName == referencingAssembly?.Name)
            return ReferenceScope.Internal;
        // Cross-assembly internals reach the reference through the restored
        // InternalsVisibleTo grants - but a grant naming a friend with a
        // public key can never bind, because the emitted assembly is unsigned
        // (the same asymmetry InternalScopeShared bakes into chain promotion).
        return AccessibilityExtensions.SharesEmittedInternals(memberAssembly, referencingAssembly)
            && referencingAssembly?.PublicKey is null
            ? ReferenceScope.Internal
            : ReferenceScope.Public;
    }

    // A private member is visible only within the program text of its own
    // declaring type, including types nested inside it. Unlike the CLR, C#
    // gives an enclosing type no access to a nested type's privates, so only
    // the downward direction qualifies.
    private static bool SharesPrivateScope(TypeAnalysisContext memberType, TypeAnalysisContext referencingType) =>
        IsWithinOrSame(referencingType, memberType);

    private static bool IsWithinOrSame(TypeAnalysisContext candidate, TypeAnalysisContext ancestor)
    {
        var target = Unwrap(ancestor);
        for (var current = Unwrap(candidate); current != null; current = Unwrap(current.DeclaringType))
            if (ReferenceEquals(current, target))
                return true;
        return false;
    }

    // Generic instances rebuild their context per instantiation; the scope
    // check cares about the underlying definition's nesting.
    private static TypeAnalysisContext? Unwrap(TypeAnalysisContext? type) =>
        type is GenericInstanceTypeAnalysisContext instance ? instance.GenericType : type;

    // Member access bits and nested type visibility bits describe the same
    // ladder renumbered, and every level includes the declaring type itself, so
    // private is covered by all of them and only the family/assembly pair is
    // incomparable - their join is fam-or-assem.
    private static int JoinAccess(int a, int b)
    {
        if (a == b)
            return a;
        if (a == 6 || b == 6)
            return 6;
        if (a == 5 || b == 5)
            return 5;
        if (a == 4 || b == 4)
            return a == 3 || b == 3 ? 5 : 4;
        return Math.Max(a, b);
    }

    private static int RequiredRank(ReferenceScope scope) => scope switch
    {
        ReferenceScope.Internal => 3,
        ReferenceScope.Public => 6,
        _ => 0,
    };

    public static void EnsureAccessible(FieldDefinition field, FieldAnalysisContext? context = null)
    {
        var scope = RequiredScope(context?.DeclaringType);
        if (scope == ReferenceScope.Private)
            return; // an in-scope reference leaves every flag as declared
        lock (NormalizeLock)
        {
            var access = (FieldAttributes)JoinAccess(
                (int)(field.Attributes & FieldAttributes.FieldAccessMask), RequiredRank(scope));
            field.Attributes = (field.Attributes & ~FieldAttributes.FieldAccessMask) | access;
            if (field.DeclaringType != null)
                WidenTypeAndAncestors(field.DeclaringType, RequiredRank(scope), []);
            if (context != null)
                EnsureSignatureTypesAccessible((int)access, context.FieldType);
        }
    }

    public static void EnsureAccessible(MethodDefinition method, MethodAnalysisContext? context = null)
    {
        var scope = RequiredScope(context?.DeclaringType);
        if (scope == ReferenceScope.Private)
            return;
        lock (NormalizeLock)
        {
            var access = (MethodAttributes)JoinAccess(
                (int)(method.Attributes & MethodAttributes.MemberAccessMask), RequiredRank(scope));
            method.Attributes = (method.Attributes & ~MethodAttributes.MemberAccessMask) | access;
            if (method.DeclaringType != null)
                WidenTypeAndAncestors(method.DeclaringType, RequiredRank(scope), []);
            if (context != null)
                EnsureSignatureTypesAccessible((int)access, context);
        }
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
    public static void EnsureAccessible(MethodAnalysisContext method) =>
        NormalizeChain(method, promoteRoots: true, RequiredScope(method.DeclaringType));

    /// <summary>
    /// Same pass as <see cref="EnsureAccessible(MethodAnalysisContext)"/> but without
    /// promotion: run while a method's own <see cref="MethodDefinition"/> is populated,
    /// so an emitted override's flags are legal relative to its base's emitted surface
    /// even when nothing references the member. Chain roots keep their declared access.
    /// </summary>
    internal static void NormalizeEmittedOverrideAccess(MethodAnalysisContext method) =>
        NormalizeChain(method, promoteRoots: false, ReferenceScope.Public);

    private static void NormalizeChain(MethodAnalysisContext method, bool promoteRoots, ReferenceScope scope)
    {
        var required = new Dictionary<MethodAnalysisContext, MethodAttributes>();
        var chain = new HashSet<MethodAnalysisContext>(OverrideChain(method));
        var rank = RequiredRank(scope);
        lock (NormalizeLock)
        {
            foreach (var member in chain)
            {
                if (member.GetExtraData<MethodDefinition>("AsmResolverMethod") is not { } emitted
                    || AccessibilityExtensions.IsExternalRuntimeAssembly(member.DeclaringType?.DeclaringAssembly?.Name))
                    continue; // frozen links contribute their declared access via RequiredAccess

                var declared = DeclaredAccess(member);
                var access = RequiredAccess(member);
                // RequiredAccess legitimately lowers access for frozen-base
                // chains, so join only against access that was already widened
                // (emitted flags no longer at their declared copy), not against
                // declared: a weaker later reference must not narrow an earlier
                // widening.
                if ((emitted.Attributes & MethodAttributes.MemberAccessMask) != declared)
                    access = (MethodAttributes)JoinAccess(
                        (int)access, (int)(emitted.Attributes & MethodAttributes.MemberAccessMask));
                emitted.Attributes = (emitted.Attributes & ~MethodAttributes.MemberAccessMask) | access;
                // Widening the declaring type exists so a reference site can
                // name it; populate-time normalization has no site. A member
                // may legally stay more visible than its containing type.
                if (promoteRoots && emitted.DeclaringType != null)
                    WidenTypeAndAncestors(emitted.DeclaringType, rank, []);
                if (access > declared)
                    EnsureSignatureTypesAccessible((int)access, member);
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
                    // A referenced member's chain promotes to the access the
                    // ambient reference needs; populate-time normalization
                    // leaves untouched roots at declared.
                    : promoteRoots ? (MethodAttributes)JoinAccess((int)declared, rank) : declared;
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
            // LibCpp2IL's metadata-usage casts throw plain Exception on damaged
            // vtables, so a narrower filter cannot isolate them; the signature
            // fallback below still finds the base the override binds to.
            catch (Exception e)
            {
                Logger.WarnNewline($"Slot-based override resolution failed for {method.FullName}: {e.Message}", "Member Accessibility");
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
                catch (Exception e) when (e is IndexOutOfRangeException or ArgumentOutOfRangeException)
                {
                    // A corrupted generic argument count cannot be substituted;
                    // treat the pair as not matching.
                    Logger.VerboseNewline($"Generic substitution failed while matching {method.FullName}: {e.Message}", "Member Accessibility");
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

    // Visibility a nested or top-level type must reach for a reference at the
    // given ladder rank; top-level types cannot express family access, so a
    // rank above internal lands on Public.
    private static int VisibilityRank(TypeAttributes visibility, bool nested) => nested
        ? visibility switch
        {
            TypeAttributes.NestedPrivate => 1,
            TypeAttributes.NestedFamilyAndAssembly => 2,
            TypeAttributes.NestedAssembly => 3,
            TypeAttributes.NestedFamily => 4,
            TypeAttributes.NestedFamilyOrAssembly => 5,
            _ => 6,
        }
        : visibility == TypeAttributes.Public ? 6 : 3;

    private static TypeAttributes VisibilityForRank(int rank, bool nested) => nested
        ? rank switch
        {
            <= 1 => TypeAttributes.NestedPrivate,
            2 => TypeAttributes.NestedFamilyAndAssembly,
            3 => TypeAttributes.NestedAssembly,
            4 => TypeAttributes.NestedFamily,
            5 => TypeAttributes.NestedFamilyOrAssembly,
            _ => TypeAttributes.NestedPublic,
        }
        : rank >= 4 ? TypeAttributes.Public : TypeAttributes.NotPublic;

    // A widened member must not outrank the types its signature names
    // (CS0050/CS0051/CS0052/CS0053): each emitted signature type rises to the
    // member's new access, stopping where it already meets it. Frozen runtime
    // surfaces and placeholders without an emitted TypeDefinition keep their
    // declared shape.
    private static void EnsureSignatureTypesAccessible(int accessRank, MethodAnalysisContext member)
    {
        foreach (var parameter in member.Parameters)
            EnsureSignatureTypesAccessible(accessRank, parameter.ParameterType);
        EnsureSignatureTypesAccessible(accessRank, member.ReturnType);
    }

    private static void EnsureSignatureTypesAccessible(int accessRank, TypeAnalysisContext? type)
    {
        if (accessRank <= 1)
            return; // a private member is consistent with whatever scope it names
        var visited = new Dictionary<TypeDefinition, int>();
        foreach (var leaf in SignatureLeaves(type))
        {
            if (leaf.GetExtraData<TypeDefinition>("AsmResolverType") is not { } emitted
                || AccessibilityExtensions.IsExternalRuntimeAssembly(leaf.DeclaringAssembly?.Name))
                continue;
            WidenTypeAndAncestors(emitted, accessRank, visited);
        }
    }

    // Widening a signature type must also satisfy the type's own declaration
    // constraints (CS0060/CS0061): its base type and interfaces have to cover
    // the new access too, so the walk follows them transitively. Raising a
    // type's own visibility additionally enlarges the effective accessibility
    // of every member inside it, so each raised level re-covers its members'
    // signatures (CS0050/51/52/53). The visited map records the rank a type was
    // already covered at, so a weaker later requirement does not re-walk it
    // but a stronger one does.
    private static bool WidenTypeAndAncestors(TypeDefinition type, int requiredRank, Dictionary<TypeDefinition, int> visited)
    {
        if (visited.TryGetValue(type, out var coveredRank) && coveredRank >= requiredRank)
            return false;
        visited[type] = requiredRank;
        var changed = false;
        for (var level = type; level != null; level = level.DeclaringType)
            if (RaiseType(level, requiredRank))
            {
                changed = true;
                changed |= CoverEmittedConsistency(level, visited);
            }
        return changed;
    }

    private static bool RaiseType(TypeDefinition type, int requiredRank)
    {
        var nested = type.DeclaringType != null;
        var rank = JoinAccess(VisibilityRank(type.Attributes & TypeAttributes.VisibilityMask, nested), requiredRank);
        var next = (type.Attributes & ~TypeAttributes.VisibilityMask) | VisibilityForRank(rank, nested);
        var changed = next != type.Attributes;
        type.Attributes = next;
        return changed;
    }

    // The accessibility a recompiled type actually presents: its own emitted
    // visibility bounded by every enclosing type's, the "accessibility domain"
    // the C# spec intersects for consistency checks.
    private static int EmittedEffectiveRank(TypeDefinition type)
    {
        var rank = 6;
        for (var current = type; current != null; current = current.DeclaringType)
            rank = Math.Min(rank, VisibilityRank(
                current.Attributes & TypeAttributes.VisibilityMask, current.DeclaringType != null));
        return rank;
    }

    // Re-asserts the consistency constraints a raised type's new effective
    // accessibility imposes: its base type and - for interfaces - its base
    // interfaces must cover it (CS0060/CS0061), and every member whose access
    // exceeded the old domain now exposes its signature types at the new one
    // (CS0050/51/52/53). Signature types reachable only through an unresolved
    // TypeReference are left for the post-build pass.
    private static bool CoverEmittedConsistency(TypeDefinition type, Dictionary<TypeDefinition, int> visited)
    {
        var effectiveRank = EmittedEffectiveRank(type);
        var changed = false;
        if (AsTypeDefinition(type.BaseType) is { } baseType)
            changed |= WidenTypeAndAncestors(baseType, effectiveRank, visited);
        if (type.IsInterface)
            foreach (var @interface in type.Interfaces)
                if (AsTypeDefinition(@interface.Interface) is { } interfaceType)
                    changed |= WidenTypeAndAncestors(interfaceType, effectiveRank, visited);

        foreach (var method in type.Methods)
            changed |= CoverEmittedSignature(
                Math.Min((int)(method.Attributes & MethodAttributes.MemberAccessMask), effectiveRank),
                MethodLeaves(method.Signature), visited);
        foreach (var field in type.Fields)
            changed |= CoverEmittedSignature(
                Math.Min((int)(field.Attributes & FieldAttributes.FieldAccessMask), effectiveRank),
                EmittedSignatureLeaves(field.Signature?.FieldType), visited);

        foreach (var nested in type.NestedTypes)
            changed |= CoverEmittedConsistency(nested, visited);
        return changed;
    }

    private static bool CoverEmittedSignature(int memberRank, IEnumerable<TypeDefinition> leaves,
        Dictionary<TypeDefinition, int> visited)
    {
        if (memberRank <= 1)
            return false;
        var changed = false;
        foreach (var leaf in leaves)
            changed |= WidenTypeAndAncestors(leaf, memberRank, visited);
        return changed;
    }

    private static IEnumerable<TypeDefinition> MethodLeaves(MethodSignature? signature)
    {
        if (signature is null)
            yield break;
        foreach (var leaf in EmittedSignatureLeaves(signature.ReturnType))
            yield return leaf;
        foreach (var parameter in signature.ParameterTypes)
            foreach (var leaf in EmittedSignatureLeaves(parameter))
                yield return leaf;
    }

    // The emitted TypeDefinitions a signature names in its own module: generic
    // definitions and arguments, and the elements of wrapped types. Cross-module
    // TypeReference leaves cannot be resolved while assemblies are still being
    // built and are covered by FixupEmittedVisibility instead.
    private static IEnumerable<TypeDefinition> EmittedSignatureLeaves(TypeSignature? signature)
    {
        switch (signature)
        {
            case null:
            case GenericParameterSignature:
                break;
            case GenericInstanceTypeSignature generic:
                foreach (var leaf in EmittedLeaf(generic.GenericType))
                    yield return leaf;
                foreach (var argument in generic.TypeArguments)
                    foreach (var leaf in EmittedSignatureLeaves(argument))
                        yield return leaf;
                break;
            case TypeDefOrRefSignature typeDefOrRef:
                foreach (var leaf in EmittedLeaf(typeDefOrRef.Type))
                    yield return leaf;
                break;
            case TypeSpecificationSignature specification:
                foreach (var leaf in EmittedSignatureLeaves(specification.BaseType))
                    yield return leaf;
                break;
        }
    }

    private static IEnumerable<TypeDefinition> EmittedLeaf(ITypeDefOrRef? type)
    {
        switch (type)
        {
            case TypeDefinition definition:
                yield return definition;
                break;
            case TypeSpecification specification:
                foreach (var leaf in EmittedSignatureLeaves(specification.Signature))
                    yield return leaf;
                break;
        }
    }

    /// <summary>
    /// Post-build pass over the emitted assemblies restoring the visibility
    /// consistency C# demands (CS0050/51/52/53, CS0060/61). A member can end up
    /// more visible than a type in its signature when its containing type
    /// widened after the member did - the signature walk in
    /// <see cref="EnsureAccessible(MethodDefinition, MethodAnalysisContext)"/>
    /// only fires when the member's own access changes - and a widened type can
    /// outrank its base type. Here every emitted member's effective
    /// accessibility (its access bounded by the enclosing types') is covered by
    /// the emitted accessibility of each type its signature names, and every
    /// emitted type's base and interfaces cover the type's own effective
    /// accessibility. Widening is monotone and bounded, so the pass runs to a
    /// fixpoint.
    /// </summary>
    internal static void FixupEmittedVisibility(ApplicationAnalysisContext appContext)
    {
        for (var pass = 0; pass < 8; pass++)
        {
            var changed = false;
            foreach (var type in appContext.AllTypes)
            {
                if (type.GetExtraData<TypeDefinition>("AsmResolverType") is not { } emitted
                    || AccessibilityExtensions.IsExternalRuntimeAssembly(type.DeclaringAssembly?.Name))
                    continue;

                var typeRank = EmittedEffectiveRank(emitted);
                if (typeRank <= 1)
                    continue;

                if (AsTypeDefinition(emitted.BaseType) is { } baseType)
                    changed |= WidenTypeAndAncestors(baseType, typeRank, []);
                if (emitted.IsInterface)
                    foreach (var @interface in emitted.Interfaces)
                        if (AsTypeDefinition(@interface.Interface) is { } interfaceType)
                            changed |= WidenTypeAndAncestors(interfaceType, typeRank, []);

                foreach (var member in type.Methods)
                    if (member.GetExtraData<MethodDefinition>("AsmResolverMethod") is { } emittedMember)
                        changed |= CoverSignatureTypes(
                            Math.Min((int)(emittedMember.Attributes & MethodAttributes.MemberAccessMask), typeRank),
                            SignatureLeaves(member.Parameters.Select(p => p.ParameterType)
                                .Append(member.ReturnType)));

                foreach (var field in type.Fields)
                    if (field.GetExtraData<FieldDefinition>("AsmResolverField") is { } emittedField)
                        changed |= CoverSignatureTypes(
                            Math.Min((int)(emittedField.Attributes & FieldAttributes.FieldAccessMask), typeRank),
                            SignatureLeaves(field.FieldType));
            }
            if (!changed)
                return;
        }
    }

    private static bool CoverSignatureTypes(int memberRank, IEnumerable<TypeAnalysisContext> leaves)
    {
        if (memberRank <= 1)
            return false;
        var changed = false;
        foreach (var leaf in leaves)
        {
            if (leaf.GetExtraData<TypeDefinition>("AsmResolverType") is not { } emitted
                || AccessibilityExtensions.IsExternalRuntimeAssembly(leaf.DeclaringAssembly?.Name))
                continue;
            changed |= WidenTypeAndAncestors(emitted, memberRank, []);
        }
        return changed;
    }

    private static IEnumerable<TypeAnalysisContext> SignatureLeaves(IEnumerable<TypeAnalysisContext> types)
    {
        foreach (var type in types)
            foreach (var leaf in SignatureLeaves(type))
                yield return leaf;
    }

    private static TypeDefinition? AsTypeDefinition(ITypeDefOrRef? type) => type switch
    {
        TypeDefinition definition => definition,
        TypeSpecification { Signature: GenericInstanceTypeSignature generic } => generic.GenericType as TypeDefinition,
        _ => null,
    };

    // The metadata types a signature can actually name: the generic definition
    // and every argument of an instantiation, the element of a wrapped type,
    // and the enclosing type of a nested one. Generic parameters and runtime
    // placeholders never reach a metadata token.
    private static IEnumerable<TypeAnalysisContext> SignatureLeaves(TypeAnalysisContext? type)
    {
        switch (type)
        {
            case null:
            case GenericParameterTypeAnalysisContext or SentinelTypeAnalysisContext
                or RuntimeClassTypeAnalysisContext or RuntimeMethodInfoAnalysisContext
                or RuntimeFieldInfoAnalysisContext or StaticFieldStorageTypeAnalysisContext
                or RgctxTableTypeAnalysisContext or MethodRgctxTableTypeAnalysisContext:
                break;
            case GenericInstanceTypeAnalysisContext instance:
                foreach (var leaf in SignatureLeaves(instance.GenericType))
                    yield return leaf;
                foreach (var leaf in SignatureLeaves(instance.DeclaringType))
                    yield return leaf;
                foreach (var argument in instance.GenericArguments)
                    foreach (var leaf in SignatureLeaves(argument))
                        yield return leaf;
                break;
            case WrappedTypeAnalysisContext wrapped:
                foreach (var leaf in SignatureLeaves(wrapped.ElementType))
                    yield return leaf;
                break;
            default:
                yield return type;
                break;
        }
    }
}
