using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// IL2CPP inlines the fast paths of BCL members and keeps the slow path as a direct call to a
/// corlib member managed code could never name (the internal <c>List&lt;T&gt;.AddWithResize</c>
/// behind an inlined <c>Add</c>, the private <c>Math.ThrowMinMaxException&lt;T&gt;</c> behind an
/// inlined clamp). Shared-generic method references can also be instantiated over non-public
/// corlib marker types such as <c>System.ByteEnum</c>. These callees reach the emitted assembly
/// as member references that keep their declared accessibility, so the verifier rejects them;
/// this helper recognizes when a callee is genuinely invisible and offers the honest public
/// equivalent when one exists.
/// </summary>
internal static class InaccessibleCalleeRecovery
{
    /// <summary>
    /// Whether <paramref name="callee"/> may be named by a call emitted into
    /// <paramref name="caller"/>'s body.
    /// </summary>
    /// <remarks>
    /// Non-generic callees resolve to their emitted <see cref="AsmResolver.DotNet.MethodDefinition"/>,
    /// which <see cref="Utils.AsmResolver.MemberAccessibility"/> relaxes to public along with the
    /// declaring-type chain, so member and declaring-type access are never the blocker for them.
    /// Member references built for concrete generic methods keep the declared accessibility, and
    /// no emission path relaxes a signature: every callee - generic or not - is nameable only when
    /// its parameter and return types are all visible to the caller.
    /// </remarks>
    internal static bool IsVisibleFrom(MethodAnalysisContext callee, MethodAnalysisContext caller)
    {
        var callerType = caller.DeclaringType;
        if (callerType is null)
            return true; // no metadata basis to judge the access

        var concrete = callee as ConcreteGenericMethodAnalysisContext;
        var declaring = concrete?.BaseMethodContext.DeclaringType ?? callee.DeclaringType;
        var keepsDeclaredAccessibility = concrete != null
            || Extensions.AccessibilityExtensions.IsExternalRuntimeAssembly(declaring?.DeclaringAssembly?.Name);
        if (keepsDeclaredAccessibility && declaring is not null)
        {
            var sameAssembly = ReferenceEquals(callerType.DeclaringAssembly, declaring.DeclaringAssembly)
                || Extensions.AccessibilityExtensions.SharesEmittedInternals(callerType.DeclaringAssembly, declaring.DeclaringAssembly);
            var memberVisible = (callee.Attributes & MethodAttributes.MemberAccessMask) switch
            {
                MethodAttributes.Public => true,
                MethodAttributes.Private => IsWithinOrSame(callerType, declaring) || IsWithinOrSame(declaring, callerType),
                MethodAttributes.Assembly => sameAssembly,
                MethodAttributes.Family => IsWithinOrSame(callerType, declaring) || callerType.IsAssignableTo(declaring),
                MethodAttributes.FamANDAssem => sameAssembly && (IsWithinOrSame(callerType, declaring) || callerType.IsAssignableTo(declaring)),
                MethodAttributes.FamORAssem => sameAssembly || IsWithinOrSame(callerType, declaring) || callerType.IsAssignableTo(declaring),
                _ => false,
            };
            if (!memberVisible)
                return false;
        }

        if (concrete != null)
        {
            // The emitted member reference names the constructed declaring type and the
            // method's generic arguments verbatim: every type argument must be visible.
            if (!IsVisibleType(concrete.DeclaringType, callerType)
                || !concrete.MethodGenericParameters.All(parameter => IsVisibleType(parameter, callerType)))
                return false;
        }

        // Member signatures are never relaxed: a callee is nameable only when every
        // parameter type and the return type are visible to the caller.
        foreach (var parameter in callee.Parameters)
            if (!IsVisibleType(parameter.ParameterType, callerType))
                return false;
        return IsVisibleType(callee.ReturnType, callerType);
    }

    /// <summary>
    /// Whether every generic argument the concrete callee carries satisfies the
    /// constraint its open declaration declares. An erased shared-generic
    /// argument (object) can leave an instantiation no honest type fulfils -
    /// such a call cannot be named at all and must be stubbed.
    /// </summary>
    internal static bool SatisfiesDeclaredConstraints(MethodAnalysisContext callee)
    {
        if (callee is not ConcreteGenericMethodAnalysisContext concrete)
            return true;

        var typeArguments = concrete.TypeGenericParameters;
        var methodArguments = concrete.MethodGenericParameters;
        var baseDeclaring = concrete.BaseMethodContext.DeclaringType;
        if (baseDeclaring != null)
            for (var i = 0; i < baseDeclaring.GenericParameters.Count && i < typeArguments.Count; i++)
                if (!Utils.AsmResolver.ContextToMethodDescriptor.SatisfiesConstraints(
                        typeArguments[i], baseDeclaring.GenericParameters[i], typeArguments, methodArguments))
                    return false;

        var genericParameters = concrete.BaseMethodContext.GenericParameters;
        for (var i = 0; i < genericParameters.Count && i < methodArguments.Count; i++)
            if (!Utils.AsmResolver.ContextToMethodDescriptor.SatisfiesConstraints(
                    methodArguments[i], genericParameters[i], typeArguments, methodArguments))
                return false;

        return true;
    }

    /// <summary>
    /// The honest public callee for a corlib-internal helper, if one performs the same operation.
    /// <c>List&lt;T&gt;.AddWithResize</c> is the slow path of <c>List&lt;T&gt;.Add</c> — IL2CPP
    /// inlines the capacity check and leaves a direct call to it, so <c>Add</c> is the faithful
    /// substitute on the same instantiation.
    /// </summary>
    internal static MethodAnalysisContext? TrySubstitute(MethodAnalysisContext callee)
    {
        if (callee is ConcreteGenericMethodAnalysisContext { Name: "AddWithResize", Parameters.Count: 1 } concrete
            && concrete.BaseMethodContext.DeclaringType is { DefaultFullName: "System.Collections.Generic.List`1" } listDefinition
            && listDefinition.GenericParameters.Count == concrete.TypeGenericParameters.Count
            && listDefinition.Methods.FirstOrDefault(m => m.Name == "Add" && !m.IsStatic && m.Parameters.Count == 1
                && (m.Attributes & MethodAttributes.MemberAccessMask) == MethodAttributes.Public) is { } add)
        {
            return new ConcreteGenericMethodAnalysisContext(add, concrete.TypeGenericParameters, []);
        }

        return null;
    }

    /// <summary>
    /// Whether <paramref name="type"/> may be named in a token emitted into
    /// <paramref name="callerType"/>'s assembly. Type references keep their declared
    /// accessibility in the emitted assembly, so a shared-generic instantiation over a
    /// corlib-internal marker (e.g. <c>List&lt;System.Int32Enum&gt;</c>) is a reference the
    /// verifier rejects even though the metadata exists. The check recurses through
    /// everything the token spells out: the generic definition, every type argument, the
    /// enclosing instantiation of a nested type, and the element of a wrapped type.
    /// </summary>
    internal static bool IsVisibleType(TypeAnalysisContext? type, TypeAnalysisContext callerType)
    {
        return type switch
        {
            null => true,
            GenericInstanceTypeAnalysisContext instance => IsVisibleType(instance.GenericType, callerType)
                && instance.GenericArguments.All(argument => IsVisibleType(argument, callerType))
                && IsVisibleType(instance.DeclaringType, callerType),
            WrappedTypeAnalysisContext wrapped => IsVisibleType(wrapped.ElementType, callerType),
            // Generic parameters resolve in the caller's own generic context; the runtime
            // handle/rgctx placeholders never reach a metadata token at all.
            GenericParameterTypeAnalysisContext or SentinelTypeAnalysisContext
                or RuntimeClassTypeAnalysisContext or RuntimeMethodInfoAnalysisContext
                or RuntimeFieldInfoAnalysisContext or StaticFieldStorageTypeAnalysisContext
                or RgctxTableTypeAnalysisContext or MethodRgctxTableTypeAnalysisContext => true,
            _ => type.DeclaringAssembly is null || type.IsAccessibleTo(callerType),
        };
    }

    private static bool IsWithinOrSame(TypeAnalysisContext candidate, TypeAnalysisContext declaring)
    {
        for (var current = candidate; current != null; current = current.DeclaringType)
            if (ReferenceEquals(current, declaring))
                return true;

        return false;
    }
}
