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
    /// which <see cref="Utils.AsmResolver.MemberAccessibility"/> relaxes to public at emission time.
    /// Only member references built for concrete generic methods reach the verifier with the
    /// declared accessibility intact, so only they need this check.
    /// </remarks>
    internal static bool IsVisibleFrom(MethodAnalysisContext callee, MethodAnalysisContext caller)
    {
        if (callee is not ConcreteGenericMethodAnalysisContext concrete)
            return true;

        var declaring = concrete.BaseMethodContext.DeclaringType;
        var callerType = caller.DeclaringType;
        if (declaring is null || callerType is null)
            return true; // no metadata basis to judge the access

        var sameAssembly = ReferenceEquals(callerType.DeclaringAssembly, declaring.DeclaringAssembly);
        var memberVisible = (callee.Attributes & MethodAttributes.MemberAccessMask) switch
        {
            MethodAttributes.Public => true,
            // Private members are visible to the declaring type itself, to anything nested
            // inside it, and to the enclosing type of a nested declaration.
            MethodAttributes.Private => IsWithinOrSame(callerType, declaring) || IsWithinOrSame(declaring, callerType),
            MethodAttributes.Assembly => sameAssembly,
            MethodAttributes.Family => IsWithinOrSame(callerType, declaring) || callerType.IsAssignableTo(declaring),
            MethodAttributes.FamANDAssem => sameAssembly && (IsWithinOrSame(callerType, declaring) || callerType.IsAssignableTo(declaring)),
            MethodAttributes.FamORAssem => sameAssembly || IsWithinOrSame(callerType, declaring) || callerType.IsAssignableTo(declaring),
            _ => false,
        };

        return memberVisible && IsVisibleType(concrete.DeclaringType, callerType);
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

    private static bool IsVisibleType(TypeAnalysisContext? type, TypeAnalysisContext callerType)
    {
        return type switch
        {
            null => true,
            // A constructed type is only as visible as its definition and its type arguments.
            GenericInstanceTypeAnalysisContext instance => IsVisibleType(instance.GenericType, callerType)
                && instance.GenericArguments.All(argument => IsVisibleType(argument, callerType)),
            WrappedTypeAnalysisContext wrapped => IsVisibleType(wrapped.ElementType, callerType),
            GenericParameterTypeAnalysisContext => true,
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
