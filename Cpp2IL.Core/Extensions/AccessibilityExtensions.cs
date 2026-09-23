using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.Metadata;

namespace Cpp2IL.Core.Extensions;

internal static class AccessibilityExtensions
{
    /// <summary>
    /// Set by the il-recovery output format while assemblies are being emitted:
    /// every generated assembly carries InternalsVisibleTo to its siblings
    /// (il2cpp dropped the original attributes), so emission-time access gates
    /// answer for the friend scope that will actually exist in the output.
    /// Analysis-time callers leave it unset and keep the raw metadata answer.
    /// </summary>
    internal static bool EmittedInternalsAreShared;

    public static bool IsAccessibleTo(this TypeAnalysisContext referenceType, TypeAnalysisContext referencingType)
    {
        if (referenceType == referencingType)
            return true;

        var declaringTypesHierarchy = referenceType.GetTypeAndDeclaringTypes().ToArray();
        var referencingNesting = referencingType.GetTypeAndDeclaringTypes().ToArray();
        var sameAssembly = referenceType.DeclaringAssembly == referencingType.DeclaringAssembly
            || SharesEmittedInternals(referenceType.DeclaringAssembly, referencingType.DeclaringAssembly);
        if (!sameAssembly
            && !referenceType.DeclaringAssembly.IsDependencyOf(referencingType.DeclaringAssembly))
        {
            return false;
        }

        for (var i = 0; i < declaringTypesHierarchy.Length; i++)
        {
            var current = declaringTypesHierarchy[i];
            var parent = i + 1 < declaringTypesHierarchy.Length ? declaringTypesHierarchy[i + 1] : null;
            // A type nested inside the member's declaring type is in its friend nest:
            // it sees the parent's private members, which includes the nested type itself.
            var withinParent = parent != null && referencingNesting.Contains(parent);
            var familyToParent = parent != null && (withinParent || referencingType.IsAssignableTo(parent));
            var visible = parent == null
                ? sameAssembly || current.Visibility is not TypeAttributes.NotPublic
                : sameAssembly
                    ? current.Visibility switch
                    {
                        TypeAttributes.NestedPrivate => withinParent,
                        TypeAttributes.NestedFamily or TypeAttributes.NestedFamANDAssem => familyToParent,
                        _ => true,
                    }
                    : current.Visibility switch
                    {
                        TypeAttributes.NestedPublic => true,
                        TypeAttributes.NestedFamily or TypeAttributes.NestedFamORAssem => referencingType.IsAssignableTo(parent),
                        _ => false,
                    };
            if (!visible)
                return false;
        }

        return true;
    }

    public static bool IsAssignableTo(this TypeAnalysisContext derivedType, TypeAnalysisContext baseType)
    {
        if (baseType.IsInterface)
        {
            return derivedType.IsAssignableToInterface(baseType);
        }
        else
        {
            return derivedType.InheritsFrom(baseType);
        }
    }

    private static int IndexOf<T>(this IEnumerable<T> enumerable, Func<T, bool> selector)
    {
        var index = 0;
        foreach (var item in enumerable)
        {
            if (selector(item))
            {
                return index;
            }

            index++;
        }

        return -1;
    }

    private static IEnumerable<TypeAnalysisContext> GetTypeAndDeclaringTypes(this TypeAnalysisContext type)
    {
        var current = type;
        while (current != null)
        {
            yield return current;
            current = current.DeclaringType;
        }
    }

    private static bool InheritsFrom(this TypeAnalysisContext derivedType, TypeAnalysisContext baseType)
    {
        var current = derivedType;
        while (current != null)
        {
            if (current == baseType)
                return true;
            current = current.BaseType;
        }

        return false;
    }

    private static bool IsAssignableToInterface(this TypeAnalysisContext derivedType, TypeAnalysisContext baseInterface)
    {
        if (derivedType == baseInterface)
            return true;

        foreach (var @interface in derivedType.InterfaceContexts)
        {
            if (@interface.IsAssignableToInterface(baseInterface))
                return true;
        }

        return false;
    }

    /// <summary>
    /// Whether two assemblies share internal scope in emitted output: same
    /// assembly, or two real metadata assemblies, since every generated
    /// assembly carries InternalsVisibleTo to its siblings (il2cpp dropped the
    /// original attributes). Covers `internal` and the Assem half of
    /// FamANDAssem/FamORAssem; private members never cross the boundary.
    /// </summary>
    internal static bool SharesEmittedInternals(AssemblyAnalysisContext? a, AssemblyAnalysisContext? b) =>
        ReferenceEquals(a, b)
        || (a != null && b != null && (a.Name == b.Name
            || (EmittedInternalsAreShared && a.Definition != null && b.Definition != null)));

    private static bool IsDependencyOf(this AssemblyAnalysisContext referencedAssembly, AssemblyAnalysisContext referencingAssembly)
    {
        if (referencingAssembly.Definition is null)
        {
            // Injected assemblies can access everything
            return true;
        }
        if (referencedAssembly.Definition is null)
        {
            // Injected assemblies cannot be accessed by metadata assemblies
            return false;
        }
        return referencedAssembly.Definition.IsDependencyOf(referencingAssembly.Definition);
    }

    private static bool IsDependencyOf(this Il2CppAssemblyDefinition referencedAssembly, Il2CppAssemblyDefinition referencingAssembly)
    {
        if (Array.IndexOf(referencingAssembly.ReferencedAssemblies, referencedAssembly) >= 0)
            return true;

        if (Array.IndexOf(referencedAssembly.ReferencedAssemblies, referencingAssembly) >= 0)
            return false;

        return referencingAssembly.CollectAllDependencies().Contains(referencedAssembly);
    }

    private static HashSet<Il2CppAssemblyDefinition> CollectAllDependencies(this Il2CppAssemblyDefinition referencingAssembly)
    {
        var dependencies = new HashSet<Il2CppAssemblyDefinition> { referencingAssembly };
        referencingAssembly.CollectAllDependencies(dependencies);
        return dependencies;
    }

    private static void CollectAllDependencies(this Il2CppAssemblyDefinition referencingAssembly, HashSet<Il2CppAssemblyDefinition> dependencies)
    {
        foreach (var dependency in referencingAssembly.ReferencedAssemblies)
        {
            //Assemblies can have circular references
            if (dependencies.Add(dependency))
            {
                dependency.CollectAllDependencies(dependencies);
            }
        }
    }
}
