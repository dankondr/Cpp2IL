using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
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
            // Context objects for the same metadata type are not guaranteed
            // identical (generic instances are rebuilt on demand), so compare
            // the full name which carries the instantiation arguments too.
            if (current == baseType
                || current is not GenericParameterTypeAnalysisContext
                && baseType is not GenericParameterTypeAnalysisContext
                && current.FullName == baseType.FullName
                // B<int> is-a B: an instantiation's own definition is its base
                // even though the instantiating FullName never equals it.
                || current is GenericInstanceTypeAnalysisContext { GenericType: { } currentDefinition }
                && baseType is not GenericParameterTypeAnalysisContext
                && (currentDefinition == baseType || currentDefinition.FullName == baseType.FullName))
                return true;
            // A generic instance's own BaseType can stay unresolved (built
            // before the definition's base was), so continue the walk through
            // the open definition's base. That base still mentions the
            // definition's parameters (`ModProcessorBase<T>`), so it is bound
            // through the instance's arguments first - same as the interface
            // walk below.
            var next = current.BaseType
                ?? (current as GenericInstanceTypeAnalysisContext)?.GenericType.BaseType;
            if (next != null && current is GenericInstanceTypeAnalysisContext instance)
            {
                try
                {
                    next = GenericInstantiation.Instantiate(next, instance.GenericArguments, []);
                }
                catch
                {
                    // malformed base instantiations keep the open form.
                }
            }
            current = next;
        }

        return false;
    }

    private static bool IsAssignableToInterface(this TypeAnalysisContext derivedType, TypeAnalysisContext baseInterface)
    {
        // Interface contexts are not reference-unique either, and an interface
        // instance (`IEnumerable<int>`) only equals an identical instantiation -
        // the open definition or different arguments must not match it. Generic
        // parameters are excluded: unrelated `T`s share the same name.
        if (derivedType == baseInterface
            || derivedType is not GenericParameterTypeAnalysisContext
            && baseInterface is not GenericParameterTypeAnalysisContext
            && derivedType.FullName == baseInterface.FullName)
            return true;
        if (baseInterface is not GenericInstanceTypeAnalysisContext
            && derivedType is GenericInstanceTypeAnalysisContext { GenericType: { } interfaceDefinition }
            && interfaceDefinition.FullName == baseInterface.FullName)
            return true;

        // Generic instances carry no interface list of their own; the set is a
        // property of the generic definition, whose entries still mention its
        // parameters - `List<int>` implements `IEnumerable<T>`, so the entries
        // are instantiated with the instance's arguments.
        var interfaces = derivedType.InterfaceContexts;
        if (derivedType is GenericInstanceTypeAnalysisContext instance)
        {
            if (interfaces.Count == 0)
                interfaces = instance.GenericType.InterfaceContexts;
            interfaces = interfaces.Select(i =>
            {
                try
                {
                    return GenericInstantiation.Instantiate(i, instance.GenericArguments, []);
                }
                catch
                {
                    return i;
                }
            }).ToList();
        }

        foreach (var @interface in interfaces)
        {
            if (@interface.IsAssignableToInterface(baseInterface))
                return true;
        }

        // Interfaces are inherited: a type satisfies the interface its base
        // class implements even when its own list does not repeat it. For a
        // generic instance the base still mentions the definition's parameters,
        // so it is instantiated with the instance's arguments first.
        var baseType = derivedType.BaseType
            ?? (derivedType as GenericInstanceTypeAnalysisContext)?.GenericType.BaseType;
        if (baseType != null && derivedType is GenericInstanceTypeAnalysisContext baseInstance)
        {
            try
            {
                baseType = GenericInstantiation.Instantiate(baseType, baseInstance.GenericArguments, []);
            }
            catch
            {
                // malformed base instantiations keep the open form.
            }
        }
        return baseType != null && baseType.IsAssignableToInterface(baseInterface);
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
