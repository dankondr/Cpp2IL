using System;
using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;

namespace Cpp2IL.Core.Utils.AsmResolver;

/// <summary>
/// Custom-attribute blobs write typeof() argument values and enum member types
/// as assembly-qualified name strings. Unlike a TypeRef row, that never
/// registers the named assembly in the module's AssemblyRef table, so a module
/// whose only mention of an assembly lives inside an attribute blob ends up
/// with a dangling type name that decompilers and compilers cannot resolve.
/// This pass runs right before serialization and adds an AssemblyRef row for
/// every emitted assembly that an attribute signature names.
/// </summary>
internal static class AssemblyReferenceClosure
{
    public static int Ensure(List<AssemblyDefinition> assemblies)
    {
        var emitted = new Dictionary<string, AssemblyDefinition>(StringComparer.Ordinal);
        foreach (var assembly in assemblies)
        {
            if (assembly.Name is { } name)
                emitted.TryAdd(name.ToString(), assembly);
        }

        var added = 0;
        foreach (var assembly in assemblies)
        {
            if (assembly.Name is not { } self || assembly.ManifestModule is not { } module)
                continue;

            var declared = new HashSet<string>(StringComparer.Ordinal);
            foreach (var reference in module.AssemblyReferences)
            {
                if (reference.Name is { } referenceName)
                    declared.Add(referenceName.ToString());
            }

            var needed = new SortedSet<string>(StringComparer.Ordinal);
            foreach (var attribute in EnumerateAttributes(assembly))
            {
                if (attribute.Signature is not { } signature)
                    continue;

                foreach (var argument in signature.FixedArguments)
                    CollectArgument(argument, needed);
                foreach (var member in signature.NamedArguments)
                {
                    CollectSignature(member.ArgumentType, needed);
                    CollectArgument(member.Argument, needed);
                }
            }

            foreach (var name in needed)
            {
                if (name == self.ToString() || !declared.Add(name) || !emitted.TryGetValue(name, out var target))
                    continue;

                // Rows are only emitted for references that own a table entry
                // or are used by a coded index, so the new reference also needs
                // a pre-assigned token (imported under PreserveAssemblyReferenceIndices).
                var reference = target.ToAssemblyReference();
                module.AssemblyReferences.Add(reference);
                module.TokenAllocator.AssignNextAvailableToken(reference);
                added++;
            }
        }

        return added;
    }

    private static IEnumerable<CustomAttribute> EnumerateAttributes(AssemblyDefinition assembly)
    {
        if (assembly.ManifestModule is not { } module)
            yield break;

        var allTypes = module.GetAllTypes().ToList();

        foreach (var attribute in assembly.CustomAttributes)
            yield return attribute;
        foreach (var attribute in module.CustomAttributes)
            yield return attribute;

        foreach (var type in allTypes)
        {
            foreach (var attribute in type.CustomAttributes)
                yield return attribute;
            foreach (var genericParameter in type.GenericParameters)
            {
                foreach (var attribute in genericParameter.CustomAttributes)
                    yield return attribute;
            }
        }

        foreach (var field in allTypes.SelectMany(t => t.Fields))
        {
            foreach (var attribute in field.CustomAttributes)
                yield return attribute;
        }

        foreach (var method in allTypes.SelectMany(t => t.Methods))
        {
            foreach (var attribute in method.CustomAttributes)
                yield return attribute;
            foreach (var genericParameter in method.GenericParameters)
            {
                foreach (var attribute in genericParameter.CustomAttributes)
                    yield return attribute;
            }
            foreach (var parameter in method.ParameterDefinitions)
            {
                foreach (var attribute in parameter.CustomAttributes)
                    yield return attribute;
            }
        }

        foreach (var property in allTypes.SelectMany(t => t.Properties))
        {
            foreach (var attribute in property.CustomAttributes)
                yield return attribute;
        }

        foreach (var @event in allTypes.SelectMany(t => t.Events))
        {
            foreach (var attribute in @event.CustomAttributes)
                yield return attribute;
        }
    }

    private static void CollectArgument(CustomAttributeArgument argument, ISet<string> names)
    {
        CollectSignature(argument.ArgumentType, names);
        CollectValue(argument.Element, names);

        if (argument.Elements is { } elements)
        {
            foreach (var element in elements)
                CollectValue(element, names);
        }
    }

    private static void CollectValue(object? value, ISet<string> names)
    {
        switch (value)
        {
            case TypeSignature signature:
                CollectSignature(signature, names);
                break;
            case BoxedArgument boxed:
                CollectSignature(boxed.Type, names);
                CollectValue(boxed.Value, names);
                break;
            case CustomAttributeArgument nested:
                CollectArgument(nested, names);
                break;
            case IEnumerable<object?> sequence:
                foreach (var element in sequence)
                    CollectValue(element, names);
                break;
        }
    }

    private static void CollectSignature(TypeSignature? signature, ISet<string> names)
    {
        switch (signature)
        {
            case null:
                break;
            case TypeDefOrRefSignature typeDefOrRef:
                AddOwningAssembly(typeDefOrRef.Type, names);
                break;
            case GenericInstanceTypeSignature genericInstance:
                AddOwningAssembly(genericInstance.GenericType, names);
                foreach (var argument in genericInstance.TypeArguments)
                    CollectSignature(argument, names);
                break;
            case TypeSpecificationSignature specification:
                CollectSignature(specification.BaseType, names);
                break;
            case FunctionPointerTypeSignature functionPointer:
                if (functionPointer.Signature is { } methodSignature)
                {
                    CollectSignature(methodSignature.ReturnType, names);
                    foreach (var parameterType in methodSignature.ParameterTypes)
                        CollectSignature(parameterType, names);
                }
                break;
        }
    }

    private static void AddOwningAssembly(ITypeDefOrRef? type, ISet<string> names)
    {
        while (type is not null)
        {
            switch (type)
            {
                case TypeDefinition definition:
                    if (definition.DeclaringModule?.Assembly?.Name is { } definitionAssembly)
                        names.Add(definitionAssembly.ToString());
                    return;
                case TypeReference reference:
                    switch (reference.Scope)
                    {
                        case AssemblyReference { Name: { } assemblyName }:
                            names.Add(assemblyName.ToString());
                            return;
                        case ModuleDefinition { Assembly.Name: { } moduleAssembly }:
                            names.Add(moduleAssembly.ToString());
                            return;
                        case TypeReference declaringType:
                            type = declaringType;
                            continue;
                    }
                    return;
                default:
                    return;
            }
        }
    }
}
