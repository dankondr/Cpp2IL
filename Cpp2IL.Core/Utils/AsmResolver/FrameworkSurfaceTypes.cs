using System;
using System.Collections.Generic;
using System.Linq;
using AsmResolver;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
namespace Cpp2IL.Core.Utils.AsmResolver;

/// <summary>
/// il2cpp metadata keeps several BCL types only as encodings on other members:
/// method implflags ([MethodImpl]/[PreserveSig]), type layout and charset flags
/// ([StructLayout]), indexer property names ([IndexerName]), the assembly version
/// ([assembly: AssemblyVersion]), field flags ([NonSerialized], [FieldOffset])
/// and pinvoke maps ([DllImport]). Decompilers render those surfaces back as
/// attributes, so the emitted corlib must carry the corresponding TypeDefs even
/// when il2cpp never preserved the types themselves. Custom attributes emitted
/// by the pipeline can likewise reference (via constructor, argument type or
/// typeof-value) a framework type that no output assembly defines.
///
/// This pass runs once all populated data has landed on the emitted modules and
/// materializes exactly the missing typedefs: real member shapes for the known
/// BCL attribute/enum surface, minimal mirror shapes (declaring type, matching
/// constructor, named members) for other referenced-but-absent types.
/// </summary>
internal static class FrameworkSurfaceTypes
{
    [Flags]
    private enum Surface
    {
        MethodImpl = 1,
        PreserveSig = 1 << 1,
        StructLayout = 1 << 2,
        Serializable = 1 << 3,
        ComImport = 1 << 4,
        NonSerialized = 1 << 5,
        FieldOffset = 1 << 6,
        DllImport = 1 << 7,
        IndexerName = 1 << 8,
        AssemblyVersion = 1 << 9,
    }

    /// <summary>
    /// Scans the emitted assemblies for flag/attribute surfaces referencing
    /// framework types, then emits a TypeDef for each referenced type that no
    /// emitted assembly defines. Returns the number of typedefs created.
    /// </summary>
    public static int EmitMissing(List<AssemblyDefinition> assemblies)
    {
        var corlibModule = assemblies
            .Select(a => a.ManifestModule)
            .FirstOrDefault(m => m?.Assembly?.Name == "mscorlib")
            ?? assemblies.Select(a => a.ManifestModule)
                .FirstOrDefault(m => m?.TopLevelTypes.Any(t => t.FullName == "System.Object") == true);
        if (corlibModule == null)
            return 0;

        var emittedByName = assemblies
            .Where(a => a.Name is not null && a.ManifestModule != null)
            .GroupBy(a => a.Name!.ToString(), StringComparer.Ordinal)
            .ToDictionary(g => g.Key, g => g.First(), StringComparer.Ordinal);

        var emitted = EmitFlagSurface(corlibModule, ScanFlagSurface(assemblies));
        emitted += EmitAttributeSurface(assemblies, emittedByName, corlibModule);
        return emitted;
    }

    private static Surface ScanFlagSurface(List<AssemblyDefinition> assemblies)
    {
        var needed = (Surface)0;
        foreach (var assembly in assemblies)
        {
            if (assembly.Version != null)
                needed |= Surface.AssemblyVersion;
            if (assembly.ManifestModule is not { } module)
                continue;

            foreach (var type in module.GetAllTypes())
            {
                if (type.IsModuleType)
                    continue;

                var attributes = type.Attributes;
                // Decompilers emit [StructLayout] for every value type and for
                // any type carrying explicit layout or charset information.
                if (!type.IsInterface
                    && ((attributes & TypeAttributes.LayoutMask) != TypeAttributes.AutoLayout
                        || (attributes & TypeAttributes.StringFormatMask) != TypeAttributes.AnsiClass
                        || type.ClassLayout != null
                        || (type.IsValueType && !type.IsEnum)))
                    needed |= Surface.StructLayout;
                if ((attributes & TypeAttributes.Serializable) != 0)
                    needed |= Surface.Serializable;
                if ((attributes & TypeAttributes.Import) != 0)
                    needed |= Surface.ComImport;
                if (type.IsExplicitLayout)
                    needed |= Surface.FieldOffset;

                foreach (var field in type.Fields)
                {
                    if ((field.Attributes & FieldAttributes.NotSerialized) != 0)
                        needed |= Surface.NonSerialized;
                }

                foreach (var method in type.Methods)
                {
                    var impl = method.ImplAttributes;
                    // Every implflag combination other than InternalCall and
                    // PreserveSig decompiles to a [MethodImpl(...)] attribute.
                    if ((impl & ~(MethodImplAttributes.InternalCall | MethodImplAttributes.PreserveSig)) != 0)
                        needed |= Surface.MethodImpl;
                    if ((impl & MethodImplAttributes.PreserveSig) != 0)
                        needed |= Surface.PreserveSig;
                    if (method.IsPInvokeImpl || method.ImplementationMap != null)
                        needed |= Surface.DllImport;
                }

                foreach (var property in type.Properties)
                {
                    // A parameterized property whose name is not "Item"
                    // decompiles with an [IndexerName] attribute.
                    if (property.Signature is { ParameterTypes.Count: > 0 }
                        && property.Name?.ToString() is not "Item")
                        needed |= Surface.IndexerName;
                }
            }
        }
        return needed;
    }

    private static int EmitFlagSurface(ModuleDefinition corlibModule, Surface needed)
    {
        if (needed == 0)
            return 0;

        var emitted = 0;
        var factory = corlibModule.CorLibTypeFactory;

        var attributeType = EnsureCorLibType(corlibModule, "System", "Attribute", ref emitted);
        var enumType = EnsureCorLibType(corlibModule, "System", "Enum", ref emitted);

        if (needed.HasFlag(Surface.MethodImpl))
        {
            var options = EnsureEnum(corlibModule, "System.Runtime.CompilerServices", "MethodImplOptions", enumType, ref emitted,
                ("Unmanaged", 4), ("NoInlining", 8), ("ForwardRef", 16), ("Synchronized", 32),
                ("NoOptimization", 64), ("PreserveSig", 128), ("AggressiveInlining", 256),
                ("AggressiveOptimization", 512), ("InternalCall", 4096));
            var codeType = EnsureEnum(corlibModule, "System.Runtime.CompilerServices", "MethodCodeType", enumType, ref emitted,
                ("IL", 0), ("Native", 1), ("OPTIL", 2), ("Runtime", 3));
            var attribute = EnsureType(corlibModule, "System.Runtime.CompilerServices", "MethodImplAttribute",
                TypeAttributes.Public | TypeAttributes.Class, attributeType, ref emitted);
            var valueField = EnsureField(attribute, "_val", options.ToTypeSignature(), FieldAttributes.Private);
            EnsureField(attribute, "MethodCodeType", codeType.ToTypeSignature(), FieldAttributes.Public);
            EnsureProperty(attribute, "Value", options.ToTypeSignature(), valueField, true);
            EnsureCtor(attribute, []);
            EnsureCtor(attribute, [options.ToTypeSignature()], [valueField]);
            EnsureCtor(attribute, [factory.Int32], [valueField]);
            EnsureCtor(attribute, [factory.Int16], [valueField]);
        }

        if (needed.HasFlag(Surface.PreserveSig))
        {
            var attribute = EnsureType(corlibModule, "System.Runtime.InteropServices", "PreserveSigAttribute",
                TypeAttributes.Public | TypeAttributes.Sealed, attributeType, ref emitted);
            EnsureCtor(attribute, []);
        }

        if (needed.HasFlag(Surface.StructLayout))
        {
            var layout = EnsureEnum(corlibModule, "System.Runtime.InteropServices", "LayoutKind", enumType, ref emitted,
                ("Sequential", 0), ("Explicit", 2), ("Auto", 3));
            var charSet = EnsureEnum(corlibModule, "System.Runtime.InteropServices", "CharSet", enumType, ref emitted,
                ("None", 1), ("Ansi", 2), ("Unicode", 3), ("Auto", 4));
            var attribute = EnsureType(corlibModule, "System.Runtime.InteropServices", "StructLayoutAttribute",
                TypeAttributes.Public | TypeAttributes.Sealed, attributeType, ref emitted);
            var valueField = EnsureField(attribute, "_val", layout.ToTypeSignature(), FieldAttributes.Private);
            EnsureField(attribute, "Pack", factory.Int32, FieldAttributes.Public);
            EnsureField(attribute, "Size", factory.Int32, FieldAttributes.Public);
            EnsureField(attribute, "CharSet", charSet.ToTypeSignature(), FieldAttributes.Public);
            EnsureProperty(attribute, "Value", layout.ToTypeSignature(), valueField, true);
            EnsureCtor(attribute, [layout.ToTypeSignature()], [valueField]);
            EnsureCtor(attribute, [factory.Int16], [valueField]);
        }

        if (needed.HasFlag(Surface.Serializable))
        {
            var attribute = EnsureType(corlibModule, "System", "SerializableAttribute",
                TypeAttributes.Public | TypeAttributes.Sealed, attributeType, ref emitted);
            EnsureCtor(attribute, []);
        }

        if (needed.HasFlag(Surface.ComImport))
        {
            var attribute = EnsureType(corlibModule, "System.Runtime.InteropServices", "ComImportAttribute",
                TypeAttributes.Public | TypeAttributes.Class, attributeType, ref emitted);
            EnsureCtor(attribute, []);
        }

        if (needed.HasFlag(Surface.NonSerialized))
        {
            var attribute = EnsureType(corlibModule, "System", "NonSerializedAttribute",
                TypeAttributes.Public | TypeAttributes.Sealed, attributeType, ref emitted);
            EnsureCtor(attribute, []);
        }

        if (needed.HasFlag(Surface.FieldOffset))
        {
            var attribute = EnsureType(corlibModule, "System.Runtime.InteropServices", "FieldOffsetAttribute",
                TypeAttributes.Public | TypeAttributes.Sealed, attributeType, ref emitted);
            var valueField = EnsureField(attribute, "_val", factory.Int32, FieldAttributes.Private);
            EnsureProperty(attribute, "Offset", factory.Int32, valueField, true);
            EnsureCtor(attribute, [factory.Int32], [valueField]);
        }

        if (needed.HasFlag(Surface.DllImport))
        {
            var callingConvention = EnsureEnum(corlibModule, "System.Runtime.InteropServices", "CallingConvention", enumType, ref emitted,
                ("Winapi", 1), ("Cdecl", 2), ("StdCall", 3), ("ThisCall", 4), ("FastCall", 5));
            var charSet = EnsureEnum(corlibModule, "System.Runtime.InteropServices", "CharSet", enumType, ref emitted,
                ("None", 1), ("Ansi", 2), ("Unicode", 3), ("Auto", 4));
            var attribute = EnsureType(corlibModule, "System.Runtime.InteropServices", "DllImportAttribute",
                TypeAttributes.Public | TypeAttributes.Sealed, attributeType, ref emitted);
            var valueField = EnsureField(attribute, "_val", factory.String, FieldAttributes.Private);
            EnsureField(attribute, "EntryPoint", factory.String, FieldAttributes.Public);
            EnsureField(attribute, "CallingConvention", callingConvention.ToTypeSignature(), FieldAttributes.Public);
            EnsureField(attribute, "CharSet", charSet.ToTypeSignature(), FieldAttributes.Public);
            EnsureField(attribute, "SetLastError", factory.Boolean, FieldAttributes.Public);
            EnsureField(attribute, "ExactSpelling", factory.Boolean, FieldAttributes.Public);
            EnsureField(attribute, "PreserveSig", factory.Boolean, FieldAttributes.Public);
            EnsureField(attribute, "BestFitMapping", factory.Boolean, FieldAttributes.Public);
            EnsureField(attribute, "ThrowOnUnmappableChar", factory.Boolean, FieldAttributes.Public);
            EnsureProperty(attribute, "DllName", factory.String, valueField, true);
            EnsureCtor(attribute, [factory.String], [valueField]);
        }

        if (needed.HasFlag(Surface.IndexerName))
        {
            var attribute = EnsureType(corlibModule, "System.Runtime.CompilerServices", "IndexerNameAttribute",
                TypeAttributes.Public | TypeAttributes.Sealed, attributeType, ref emitted);
            EnsureCtor(attribute, [factory.String]);
        }

        if (needed.HasFlag(Surface.AssemblyVersion))
        {
            var attribute = EnsureType(corlibModule, "System.Reflection", "AssemblyVersionAttribute",
                TypeAttributes.Public | TypeAttributes.Sealed, attributeType, ref emitted);
            var valueField = EnsureField(attribute, "_version", factory.String, FieldAttributes.Private);
            EnsureProperty(attribute, "Version", factory.String, valueField, true);
            EnsureCtor(attribute, [factory.String], [valueField]);
        }

        return emitted;
    }

    private static int EmitAttributeSurface(List<AssemblyDefinition> assemblies,
        IReadOnlyDictionary<string, AssemblyDefinition> emittedByName, ModuleDefinition corlibModule)
    {
        // Gather first: materialized typedefs land in the same modules being
        // scanned and carry no custom attributes of their own.
        var attributes = new List<CustomAttribute>();
        foreach (var assembly in assemblies)
        {
            attributes.AddRange(assembly.CustomAttributes);
            if (assembly.ManifestModule is not { } module)
                continue;
            attributes.AddRange(module.CustomAttributes);
            foreach (var type in module.GetAllTypes())
            {
                attributes.AddRange(type.CustomAttributes);
                foreach (var genericParameter in type.GenericParameters)
                    attributes.AddRange(genericParameter.CustomAttributes);
                foreach (var field in type.Fields)
                    attributes.AddRange(field.CustomAttributes);
                foreach (var method in type.Methods)
                {
                    attributes.AddRange(method.CustomAttributes);
                    foreach (var genericParameter in method.GenericParameters)
                        attributes.AddRange(genericParameter.CustomAttributes);
                    foreach (var parameter in method.ParameterDefinitions)
                        attributes.AddRange(parameter.CustomAttributes);
                }
                foreach (var property in type.Properties)
                    attributes.AddRange(property.CustomAttributes);
                foreach (var @event in type.Events)
                    attributes.AddRange(@event.CustomAttributes);
            }
        }

        var emitted = 0;
        foreach (var attribute in attributes)
        {
            if (attribute.Constructor is not { } constructor)
                continue;

            var attributeType = UnwrapType(constructor.DeclaringType) switch
            {
                TypeReference typeRef => EnsureReferencedType(typeRef, MemberShape.AttributeClass,
                    emittedByName, corlibModule, ref emitted),
                TypeDefinition typeDef => typeDef,
                _ => null,
            };

            var signature = constructor.Signature as MethodSignature;
            if (attributeType != null)
            {
                // Mirror the referenced constructor and any named members the
                // attribute uses, resolving their signature types into the
                // target module. Anything unrepresentable there (a corlib
                // member referencing another assembly) is left absent rather
                // than emitted dangling.
                if (signature?.ParameterTypes
                        .Select(t => ResolveSignature(t, attributeType.DeclaringModule!, emittedByName, corlibModule, ref emitted))
                        .ToList() is { } parameterTypes
                    && !parameterTypes.Contains(null))
                    EnsureCtor(attributeType, parameterTypes!);
            }

            if (attribute.Signature is not { } attributeSignature)
                continue;
            foreach (var fixedArgument in attributeSignature.FixedArguments)
                MaterializeArgument(fixedArgument, emittedByName, corlibModule, ref emitted);
            foreach (var namedArgument in attributeSignature.NamedArguments)
            {
                var memberType = ResolveSignature(namedArgument.ArgumentType,
                    attributeType?.DeclaringModule ?? corlibModule, emittedByName, corlibModule, ref emitted);
                MaterializeArgument(namedArgument.Argument, emittedByName, corlibModule, ref emitted);
                if (attributeType != null && memberType != null)
                    EnsureNamedMember(attributeType, namedArgument, memberType);
            }
        }
        return emitted;
    }

    private static void MaterializeArgument(CustomAttributeArgument argument,
        IReadOnlyDictionary<string, AssemblyDefinition> emittedByName, ModuleDefinition corlibModule, ref int emitted)
    {
        MaterializeArgumentType(argument.ArgumentType, emittedByName, corlibModule, ref emitted);
        MaterializeArgumentValue(argument.Element, emittedByName, corlibModule, ref emitted);
        if (argument.Elements is { } elements)
            foreach (var element in elements)
                MaterializeArgumentValue(element, emittedByName, corlibModule, ref emitted);
    }

    private static void MaterializeArgumentValue(object? value,
        IReadOnlyDictionary<string, AssemblyDefinition> emittedByName, ModuleDefinition corlibModule, ref int emitted)
    {
        switch (value)
        {
            case TypeSignature typeValue:
                // A typeof(...) argument names a type of any kind; emit a class.
                if (UnwrapSignature(typeValue) is TypeDefOrRefSignature { Type: TypeReference typeRef })
                    EnsureReferencedType(typeRef, MemberShape.Class, emittedByName, corlibModule, ref emitted);
                break;
            case BoxedArgument boxed:
                MaterializeArgumentType(boxed.Type, emittedByName, corlibModule, ref emitted);
                MaterializeArgumentValue(boxed.Value, emittedByName, corlibModule, ref emitted);
                break;
            case CustomAttributeArgument nested:
                MaterializeArgument(nested, emittedByName, corlibModule, ref emitted);
                break;
        }
    }

    // The only non-primitive, non-System.Type types legal as attribute argument
    // types are enums, so an argument type signature ending in a TypeReference
    // to a type no emitted assembly defines must be a stripped framework enum.
    private static void MaterializeArgumentType(TypeSignature? signature,
        IReadOnlyDictionary<string, AssemblyDefinition> emittedByName, ModuleDefinition corlibModule, ref int emitted)
    {
        if (UnwrapSignature(signature) is TypeDefOrRefSignature { Type: TypeReference typeRef }
            && typeRef.FullName != "System.Type")
            EnsureReferencedType(typeRef, MemberShape.Enum, emittedByName, corlibModule, ref emitted);
    }

    private enum MemberShape { Class, Enum, AttributeClass }

    // Finds or creates the typedef a TypeReference targets when its scope is one
    // of the emitted assemblies. Nested references materialize their declaring
    // chain as plain classes. Returns null when the scope is not emitted.
    private static TypeDefinition? EnsureReferencedType(TypeReference reference, MemberShape shape,
        IReadOnlyDictionary<string, AssemblyDefinition> emittedByName, ModuleDefinition corlibModule, ref int emitted)
    {
        ModuleDefinition? module;
        TypeDefinition? declaring = null;
        switch (reference.Scope)
        {
            case AssemblyReference assemblyReference:
                if (!emittedByName.TryGetValue(assemblyReference.Name?.ToString() ?? "", out var owner)
                    || owner.ManifestModule == null)
                    return null;
                module = owner.ManifestModule;
                break;
            case ModuleDefinition moduleScope:
                module = moduleScope;
                break;
            case TypeReference parentReference:
                declaring = EnsureReferencedType(parentReference, MemberShape.Class, emittedByName, corlibModule, ref emitted);
                if (declaring == null)
                    return null;
                module = declaring.DeclaringModule;
                break;
            default:
                return null;
        }
        if (module == null)
            return null;

        var name = reference.Name?.ToString() ?? "";
        var ns = reference.Namespace?.ToString() ?? "";
        // il2cpp global-namespace types carry Namespace=null while references
        // to them read ""; treat the two as equal or a real typedef would be
        // missed and a shell typedef materialized on top of it.
        var existing = declaring == null
            ? module.TopLevelTypes.FirstOrDefault(t => !t.IsNested
                && t.Name?.ToString() == name && (t.Namespace?.ToString() ?? "") == ns)
            : declaring.NestedTypes.FirstOrDefault(t => t.Name?.ToString() == name);
        if (existing != null)
            return existing;

        if (shape == MemberShape.Enum)
        {
            var enumBase = CorLibType(module, corlibModule, "System", "Enum", ref emitted);
            var enumType = declaring == null
                ? EnsureType(module, ns, name, TypeAttributes.Public | TypeAttributes.Sealed, enumBase, ref emitted)
                : EnsureNestedType(declaring, name, TypeAttributes.NestedPublic | TypeAttributes.Sealed, enumBase, ref emitted);
            if (enumType.Fields.Count == 0)
                enumType.Fields.Add(new FieldDefinition("value__",
                    FieldAttributes.Public | FieldAttributes.SpecialName | FieldAttributes.RuntimeSpecialName,
                    new FieldSignature(module.CorLibTypeFactory.Int32)));
            return enumType;
        }

        var baseName = shape == MemberShape.AttributeClass ? "Attribute" : "Object";
        var baseType = CorLibType(module, corlibModule, "System", baseName, ref emitted);
        return declaring == null
            ? EnsureType(module, ns, name, TypeAttributes.Public | TypeAttributes.Class, baseType, ref emitted)
            : EnsureNestedType(declaring, name, TypeAttributes.NestedPublic | TypeAttributes.Class, baseType, ref emitted);
    }

    // Rewrites a signature so it can be emitted inside the target module:
    // TypeReferences scoping to a missing type in an emitted assembly are
    // materialized and swapped for the typedef signature. Returns null when a
    // corlib member would have to reference another assembly's type.
    private static TypeSignature? ResolveSignature(TypeSignature? signature, ModuleDefinition targetModule,
        IReadOnlyDictionary<string, AssemblyDefinition> emittedByName, ModuleDefinition corlibModule, ref int emitted)
    {
        switch (signature)
        {
            case null:
                return null;
            case TypeDefOrRefSignature { Type: TypeReference typeRef }:
                if (typeRef.FullName == "System.Type")
                    return ReferenceEquals(targetModule, corlibModule) ? null : signature;
                var definition = EnsureReferencedType(typeRef, MemberShape.Enum, emittedByName, corlibModule, ref emitted);
                if (definition != null)
                    return definition.ToTypeSignature();
                // Scope not emitted: legal outside corlib, impossible inside it.
                return ReferenceEquals(targetModule, corlibModule) ? null : signature;
            case TypeSpecificationSignature specification:
            {
                var baseType = ResolveSignature(specification.BaseType, targetModule, emittedByName, corlibModule, ref emitted);
                if (baseType == null)
                    return null;
                if (ReferenceEquals(baseType, specification.BaseType))
                    return signature;
                return specification switch
                {
                    SzArrayTypeSignature => new SzArrayTypeSignature(baseType),
                    ByReferenceTypeSignature => new ByReferenceTypeSignature(baseType),
                    PointerTypeSignature => new PointerTypeSignature(baseType),
                    CustomModifierTypeSignature modifier => new CustomModifierTypeSignature(
                        modifier.ModifierType, modifier.IsRequired, baseType),
                    _ => null,
                };
            }
            default:
                return signature;
        }
    }

    private static ITypeDefOrRef? UnwrapType(ITypeDefOrRef? type)
    {
        while (type is TypeSpecification { Signature: TypeSpecificationSignature specification })
            type = specification.BaseType is TypeDefOrRefSignature signature ? signature.Type : null;
        return type;
    }

    private static TypeSignature? UnwrapSignature(TypeSignature? signature)
    {
        while (signature is TypeSpecificationSignature specification)
            signature = specification.BaseType;
        return signature;
    }

    private static void EnsureNamedMember(TypeDefinition type, CustomAttributeNamedArgument argument,
        TypeSignature memberType)
    {
        var name = argument.MemberName?.ToString();
        if (string.IsNullOrEmpty(name))
            return;
        if (argument.MemberType == CustomAttributeArgumentMemberType.Field)
        {
            EnsureField(type, name!, memberType, FieldAttributes.Public);
        }
        else
        {
            var backing = EnsureField(type, "<" + name + ">k__BackingField", memberType, FieldAttributes.Private);
            EnsureProperty(type, name!, memberType, backing, false);
        }
    }

    // The four roots every synthesized type can hang off. Anything else needed
    // as a base is emitted as a plain class on System.Object.
    private static TypeDefinition EnsureCorLibType(ModuleDefinition corlibModule, string ns, string name, ref int emitted)
    {
        var existing = corlibModule.TopLevelTypes.FirstOrDefault(t =>
            t.Name?.ToString() == name && (t.Namespace?.ToString() ?? "") == ns);
        if (existing != null)
            return existing;
        var (attributes, baseName) = (ns, name) switch
        {
            ("System", "Object") => (TypeAttributes.Public | TypeAttributes.Class | TypeAttributes.BeforeFieldInit,
                (string?)null),
            ("System", "ValueType") or ("System", "Enum") =>
                (TypeAttributes.Public | TypeAttributes.Class | TypeAttributes.Abstract
                    | TypeAttributes.SequentialLayout | TypeAttributes.BeforeFieldInit,
                    name == "Enum" ? "ValueType" : "Object"),
            _ => (TypeAttributes.Public | TypeAttributes.Class | TypeAttributes.Abstract
                    | TypeAttributes.BeforeFieldInit, (string?)"Object"),
        };
        var baseType = baseName == null ? null : EnsureCorLibType(corlibModule, "System", baseName, ref emitted);
        return EnsureType(corlibModule, ns, name, attributes, baseType, ref emitted);
    }

    private static TypeDefinition EnsureType(ModuleDefinition module, string ns, string name,
        TypeAttributes attributes, ITypeDefOrRef? baseType, ref int emitted)
    {
        var existing = module.TopLevelTypes.FirstOrDefault(t => !t.IsNested
            && t.Name?.ToString() == name && (t.Namespace?.ToString() ?? "") == ns);
        if (existing != null)
            return existing;
        var type = new TypeDefinition(ns, name, attributes, baseType);
        module.TopLevelTypes.Add(type);
        emitted++;
        return type;
    }

    private static TypeDefinition EnsureNestedType(TypeDefinition parent, string name,
        TypeAttributes attributes, ITypeDefOrRef? baseType, ref int emitted)
    {
        var existing = parent.NestedTypes.FirstOrDefault(t => t.Name?.ToString() == name);
        if (existing != null)
            return existing;
        var type = new TypeDefinition(parent.Namespace, name, attributes, baseType);
        parent.NestedTypes.Add(type);
        emitted++;
        return type;
    }

    private static TypeDefinition EnsureEnum(ModuleDefinition module, string ns, string name,
        TypeDefinition enumBase, ref int emitted, params (string Name, int Value)[] members)
    {
        var enumType = EnsureType(module, ns, name,
            TypeAttributes.Public | TypeAttributes.Sealed, enumBase, ref emitted);
        if (enumType.Fields.Count == 0)
        {
            enumType.Fields.Add(new FieldDefinition("value__",
                FieldAttributes.Public | FieldAttributes.SpecialName | FieldAttributes.RuntimeSpecialName,
                new FieldSignature(module.CorLibTypeFactory.Int32)));
            foreach (var (memberName, value) in members)
                enumType.Fields.Add(new FieldDefinition(memberName,
                    FieldAttributes.Public | FieldAttributes.Static | FieldAttributes.Literal | FieldAttributes.HasDefault,
                    new FieldSignature(enumType.ToTypeSignature()))
                { Constant = AsmResolverConstants.GetOrCreateConstant(value) });
        }
        return enumType;
    }

    private static FieldDefinition EnsureField(TypeDefinition type, string name, TypeSignature signature,
        FieldAttributes attributes)
    {
        var existing = type.Fields.FirstOrDefault(f => f.Name?.ToString() == name);
        if (existing != null)
            return existing;
        var field = new FieldDefinition(name, attributes, new FieldSignature(signature));
        type.Fields.Add(field);
        return field;
    }

    private static void EnsureProperty(TypeDefinition type, string name, TypeSignature propertyType,
        FieldDefinition backingField, bool getterOnly)
    {
        if (type.Properties.Any(p => p.Name?.ToString() == name))
            return;
        var factory = type.DeclaringModule!.CorLibTypeFactory;
        var property = new PropertyDefinition(name, 0, PropertySignature.CreateInstance(propertyType));
        var getter = new MethodDefinition("get_" + name,
            MethodAttributes.Public | MethodAttributes.HideBySig | MethodAttributes.SpecialName,
            MethodSignature.CreateInstance(propertyType));
        var getterBody = new CilMethodBody();
        getterBody.Instructions.Add(CilOpCodes.Ldarg_0);
        getterBody.Instructions.Add(CilOpCodes.Ldfld, backingField);
        getterBody.Instructions.Add(CilOpCodes.Ret);
        getter.CilMethodBody = getterBody;
        type.Methods.Add(getter);
        MethodDefinition? setter = null;
        if (!getterOnly)
        {
            setter = new MethodDefinition("set_" + name,
                MethodAttributes.Public | MethodAttributes.HideBySig | MethodAttributes.SpecialName,
                MethodSignature.CreateInstance(factory.Void, [propertyType]));
            var setterBody = new CilMethodBody();
            setterBody.Instructions.Add(CilOpCodes.Ldarg_0);
            setterBody.Instructions.Add(CilOpCodes.Ldarg_1);
            setterBody.Instructions.Add(CilOpCodes.Stfld, backingField);
            setterBody.Instructions.Add(CilOpCodes.Ret);
            setter.CilMethodBody = setterBody;
            type.Methods.Add(setter);
        }
        property.SetSemanticMethods(getter, setter);
        type.Properties.Add(property);
    }

    // Emits the referenced constructor shape: matching parameter list, an
    // honest base-call prologue when a parameterless base .ctor exists (or a
    // memberref to it when the base is a corlib TypeReference), and straight
    // stores into the given backing fields. When no base .ctor is resolvable
    // the body is an explicit diagnostic throw - the same shape the pipeline's
    // own stub-fill emits for uninitializable constructors - never a silent
    // return with `this` left uninitialized.
    private static void EnsureCtor(TypeDefinition type,
        IReadOnlyList<TypeSignature> parameterTypes, IReadOnlyList<FieldDefinition>? stores = null)
    {
        var module = type.DeclaringModule!;
        if (type.Methods.Any(m => m.IsConstructor && !m.IsStatic
                && m.Signature is { } s && s.ParameterTypes.Count == parameterTypes.Count))
            return;
        var ctor = new MethodDefinition(".ctor",
            MethodAttributes.Public | MethodAttributes.HideBySig | MethodAttributes.SpecialName | MethodAttributes.RuntimeSpecialName,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void, parameterTypes));
        var body = new CilMethodBody();
        var instructions = body.Instructions;
        if (FindParameterlessCtor(type.BaseType, module) is { } baseCtor)
        {
            instructions.Add(CilOpCodes.Ldarg_0);
            instructions.Add(CilOpCodes.Call, baseCtor);
            for (var i = 0; i < (stores?.Count ?? 0); i++)
            {
                instructions.Add(CilOpCodes.Ldarg_0);
                instructions.Add(new CilInstruction(CilOpCodes.Ldarg, (ushort)(i + 1)));
                instructions.Add(CilOpCodes.Stfld, stores![i]);
            }
            instructions.Add(CilOpCodes.Ret);
        }
        else
        {
            instructions.Add(CilOpCodes.Ldnull);
            instructions.Add(CilOpCodes.Throw);
        }
        ctor.CilMethodBody = body;
        type.Methods.Add(ctor);
    }

    private static IMethodDescriptor? FindParameterlessCtor(ITypeDefOrRef? baseType, ModuleDefinition module)
    {
        // TypeDefinitions in the same module can be inspected directly; a
        // TypeReference base (a corlib type for non-corlib targets) gets a
        // memberref to its declared parameterless .ctor, which the real BCL
        // type always provides.
        for (var current = baseType; current is TypeDefinition definition; current = definition.BaseType)
        {
            var ctor = definition.Methods.FirstOrDefault(m =>
                m.IsConstructor && !m.IsStatic && m.Signature is { ParameterTypes.Count: 0 });
            if (ctor != null)
                return ctor;
        }
        if (baseType is TypeReference reference)
            return reference.CreateMemberReference(".ctor",
                MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        return null;
    }

    // A corlib member's signature may only name typedefs (corlib carries no
    // TypeRefs); outside corlib the corlib type is a normal reference.
    private static ITypeDefOrRef CorLibType(ModuleDefinition targetModule, ModuleDefinition corlibModule,
        string ns, string name, ref int emitted)
        => ReferenceEquals(targetModule, corlibModule)
            ? EnsureCorLibType(corlibModule, ns, name, ref emitted)
            : targetModule.CorLibTypeFactory.CorLibScope.CreateTypeReference(ns, name);
}
