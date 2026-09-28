using System;
using System.Collections.Generic;
using System.Linq;
using AsmResolver;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Logging;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Model.CustomAttributes;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Utils.AsmResolver;

public static class AsmResolverAssemblyPopulator
{
    public static bool IsTypeContextModule(TypeAnalysisContext typeCtx)
    {
        return typeCtx.Name.StartsWith("<Module>") || typeCtx.FullName.StartsWith("<Module>");
    }

    public static void ConfigureHierarchy(AssemblyAnalysisContext asmCtx)
    {
        foreach (var typeCtx in asmCtx.Types)
        {
            if (IsTypeContextModule(typeCtx))
                continue;

            var typeDefinition = typeCtx.GetExtraData<TypeDefinition>("AsmResolverType") ?? throw new($"AsmResolver type not found in type analysis context for {typeCtx.FullName}");

            //Type generic params.
            PopulateGenericParamsForType(typeCtx, typeDefinition);

            //Set base type
            if(asmCtx.AppContext.MetadataVersion >= 35 && typeCtx is {Definition.IsEnumType: true })
                //v35 restructures this a bit so that enums now directly inherit from their primitive type, so we need to explicitly set this to enum
                typeDefinition.BaseType = typeCtx.AppContext.SystemTypes.EnumType.ToTypeSignature().ToTypeDefOrRef();
            else
                typeDefinition.BaseType = typeCtx.BaseType?.ToTypeSignature().ToTypeDefOrRef();

            //Set interfaces
            foreach (var interfaceType in typeCtx.InterfaceContexts)
                typeDefinition.Interfaces.Add(new(interfaceType.ToTypeSignature().ToTypeDefOrRef()));
        }

        var assemblyDefinition = asmCtx.GetExtraData<AssemblyDefinition>("AsmResolverAssembly") ?? throw new("AsmResolver assembly not found in assembly analysis context for " + asmCtx);
        var moduleDefinition = assemblyDefinition.ManifestModule!;
        foreach (var typeCtx in asmCtx.ExportedTypes)
        {
            var owningAssembly = typeCtx.DeclaringAssembly.GetExtraData<AssemblyDefinition>("AsmResolverAssembly") ?? throw new("AsmResolver assembly not found in assembly analysis context for " + typeCtx.DeclaringAssembly);
            moduleDefinition.ExportedTypes.Add(new ExportedType(owningAssembly.ToAssemblyReference(), typeCtx.Namespace, typeCtx.Name));
        }
    }

    private static void PopulateGenericParamsForType(TypeAnalysisContext cppTypeDefinition, TypeDefinition ilTypeDefinition)
    {
        foreach (var param in cppTypeDefinition.GenericParameters)
        {
            var p = new GenericParameter(param.Name, (GenericParameterAttributes)param.Attributes);

            ilTypeDefinition.GenericParameters.Add(p);

            param.ConstraintTypes
                .Select(c => new GenericParameterConstraint(c.ToTypeSignature().ToTypeDefOrRef()))
                .ToList()
                .ForEach(p.Constraints.Add);
        }
    }

    // ECMA-335 writes a nested type's attribute-blob SerString as
    // "Ns.Parent+Child": only the outermost element carries a namespace.
    // AsmResolver's TypeNameBuilder walks DeclaringType but still prints each
    // element's own Namespace, so a nested typedef/typeref that kept it emits
    // "Parent+Ns.Child", which no compiler resolves. Rewrap nested elements in
    // null-namespace TypeReference clones - only the name the blob serializes
    // changes; resolution scope is preserved via the parent chain.
    internal static TypeSignature CanonicalBlobTypeName(TypeSignature signature) => signature switch
    {
        TypeDefOrRefSignature { Type.DeclaringType: not null } defOrRef =>
            new TypeDefOrRefSignature(CanonicalBlobTypeRef(defOrRef.Type), defOrRef.IsValueType),
        GenericInstanceTypeSignature generic => new GenericInstanceTypeSignature(
            CanonicalBlobTypeRef(generic.GenericType), generic.IsValueType,
            generic.TypeArguments.Select(CanonicalBlobTypeName).ToList()),
        SzArrayTypeSignature szArray => CanonicalBlobTypeName(szArray.BaseType).MakeSzArrayType(),
        ByReferenceTypeSignature byRef => CanonicalBlobTypeName(byRef.BaseType).MakeByReferenceType(),
        PointerTypeSignature pointer => CanonicalBlobTypeName(pointer.BaseType).MakePointerType(),
        PinnedTypeSignature pinned => CanonicalBlobTypeName(pinned.BaseType).MakePinnedType(),
        CustomModifierTypeSignature modifier => CanonicalBlobTypeName(modifier.BaseType)
            .MakeModifierType(modifier.ModifierType, modifier.IsRequired),
        ArrayTypeSignature array => new ArrayTypeSignature(
            CanonicalBlobTypeName(array.BaseType), array.Dimensions.ToArray()),
        _ => signature,
    };

    private static TypeReference CanonicalBlobTypeRef(ITypeDefOrRef type)
    {
        if (type.DeclaringType is { } declaring)
            // Nested level: the canonical SerString drops the element's own
            // namespace; its scope is the canonicalized parent.
            return new TypeReference(CanonicalBlobTypeRef(declaring), null, type.Name);

        // Outermost element keeps its real scope (module, or declaring
        // assembly reference) and namespace. ITypeDefOrRef.Scope already
        // answers module-or-parent for TypeDefinition and the declared scope
        // for TypeReference.
        return new TypeReference(type.Scope, type.Namespace, type.Name);
    }

    private static TypeSignature? BlobTypeValue(BaseCustomAttributeTypeParameter parameter)
        => parameter.TypeContext?.ToTypeSignature() is { } signature
            ? CanonicalBlobTypeName(signature)
            : null;

    private static TypeSignature GetTypeSigFromAttributeArg(BaseCustomAttributeParameter parameter) =>
        parameter switch
        {
            CustomAttributePrimitiveParameter primitiveParameter => parameter.Owner.Constructor.AppContext.SystemTypes.GetPrimitive(primitiveParameter.PrimitiveType).ToTypeSignature(),
            CustomAttributeEnumParameter enumParameter => enumParameter.EnumTypeContext.ToTypeSignature(),
            BaseCustomAttributeTypeParameter => parameter.Owner.Constructor.AppContext.SystemTypes.SystemTypeType.ToTypeSignature(),
            CustomAttributeArrayParameter arrayParameter => parameter.Owner.Constructor.AppContext.SystemTypes.GetPrimitive(arrayParameter.ArrType).ToTypeSignature().MakeSzArrayType(),
            _ => throw new ArgumentException("Unknown custom attribute parameter type: " + parameter.GetType().FullName)
        };

    private static CustomAttributeArgument BuildArrayArgument(CustomAttributeArrayParameter arrayParameter)
    {
#if !DEBUG
        try
#endif
        {
            if (arrayParameter.IsNullArray)
                return BuildEmptyArrayArgument(arrayParameter);

            var typeSig = GetTypeSigFromAttributeArg(arrayParameter);

            var isObjectArray = arrayParameter.ArrType == Il2CppTypeEnum.IL2CPP_TYPE_OBJECT;

            var arrayElements = arrayParameter.ArrayElements.Select(e =>
            {
                var rawValue = e switch
                {
                    CustomAttributePrimitiveParameter primitiveParameter => primitiveParameter.PrimitiveValue,
                    CustomAttributeEnumParameter enumParameter => enumParameter.UnderlyingPrimitiveParameter.PrimitiveValue,
                    BaseCustomAttributeTypeParameter type => (object?)BlobTypeValue(type),
                    CustomAttributeNullParameter => null,
                    CustomAttributeArrayParameter array => BuildArrayArgument(array).Elements.ToArray(),
                    _ => throw new("Not supported array element type: " + e.GetType().FullName)
                };

                if (isObjectArray)
                    //Object params have to be boxed
                    return new BoxedArgument(GetTypeSigFromAttributeArg(e), rawValue);

                return rawValue;
            }).ToArray();

            return new(typeSig, arrayElements);
        }
#if !DEBUG
        catch (Exception e)
        {
            throw new("Failed to build array argument for " + arrayParameter, e);
        }
#endif
    }

    private static CustomAttributeArgument BuildEmptyArrayArgument(CustomAttributeArrayParameter arrayParameter)
    {
        //Need to resolve the type of the array because it's not in the blob and AsmResolver needs it.

        var typeSig = arrayParameter.Kind switch
        {
            CustomAttributeParameterKind.ConstructorParam => arrayParameter.Owner.Constructor.Parameters[arrayParameter.Index].ToTypeSignature(),
            CustomAttributeParameterKind.Property => arrayParameter.Owner.Properties[arrayParameter.Index].Property.ToTypeSignature(),
            CustomAttributeParameterKind.Field => arrayParameter.Owner.Fields[arrayParameter.Index].Field.ToTypeSignature(),
            CustomAttributeParameterKind.ArrayElement => throw new("Array element cannot be an array (or at least, not implemented!)"),
            _ => throw new("Unknown array parameter kind: " + arrayParameter.Kind)
        };

        return new(typeSig) { IsNullArray = true };
    }

    /// <summary>
    /// Converts the given parameter to a custom attribute argument, given the context of the parent assembly.
    /// </summary>
    /// <param name="parameter">The parameter to convert</param>
    /// <param name="boxIfNeeded">Whether the returned attribute will be used in context of a member that is typed as object. If true, the resulting attribute will be an object-typed one wrapping a BoxedArgument containing the real value. If false, the real value will be returned directly.</param>
    /// <remarks>
    /// BoxIfNeeded will cause the resulting attribute to be boxed if the parameter is an enum or a type parameter. This is required if, for example, the enum or type is being passed as the argument in a constructor for which the parameter is typed as object.
    /// </remarks>
    internal static CustomAttributeArgument FromAnalyzedAttributeArgument(BaseCustomAttributeParameter parameter, bool boxIfNeeded)
    {
#if !DEBUG
        try
#endif
        {
            var systemTypes = parameter.Owner.Constructor.AppContext.SystemTypes;
            
            return parameter switch
            {
                CustomAttributePrimitiveParameter primitiveParameter when boxIfNeeded => new(systemTypes.SystemObjectType.ToTypeSignature(), new BoxedArgument(GetTypeSigFromAttributeArg(primitiveParameter), primitiveParameter.PrimitiveValue)),
                CustomAttributePrimitiveParameter primitiveParameter => new(GetTypeSigFromAttributeArg(primitiveParameter), primitiveParameter.PrimitiveValue),
                
                CustomAttributeEnumParameter enumParameter when boxIfNeeded => new(systemTypes.SystemObjectType.ToTypeSignature(), new BoxedArgument(GetTypeSigFromAttributeArg(enumParameter), enumParameter.UnderlyingPrimitiveParameter.PrimitiveValue)),
                CustomAttributeEnumParameter enumParameter => new(GetTypeSigFromAttributeArg(enumParameter), enumParameter.UnderlyingPrimitiveParameter.PrimitiveValue),
                
                //A typeof(x) argument in an object-typed slot is boxed like an enum is:
                //the blob needs the SERIALIZATION_TYPE_TYPE tag before the SerString or
                //the attribute decodes as garbage ("Could not decode attribute arguments").
                BaseCustomAttributeTypeParameter typeParameter when boxIfNeeded => new(systemTypes.SystemObjectType.ToTypeSignature(), new BoxedArgument(systemTypes.SystemTypeType.ToTypeSignature(), BlobTypeValue(typeParameter))),
                BaseCustomAttributeTypeParameter typeParameter => new(systemTypes.SystemTypeType.ToTypeSignature(), BlobTypeValue(typeParameter)),
                
                CustomAttributeArrayParameter arrayParameter => BuildArrayArgument(arrayParameter),
                _ => throw new ArgumentException("Unknown custom attribute parameter type: " + parameter.GetType().FullName)
            };
        }
#if !DEBUG
        catch (Exception e)
        {
            throw new("Failed to build custom attribute argument for " + parameter, e);
        }
#endif
    }

    private static CustomAttributeNamedArgument FromAnalyzedAttributeField(CustomAttributeField field)
        => new(CustomAttributeArgumentMemberType.Field, field.Field.Name, GetTypeSigFromAttributeArg(field.Value), FromAnalyzedAttributeArgument(field.Value, field.Field.FieldType == field.Field.AppContext.SystemTypes.SystemObjectType));

    private static CustomAttributeNamedArgument FromAnalyzedAttributeProperty(CustomAttributeProperty property)
        => new(CustomAttributeArgumentMemberType.Property, property.Property.Name, GetTypeSigFromAttributeArg(property.Value), FromAnalyzedAttributeArgument(property.Value, property.Property.PropertyType == property.Property.AppContext.SystemTypes.SystemObjectType));

    private static CustomAttribute? ConvertCustomAttribute(AnalyzedCustomAttribute analyzedCustomAttribute)
    {
        var ctor = analyzedCustomAttribute.Constructor.GetExtraData<MethodDefinition>("AsmResolverMethod") ?? throw new($"Found a custom attribute with no AsmResolver constructor: {analyzedCustomAttribute}");

        CustomAttributeSignature signature;
        var numNamedArgs = analyzedCustomAttribute.Fields.Count + analyzedCustomAttribute.Properties.Count;

#if !DEBUG
        try
#endif
        {
            if (!analyzedCustomAttribute.HasAnyParameters && numNamedArgs == 0)
                signature = new();
            else if (analyzedCustomAttribute.IsSuitableForEmission)
            {
                if (numNamedArgs == 0)
                {
                    //Only fixed arguments.
                    signature = new(analyzedCustomAttribute.ConstructorParameters.Select(p => FromAnalyzedAttributeArgument(p, analyzedCustomAttribute.Constructor.Parameters[p.Index].ParameterType == analyzedCustomAttribute.Constructor.AppContext.SystemTypes.SystemObjectType)));
                }
                else
                {
                    //Has named arguments.
                    signature = new(
                        analyzedCustomAttribute.ConstructorParameters.Select(p => FromAnalyzedAttributeArgument(p, analyzedCustomAttribute.Constructor.Parameters[p.Index].ParameterType == analyzedCustomAttribute.Constructor.AppContext.SystemTypes.SystemObjectType)),
                        analyzedCustomAttribute.Fields
                            .Select(FromAnalyzedAttributeField)
                            .Concat(analyzedCustomAttribute.Properties.Select(FromAnalyzedAttributeProperty))
                    );
                }
            }
            else
            {
                return null;
            }
        }
#if !DEBUG
        catch (Exception e)
        {
            throw new("Failed to build custom attribute signature for " + analyzedCustomAttribute, e);
        }
#endif

        return new CustomAttribute((ICustomAttributeType)ctor, signature);
    }

    // il2cpp strips accessor MethodDefs the binary never calls, but a property
    // used as an attribute named argument keeps its setter (the runtime assigns
    // through it) while losing the getter, leaving a write-only member that C#
    // cannot name in attribute syntax (CS0617). Restore the missing accessor
    // only when a compiler backing field exists - that proves the original was
    // an auto-property the accessor can read or write directly. A property
    // without one is left unchanged and logged rather than given an invented
    // body.
    private static void EnsureNamedArgumentAccessors(AnalyzedCustomAttribute attribute)
    {
        foreach (var namedProperty in attribute.Properties)
        {
            var property = namedProperty.Property.GetExtraData<PropertyDefinition>("AsmResolverProperty");
            var declaringType = property?.DeclaringType;
            if (declaringType == null || property.Signature is not { ParameterTypes.Count: 0 })
                continue; //Indexers can never be named arguments anyway.

            //PopulateCustomAttributes runs per-assembly in parallel, and an
            //attribute in one assembly can name a property on a typedef in
            //another - serialize the check-and-synthesize on the property.
            lock (property)
            {
                var getter = property.GetMethod;
                var setter = property.SetMethod;
                if (getter != null && setter != null)
                    continue;

                var backingField = declaringType.Fields.FirstOrDefault(f =>
                    f.Name?.ToString() == $"<{property.Name}>k__BackingField");
                if (backingField == null)
                {
                    Logger.WarnNewline($"Attribute named argument '{property.Name}' on '{declaringType.FullName}' has a missing accessor but no compiler backing field to restore it from; leaving the property as-is.", "Custom Attribute Restoration");
                    continue;
                }

                getter ??= SynthesizeAccessor(property, setter, backingField, true);
                setter ??= SynthesizeAccessor(property, getter, backingField, false);
                property.SetSemanticMethods(getter, setter);
            }
        }
    }

    private static MethodDefinition SynthesizeAccessor(PropertyDefinition property, MethodDefinition? sibling, FieldDefinition backingField, bool isGetter)
    {
        var declaringType = property.DeclaringType!;
        var propertyType = property.Signature!.ReturnType;
        var corlibFactory = declaringType.DeclaringModule!.CorLibTypeFactory;
        var returnType = isGetter ? propertyType : corlibFactory.Void;
        IEnumerable<TypeSignature> parameterTypes = isGetter ? [] : [propertyType];
        var accessorSignature = property.Signature.HasThis
            ? MethodSignature.CreateInstance(returnType, parameterTypes)
            : MethodSignature.CreateStatic(returnType, parameterTypes);

        //Mirror the surviving accessor when there is one - paired accessors
        //share visibility and dispatch flags in real metadata.
        var attributes = (sibling?.Attributes ?? MethodAttributes.Public)
            | MethodAttributes.HideBySig | MethodAttributes.SpecialName;
        // Accessor names embed the property's name: for an explicit interface
        // implementation like `I.Prop` the pair is `I.get_Prop`/`I.set_Prop`, so
        // keep the dotted prefix or the pair stops matching the interface
        // convention.
        var propertyName = property.Name.ToString();
        var lastDot = propertyName.LastIndexOf('.');
        var accessorName = lastDot < 0
            ? (isGetter ? "get_" : "set_") + propertyName
            : propertyName.Substring(0, lastDot + 1) + (isGetter ? "get_" : "set_") + propertyName.Substring(lastDot + 1);
        var accessor = new MethodDefinition(accessorName, attributes, accessorSignature);
        declaringType.Methods.Add(accessor);

        if (accessor.IsAbstract)
            return accessor;

        // On a generic declaring type the field operand must be the type's own
        // generic instance (a TypeSpec `C<T>`), not the bare typedef — that is
        // the shape the compiler emits and the only one the verifier accepts.
        IFieldDescriptor fieldOperand = backingField;
        if (declaringType.GenericParameters.Count > 0)
        {
            var selfInstance = new GenericInstanceTypeSignature(
                declaringType, declaringType.IsValueType,
                declaringType.GenericParameters
                    .Select((_, i) => (TypeSignature)new GenericParameterSignature(GenericParameterType.Type, i))
                    .ToArray());
            fieldOperand = new MemberReference(
                new TypeSpecification(selfInstance), backingField.Name, backingField.Signature);
        }

        var body = new CilMethodBody();
        var instructions = body.Instructions;
        if (property.Signature.HasThis)
        {
            instructions.Add(CilOpCodes.Ldarg_0);
            if (!isGetter)
                instructions.Add(CilOpCodes.Ldarg_1);
            instructions.Add(isGetter ? CilOpCodes.Ldfld : CilOpCodes.Stfld, fieldOperand);
        }
        else
        {
            if (!isGetter)
                instructions.Add(CilOpCodes.Ldarg_0);
            instructions.Add(isGetter ? CilOpCodes.Ldsfld : CilOpCodes.Stsfld, fieldOperand);
        }
        instructions.Add(CilOpCodes.Ret);
        accessor.CilMethodBody = body;

        return accessor;
    }

    private static void CopyCustomAttributes(HasCustomAttributes source, IList<CustomAttribute> destination)
    {
        if (source.CustomAttributes == null)
            return;

#if !DEBUG
        try
#endif
        {
            foreach (var analyzedCustomAttribute in source.CustomAttributes)
            {
                var asmResolverCustomAttribute = ConvertCustomAttribute(analyzedCustomAttribute);
                if (asmResolverCustomAttribute != null)
                {
                    destination.Add(asmResolverCustomAttribute);
                    EnsureNamedArgumentAccessors(analyzedCustomAttribute);
                }
            }
        }
#if !DEBUG
        catch (Exception e)
        {
            throw new("Failed to copy custom attributes for " + source, e);
        }
#endif
    }

    public static void PopulateCustomAttributes(AssemblyAnalysisContext asmContext)
    {
#if !DEBUG
        try
#endif
        {
            var assembly = asmContext.GetExtraData<AssemblyDefinition>("AsmResolverAssembly")!;
            CopyCustomAttributes(asmContext, assembly.CustomAttributes);
            CopyCustomAttributes(asmContext.ManifestModule, assembly.ManifestModule!.CustomAttributes);

            foreach (var type in asmContext.Types)
            {
                if (IsTypeContextModule(type))
                    continue;

                CopyCustomAttributes(type, type.GetExtraData<TypeDefinition>("AsmResolverType")!.CustomAttributes);

                foreach (var method in type.Methods)
                {
                    var methodDef = method.GetExtraData<MethodDefinition>("AsmResolverMethod")!;
                    CopyCustomAttributes(method, methodDef.CustomAttributes);

                    var parameterDefinitions = methodDef.ParameterDefinitions;
                    foreach (var parameterAnalysisContext in method.Parameters)
                    {
                        CopyCustomAttributes(parameterAnalysisContext, parameterDefinitions[parameterAnalysisContext.ParameterIndex].CustomAttributes);
                    }
                }

                foreach (var field in type.Fields)
                    CopyCustomAttributes(field, field.GetExtraData<FieldDefinition>("AsmResolverField")!.CustomAttributes);

                foreach (var property in type.Properties)
                    CopyCustomAttributes(property, property.GetExtraData<PropertyDefinition>("AsmResolverProperty")!.CustomAttributes);

                foreach (var eventDefinition in type.Events)
                    CopyCustomAttributes(eventDefinition, eventDefinition.GetExtraData<EventDefinition>("AsmResolverEvent")!.CustomAttributes);
            }
        }
#if !DEBUG
        catch (Exception e)
        {
            throw new($"Failed to populate custom attributes in {asmContext}", e);
        }
#endif
    }

    public static void CopyDataFromIl2CppToManaged(AssemblyAnalysisContext asmContext)
    {
        var managedAssembly = asmContext.GetExtraData<AssemblyDefinition>("AsmResolverAssembly") ?? throw new("AsmResolver assembly not found in assembly analysis context for " + asmContext);

        foreach (var typeContext in asmContext.Types)
        {
            if (IsTypeContextModule(typeContext))
                continue;

            var managedType = typeContext.GetExtraData<TypeDefinition>("AsmResolverType") ?? throw new($"AsmResolver type not found in type analysis context for {typeContext.Definition?.FullName}");
            // CopyCustomAttributes(typeContext, managedType.CustomAttributes);

#if !DEBUG
            try
#endif
            {
                CopyIl2CppDataToManagedType(typeContext, managedType);
            }
#if !DEBUG
            catch (Exception e)
            {
                throw new Exception($"Failed to process type {managedType.FullName} (module {managedType.DeclaringModule?.Name}, declaring type {managedType.DeclaringType?.FullName}) in {asmContext.Name}", e);
            }
#endif
        }
    }

    private static void CopyIl2CppDataToManagedType(TypeAnalysisContext typeContext, TypeDefinition ilTypeDefinition)
    {
        CopyFieldsInType(typeContext, ilTypeDefinition);

        CopyMethodsInType(typeContext, ilTypeDefinition);

        CopyPropertiesInType(typeContext, ilTypeDefinition);

        CopyEventsInType(typeContext, ilTypeDefinition);
    }

    private static void CopyFieldsInType(TypeAnalysisContext typeContext, TypeDefinition ilTypeDefinition)
    {
        foreach (var fieldContext in typeContext.Fields)
        {
            var fieldTypeSig = fieldContext.ToTypeSignature();

            var managedField = new FieldDefinition(fieldContext.Name, (FieldAttributes)fieldContext.Attributes, fieldTypeSig);

            //Field default values
            if (managedField.HasDefault)
                managedField.Constant = AsmResolverConstants.GetOrCreateConstant(fieldContext.ConstantValue);

            //Field Initial Values (used for allocation of Array Literals)
            if (managedField.HasFieldRva)
                managedField.FieldRva = new DataSegment(fieldContext.StaticArrayInitialValue);

            //Copy field offset
            if (ilTypeDefinition.IsExplicitLayout && !fieldContext.IsStatic)
                managedField.FieldOffset = fieldContext.Offset;

            fieldContext.PutExtraData("AsmResolverField", managedField);

            ilTypeDefinition.Fields.Add(managedField);
        }
    }

    private static void CopyMethodsInType(TypeAnalysisContext typeContext, TypeDefinition ilTypeDefinition)
    {
        foreach (var methodCtx in typeContext.Methods)
        {
            var returnType = methodCtx.ReturnType.ToTypeSignature();

            var paramData = methodCtx.Parameters;
            var parameterTypes = new TypeSignature[paramData.Count];
            var parameterDefinitions = new ParameterDefinition[paramData.Count];
            foreach (var parameterAnalysisContext in methodCtx.Parameters)
            {
                var i = parameterAnalysisContext.ParameterIndex;
                parameterTypes[i] = parameterAnalysisContext.ParameterType.ToTypeSignature();

                var sequence = (ushort)(i + 1); //Add one because sequence 0 is the return type
                parameterDefinitions[i] = new(sequence, parameterAnalysisContext.Name, (ParameterAttributes)parameterAnalysisContext.Attributes);

                if (parameterAnalysisContext.Attributes.HasFlag(System.Reflection.ParameterAttributes.HasDefault))
                    parameterDefinitions[i].Constant = AsmResolverConstants.GetOrCreateConstant(parameterAnalysisContext.DefaultValue);
            }


            var signature = methodCtx.IsStatic
                ? MethodSignature.CreateStatic(returnType, methodCtx.GenericParameters.Count, parameterTypes)
                : MethodSignature.CreateInstance(returnType, methodCtx.GenericParameters.Count, parameterTypes);

            var managedMethod = new MethodDefinition(methodCtx.Name, (MethodAttributes)methodCtx.Attributes, signature);

            managedMethod.ImplAttributes = (MethodImplAttributes)methodCtx.ImplAttributes;

            if (methodCtx.Definition != null)
            {
                if (methodCtx.Definition.IsUnmanagedCallersOnly && typeContext.AppContext.SystemTypes.UnmanagedCallersOnlyAttributeType != null)
                {
                    var unmanagedCallersOnlyType = typeContext.AppContext.SystemTypes.UnmanagedCallersOnlyAttributeType.GetExtraData<TypeDefinition>("AsmResolverType");
                    if(unmanagedCallersOnlyType != null)
                        managedMethod.CustomAttributes.Add(new CustomAttribute((ICustomAttributeType)unmanagedCallersOnlyType.GetConstructor()!, new()));
                }

            }

            //Add parameter definitions if we have them so we get names, defaults, out params, etc
            foreach (var parameterDefinition in parameterDefinitions)
            {
                managedMethod.ParameterDefinitions.Add(parameterDefinition);
            }

            //Handle generic parameters.
            methodCtx.GenericParameters
                .ForEach(p =>
                {
                    var gp = new GenericParameter(p.Name, (GenericParameterAttributes)p.Attributes);

                    if (!managedMethod.GenericParameters.Contains(gp))
                        managedMethod.GenericParameters.Add(gp);

                    p.ConstraintTypes
                        .Select(c => new GenericParameterConstraint(c.ToTypeSignature().ToTypeDefOrRef()))
                        .ToList()
                        .ForEach(gp.Constraints.Add);
                });


            methodCtx.PutExtraData("AsmResolverMethod", managedMethod);
            ilTypeDefinition.Methods.Add(managedMethod);

            MemberAccessibility.NormalizeEmittedOverrideAccess(methodCtx);
        }
    }

    private static void CopyPropertiesInType(TypeAnalysisContext typeContext, TypeDefinition ilTypeDefinition)
    {
        foreach (var propertyCtx in typeContext.Properties)
        {
            var propertyTypeSig = propertyCtx.ToTypeSignature();
            var propertySignature = propertyCtx.IsStatic
                ? PropertySignature.CreateStatic(propertyTypeSig)
                : PropertySignature.CreateInstance(propertyTypeSig);

            var managedProperty = new PropertyDefinition(propertyCtx.Name, (PropertyAttributes)propertyCtx.Attributes, propertySignature);

            var managedGetter = propertyCtx.Getter?.GetExtraData<MethodDefinition>("AsmResolverMethod");
            var managedSetter = propertyCtx.Setter?.GetExtraData<MethodDefinition>("AsmResolverMethod");

            managedProperty.SetSemanticMethods(managedGetter, managedSetter);

            //Indexer parameters
            if (managedGetter != null && managedGetter.Parameters.Count > 0)
            {
                foreach (var parameter in managedGetter.Parameters)
                {
                    propertySignature.ParameterTypes.Add(parameter.ParameterType);
                }
            }
            else if (managedSetter != null && managedSetter.Parameters.Count > 1)
            {
                //value parameter is always last
                for (var i = 0; i < managedSetter.Parameters.Count - 1; i++)
                {
                    var parameter = managedSetter.Parameters[i];
                    propertySignature.ParameterTypes.Add(parameter.ParameterType);
                }
            }

            propertyCtx.PutExtraData("AsmResolverProperty", managedProperty);

            ilTypeDefinition.Properties.Add(managedProperty);

            // il2cpp strips accessor MethodDefs the binary never calls, so a
            // compiler-generated auto-property can arrive with only its setter
            // surviving. A setter-only property decompiles to `{ set; }`, which
            // is not valid C# (CS8051). `<X>k__BackingField` proves the original
            // was `{ get; set; }`, so the getter can be restored from it. A
            // normal setter's only parameter is `value`; a setter with more is
            // an indexer, which can never be an auto-property.
            // A dotted property name is an explicit interface implementation;
            // C# forbids those as auto-properties, so the interface's own
            // stripped getter cannot be evidenced by a backing field and the
            // surviving accessor pair already decompiles legally — leave it.
            if (managedGetter == null && managedSetter is { Parameters.Count: 1 }
                && !managedProperty.Name!.ToString().Contains('.'))
            {
                var backingField = ilTypeDefinition.Fields.FirstOrDefault(f =>
                    f.Name?.ToString() == $"<{managedProperty.Name}>k__BackingField");
                if (backingField != null)
                    managedProperty.SetSemanticMethods(
                        SynthesizeAccessor(managedProperty, managedSetter, backingField, true),
                        managedSetter);
            }
        }
    }

    private static void CopyEventsInType(TypeAnalysisContext cppTypeDefinition, TypeDefinition ilTypeDefinition)
    {
        foreach (var eventCtx in cppTypeDefinition.Events)
        {
            var eventType = eventCtx.ToTypeSignature().ToTypeDefOrRef();

            var managedEvent = new EventDefinition(eventCtx.Name, (EventAttributes)eventCtx.Attributes, eventType);

            var managedAdder = eventCtx.Adder?.GetExtraData<MethodDefinition>("AsmResolverMethod");
            var managedRemover = eventCtx.Remover?.GetExtraData<MethodDefinition>("AsmResolverMethod");
            var managedInvoker = eventCtx.Invoker?.GetExtraData<MethodDefinition>("AsmResolverMethod");

            managedEvent.SetSemanticMethods(managedAdder, managedRemover, managedInvoker);

            eventCtx.PutExtraData("AsmResolverEvent", managedEvent);

            ilTypeDefinition.Events.Add(managedEvent);
        }
    }

    public static void AddExplicitInterfaceImplementations(AssemblyAnalysisContext asmContext)
    {
        var managedAssembly = asmContext.GetExtraData<AssemblyDefinition>("AsmResolverAssembly") ?? throw new("AsmResolver assembly not found in assembly analysis context for " + asmContext);
        var runtimeContext = asmContext.AppContext.GetExtraData<RuntimeContext>("AsmResolverRuntimeContext") ?? throw new("AsmResolver runtime context not found in application analysis context");

        var module = managedAssembly.ManifestModule!;

        foreach (var typeContext in asmContext.Types)
        {
            if (IsTypeContextModule(typeContext))
                continue;

            var managedType = typeContext.GetExtraData<TypeDefinition>("AsmResolverType") ?? throw new($"AsmResolver type not found in type analysis context for {typeContext.Definition?.FullName}");

#if !DEBUG
            try
#endif
            {
                AddExplicitInterfaceImplementations(managedType, typeContext, runtimeContext);
            }
#if !DEBUG
            catch (Exception e)
            {
                throw new Exception($"Failed to process type {managedType.FullName} (module {managedType.DeclaringModule?.Name}, declaring type {managedType.DeclaringType?.FullName}) in {asmContext.Name}", e);
            }
#endif
        }
    }

    private static void AddExplicitInterfaceImplementations(TypeDefinition type, TypeAnalysisContext typeContext, RuntimeContext runtimeContext)
    {
        List<(PropertyDefinition InterfaceProperty, TypeSignature InterfaceType, MethodDefinition Method)>? getMethodsToCreate = null;
        List<(PropertyDefinition InterfaceProperty, TypeSignature InterfaceType, MethodDefinition Method)>? setMethodsToCreate = null;

        foreach (var methodContext in typeContext.Methods)
        {
            var isPrivate = (methodContext.Attributes & System.Reflection.MethodAttributes.MemberAccessMask) == System.Reflection.MethodAttributes.Private;

            foreach (var overrideContext in methodContext.Overrides)
            {
                if (overrideContext.Name == methodContext.Name && !isPrivate)
                    continue;

                // The emitted MethodImpl sits on typeContext, so the operand
                // only needs the access visible from there.
                IMethodDefOrRef interfaceMethod;
                using (MemberAccessibility.EmittingFrom(typeContext))
                    interfaceMethod = (IMethodDefOrRef)overrideContext.ToMethodDescriptor();
                var method = methodContext.GetExtraData<MethodDefinition>("AsmResolverMethod") ?? throw new($"AsmResolver method not found in method analysis context for {methodContext}");
                type.MethodImplementations.Add(new MethodImplementation(interfaceMethod, method));
                var resolutionStatus = interfaceMethod.Resolve(runtimeContext, out var interfaceMethodResolved);
                if (resolutionStatus == ResolutionStatus.Success && interfaceMethodResolved != null)
                {
                    if (interfaceMethodResolved.IsGetMethod && !method.IsGetMethod)
                    {
                        getMethodsToCreate ??= [];
                        var interfacePropertyResolved = interfaceMethodResolved.DeclaringType!.Properties.First(p => p.Semantics.Contains(interfaceMethodResolved.Semantics));
                        getMethodsToCreate.Add((interfacePropertyResolved, interfaceMethod.DeclaringType!.ToTypeSignature(runtimeContext), method));
                    }
                    else if (interfaceMethodResolved.IsSetMethod && !method.IsSetMethod)
                    {
                        setMethodsToCreate ??= [];
                        var interfacePropertyResolved = interfaceMethodResolved.DeclaringType!.Properties.First(p => p.Semantics.Contains(interfaceMethodResolved.Semantics));
                        setMethodsToCreate.Add((interfacePropertyResolved, interfaceMethod.DeclaringType!.ToTypeSignature(runtimeContext), method));
                    }
                }
            }
        }

        // Il2Cpp doesn't include properties for explicit interface implementations, so we have to create them ourselves.
        if (getMethodsToCreate is not null)
        {
            foreach (var entry in getMethodsToCreate)
            {
                var (interfaceProperty, interfaceType, getMethod) = entry;
                var setMethod = setMethodsToCreate?
                    .FirstOrDefault(e => e.InterfaceProperty == interfaceProperty && runtimeContext.SignatureComparer.Equals(e.InterfaceType, interfaceType))
                    .Method;

                var name = $"{interfaceType.FullName}.{interfaceProperty.Name}";
                var propertySignature = getMethod.IsStatic
                    ? PropertySignature.CreateStatic(getMethod.Signature!.ReturnType, getMethod.Signature.ParameterTypes)
                    : PropertySignature.CreateInstance(getMethod.Signature!.ReturnType, getMethod.Signature.ParameterTypes);
                var property = new PropertyDefinition(name, interfaceProperty.Attributes, propertySignature);
                type.Properties.Add(property);
                property.SetSemanticMethods(getMethod, setMethod);
            }
        }
        if (setMethodsToCreate is not null)
        {
            foreach (var entry in setMethodsToCreate)
            {
                var (interfaceProperty, interfaceType, setMethod) = entry;
                if (getMethodsToCreate?.Any(e => e.InterfaceProperty == interfaceProperty && runtimeContext.SignatureComparer.Equals(e.InterfaceType, interfaceType)) == true)
                    continue;
                var name = $"{interfaceType.FullName}.{interfaceProperty.Name}";
                var propertySignature = setMethod.IsStatic
                    ? PropertySignature.CreateStatic(setMethod.Signature!.ParameterTypes[^1], setMethod.Signature.ParameterTypes.Take(setMethod.Signature.ParameterTypes.Count - 1))
                    : PropertySignature.CreateInstance(setMethod.Signature!.ParameterTypes[^1], setMethod.Signature.ParameterTypes.Take(setMethod.Signature.ParameterTypes.Count - 1));
                var property = new PropertyDefinition(name, interfaceProperty.Attributes, propertySignature);
                type.Properties.Add(property);
                property.SetSemanticMethods(null, setMethod);
            }
        }
    }
}
