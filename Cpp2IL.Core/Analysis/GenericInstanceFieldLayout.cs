using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

//Resolves field offsets on generic types, which are all 0 in the metadata.
public static class GenericInstanceFieldLayout
{
    public static (FieldAnalysisContext Field, long Offset, long Size)? FindFieldContainingOffset(
        GenericInstanceTypeAnalysisContext instance, long targetOffset)
    {
        var pointerSize = instance.AppContext.Binary.PointerSizeBytes;
        var offset = instance.IsValueType ? 0 : InstanceSize(instance.BaseType, pointerSize);
        foreach (var definition in instance.GenericType.Fields.Where(field => !field.IsStatic))
        {
            var field = new ConcreteGenericFieldAnalysisContext(definition, instance);
            if (FieldLayout(field.FieldType, pointerSize) is not var (size, alignment))
                return null;
            offset = (offset + alignment - 1) & ~(alignment - 1);
            if (targetOffset >= offset && targetOffset < offset + size)
                return (field, offset, size);
            offset += size;
        }
        return null;
    }

    // The instance-aware counterparts of FindFieldAtOffset/FindStaticFieldAtOffset: the layout is
    // computed on the instantiated field types, so value-type arguments land at the offsets the
    // runtime produced rather than the erased sizes the generic definition's field types suggest.
    public static FieldAnalysisContext? FindFieldAtOffset(
        GenericInstanceTypeAnalysisContext instance, long targetOffset)
        => FindInstanceFieldAtOffset(instance, targetOffset, false);

    public static FieldAnalysisContext? FindStaticFieldAtOffset(
        GenericInstanceTypeAnalysisContext instance, long targetOffset)
        => FindInstanceFieldAtOffset(instance, targetOffset, true);

    private static FieldAnalysisContext? FindInstanceFieldAtOffset(
        GenericInstanceTypeAnalysisContext instance, long targetOffset, bool isStatic)
    {
        var pointerSize = instance.AppContext.Binary.PointerSizeBytes;
        var offset = isStatic || instance.IsValueType ? 0 : InstanceSize(instance.BaseType, pointerSize);
        foreach (var definition in instance.GenericType.Fields)
        {
            if (definition.IsStatic != isStatic)
                continue;

            var field = new ConcreteGenericFieldAnalysisContext(definition, instance);
            if (FieldLayout(field.FieldType, pointerSize) is not var (size, alignment))
                return null;

            offset = (offset + alignment - 1) & ~(alignment - 1);
            if (offset == targetOffset)
                return field;

            offset += size;
        }
        return null;
    }

    // A field's (size, alignment): value types get the computed struct layout (member alignment
    // and trailing padding included); everything else uses the minimum unboxed size.
    private static (long Size, long Alignment)? FieldLayout(TypeAnalysisContext fieldType, int pointerSize)
    {
        if (fieldType.IsValueType && GetSizeAndAlignment(fieldType, pointerSize) is { } layout)
            return layout;
        var fallback = TypeSizes.MinimumUnboxedSize(fieldType, pointerSize);
        return fallback > 0 ? (fallback, System.Math.Min(fallback, (long)pointerSize)) : null;
    }

    public static FieldAnalysisContext? FindFieldAtOffset(TypeAnalysisContext definition, long targetOffset)
        => FindFieldAtOffset(definition, targetOffset, false);

    public static FieldAnalysisContext? FindStaticFieldAtOffset(TypeAnalysisContext definition, long targetOffset)
        => FindFieldAtOffset(definition, targetOffset, true);

    private static FieldAnalysisContext? FindFieldAtOffset(TypeAnalysisContext definition, long targetOffset, bool isStatic)
    {
        var pointerSize = definition.AppContext.Binary.PointerSizeBytes;

        var offset = isStatic || definition.IsValueType ? 0 : InstanceSize(definition.BaseType, pointerSize);
        foreach (var field in definition.Fields)
        {
            if (field.IsStatic != isStatic)
                continue;

            if (GetSizeAndAlignment(field.FieldType, pointerSize) is not var (size, alignment))
                return null;

            offset = (offset + alignment - 1) & ~(alignment - 1);

            if (offset == targetOffset)
                return field;

            offset += size;
        }

        return null;
    }

    private static long InstanceSize(TypeAnalysisContext? type, int pointerSize)
    {
        if (type == null)
            return 2L * pointerSize;

        if (type is GenericInstanceTypeAnalysisContext genericInstance)
            type = genericInstance.GenericType;

        if (type.Definition?.RawSizes is { instance_size: > 0 } sizes)
            return sizes.instance_size;

        var offset = InstanceSize(type.BaseType, pointerSize);
        foreach (var field in type.Fields.Where(f => !f.IsStatic))
        {
            if (GetSizeAndAlignment(field.FieldType, pointerSize) is not var (size, alignment))
                return offset;
            var metadataOffset = field.BackingData?.FieldOffset ?? field.Offset;
            if (metadataOffset > 0)
                offset = System.Math.Max(offset, metadataOffset + size);
            else
            {
                offset = (offset + alignment - 1) & ~(alignment - 1);
                offset += size;
            }
        }
        return offset;
    }

    private static (long Size, long Alignment)? GetSizeAndAlignment(TypeAnalysisContext fieldType, int pointerSize)
        => GetSizeAndAlignment(fieldType, pointerSize, []);

    private static (long Size, long Alignment)? GetSizeAndAlignment(
        TypeAnalysisContext fieldType, int pointerSize, HashSet<TypeAnalysisContext> activeStructs)
    {
        if (fieldType is GenericInstanceTypeAnalysisContext { GenericType.IsEnumType: true } genericEnum)
            fieldType = genericEnum.GenericType;

        if (fieldType is GenericParameterTypeAnalysisContext genericParameter)
            return genericParameter.IsValueType ? null : (pointerSize, pointerSize);

        if (fieldType is PointerTypeAnalysisContext || !fieldType.IsValueType)
            return (pointerSize, pointerSize);

        if (fieldType.IsEnumType)
            return GetSizeAndAlignment(fieldType.EnumUnderlyingType
                                       ?? fieldType.Fields.FirstOrDefault(f => !f.IsStatic)?.FieldType
                                       ?? fieldType.AppContext.SystemTypes.SystemInt32Type,
                pointerSize, activeStructs);

        return fieldType.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" => (1L, 1L),
            "System.Int16" or "System.UInt16" or "System.Char" => (2L, 2L),
            "System.Int32" or "System.UInt32" or "System.Single" => (4L, 4L),
            "System.Int64" or "System.UInt64" or "System.Double" => (8L, 8L),
            "System.IntPtr" or "System.UIntPtr" => ((long)pointerSize, (long)pointerSize),
            // an arbitrary struct: compute the layout from its instance fields
            _ => GetStructSizeAndAlignment(fieldType, pointerSize, activeStructs),
        };
    }

    // Sequential-layout value type: sum its instance fields with each aligned to min(size, pointer
    // size) and pad the total to the largest member alignment. Generic instances lay out the
    // instantiated field types. Returns null when any member's layout can't be computed.
    private static (long Size, long Alignment)? GetStructSizeAndAlignment(
        TypeAnalysisContext structType, int pointerSize, HashSet<TypeAnalysisContext> activeStructs)
    {
        if (!activeStructs.Add(structType))
            return null;

        var fields = structType is GenericInstanceTypeAnalysisContext instance
            ? instance.GenericType.Fields
                .Where(field => !field.IsStatic)
                .Select(field => (FieldAnalysisContext)new ConcreteGenericFieldAnalysisContext(field, instance))
            : structType.Fields.Where(field => !field.IsStatic);

        long offset = 0;
        long maxAlignment = 1;
        foreach (var field in fields)
        {
            if (GetSizeAndAlignment(field.FieldType, pointerSize, activeStructs) is not var (size, alignment))
            {
                activeStructs.Remove(structType);
                return null;
            }

            offset = (offset + alignment - 1) & ~(alignment - 1);
            offset += size;
            maxAlignment = System.Math.Max(maxAlignment, alignment);
        }

        activeStructs.Remove(structType);
        var structAlignment = System.Math.Min(maxAlignment, pointerSize);
        return ((offset + structAlignment - 1) & ~(structAlignment - 1), structAlignment);
    }
}
