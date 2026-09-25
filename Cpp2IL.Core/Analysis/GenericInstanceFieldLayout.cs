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
            var size = TypeSizes.MinimumUnboxedSize(field.FieldType, pointerSize);
            if (size == 0)
                return null;
            var alignment = System.Math.Min(size, pointerSize);
            offset = (offset + alignment - 1) & ~(alignment - 1);
            if (targetOffset >= offset && targetOffset < offset + size)
                return (field, offset, size);
            offset += size;
        }
        return null;
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
    {
        if (fieldType is GenericInstanceTypeAnalysisContext { GenericType.IsEnumType: true } genericEnum)
            fieldType = genericEnum.GenericType;

        // TODO support user-defined value types
        if (fieldType is GenericParameterTypeAnalysisContext genericParameter)
            return genericParameter.IsValueType ? null : (pointerSize, pointerSize);

        if (fieldType is PointerTypeAnalysisContext || !fieldType.IsValueType)
            return (pointerSize, pointerSize);

        if (fieldType.IsEnumType)
            return GetSizeAndAlignment(fieldType.EnumUnderlyingType
                                       ?? fieldType.Fields.FirstOrDefault(f => !f.IsStatic)?.FieldType
                                       ?? fieldType.AppContext.SystemTypes.SystemInt32Type,
                pointerSize);

        return fieldType.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" => (1, 1),
            "System.Int16" or "System.UInt16" or "System.Char" => (2, 2),
            "System.Int32" or "System.UInt32" or "System.Single" => (4, 4),
            "System.Int64" or "System.UInt64" or "System.Double" => (8, 8),
            "System.IntPtr" or "System.UIntPtr" => (pointerSize, pointerSize),
            _ => null // an arbitrary struct needs its own layout computed, bail rather than guess
        };
    }
}
