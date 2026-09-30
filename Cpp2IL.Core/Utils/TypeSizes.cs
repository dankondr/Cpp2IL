using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

public static class TypeSizes
{
    // Unboxed size of a value type, so the metadata's boxed size - the two pointer fields in the header. 0 if we
    // don't know (no definition, e.g. an open generic).
    public static long UnboxedSize(TypeAnalysisContext type, int pointerSize)
    {
        var header = 2L * pointerSize;

        var definition = type.Definition;
        if (definition == null && type is GenericInstanceTypeAnalysisContext instance)
            definition = instance.GenericType.Definition;

        if (definition?.RawSizes is { instance_size: var boxed } && boxed > header)
            return boxed - header;

        return 0;
    }

    public static long MinimumUnboxedSize(TypeAnalysisContext type, int pointerSize)
        => MinimumUnboxedSize(type, pointerSize, []);

    private static long MinimumUnboxedSize(TypeAnalysisContext type, int pointerSize,
        HashSet<TypeAnalysisContext> active)
    {
        if (!type.IsValueType)
            return pointerSize;

        var primitive = type.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" => 1,
            "System.Char" or "System.Int16" or "System.UInt16" => 2,
            "System.Int32" or "System.UInt32" or "System.Single" => 4,
            "System.Int64" or "System.UInt64" or "System.Double" or "System.IntPtr" or "System.UIntPtr" => 8,
            _ => 0,
        };
        if (primitive != 0)
            return primitive;

        var exact = UnboxedSize(type, pointerSize);
        if (exact != 0)
            return exact;
        if (!active.Add(type))
            return 0;

        var fields = type is GenericInstanceTypeAnalysisContext instance
            ? instance.GenericType.Fields.Select(field => (FieldAnalysisContext)new ConcreteGenericFieldAnalysisContext(field, instance))
            : type.Fields;
        long total = 0;
        foreach (var field in fields.Where(field => !field.IsStatic))
        {
            var size = MinimumUnboxedSize(field.FieldType, pointerSize, active);
            if (size == 0)
            {
                active.Remove(type);
                return 0;
            }
            total += size;
        }
        active.Remove(type);
        return total;
    }

    // sizeof(T) of a value type as il2cpp lays it out: C struct rules, each field at its
    // natural alignment, the whole padded to the widest one. Metadata carries the exact size of
    // a closed type; a generic instance has none, so its fields (with the arguments bound) are
    // laid out here. 0 when any field's size is unknown.
    public static long LaidOutSize(TypeAnalysisContext type, int pointerSize) => Layout(type, pointerSize, []).Size;

    private static (long Size, long Alignment) Layout(TypeAnalysisContext type, int pointerSize,
        HashSet<TypeAnalysisContext> active)
    {
        if (!type.IsValueType)
            return (pointerSize, pointerSize);
        var primitive = MinimumUnboxedSize(type, pointerSize) is var minimum && type.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" or "System.Char" or "System.Int16" or "System.UInt16"
                or "System.Int32" or "System.UInt32" or "System.Single" or "System.Int64" or "System.UInt64"
                or "System.Double" or "System.IntPtr" or "System.UIntPtr" => true,
            _ => false,
        };
        if (primitive)
            return (minimum, minimum);
        if (!active.Add(type))
            return (0, 1);

        var fields = type is GenericInstanceTypeAnalysisContext instance
            ? instance.GenericType.Fields.Select(field => (FieldAnalysisContext)new ConcreteGenericFieldAnalysisContext(field, instance))
            : type.Fields;
        long offset = 0, alignment = 1;
        foreach (var field in fields.Where(field => !field.IsStatic))
        {
            var (size, fieldAlignment) = Layout(field.FieldType, pointerSize, active);
            if (size == 0)
            {
                active.Remove(type);
                return (0, 1);
            }
            offset = (offset + fieldAlignment - 1) / fieldAlignment * fieldAlignment + size;
            alignment = System.Math.Max(alignment, fieldAlignment);
        }
        active.Remove(type);
        var laidOut = offset == 0 ? 1 : (offset + alignment - 1) / alignment * alignment;
        // A closed type's metadata size is authoritative; the layout only fills in its alignment.
        return (type is GenericInstanceTypeAnalysisContext ? laidOut : UnboxedSize(type, pointerSize) is > 0 and var exact ? exact : laidOut,
            alignment);
    }
}
