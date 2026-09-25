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
}
