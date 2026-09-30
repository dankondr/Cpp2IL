using System;
using System.Collections.Generic;
using System.Linq;

namespace Cpp2IL.Core;

public static class Il2CppClassUsefulOffsets
{
    public const int X86_INTERFACE_OFFSETS_OFFSET = 0x50;
    public const int X86_64_INTERFACE_OFFSETS_OFFSET = 0xB0;

    public static int GetVtableOffset(float metadataVersion, bool is32Bit) =>
        metadataVersion >= 24.2f
            ? is32Bit ? 0x999 /*TODO*/ : 0x138
            : is32Bit ? 0x999 /*TODO*/ : 0x128;

    // Named fields of the Il2CppClass runtime structure, addressed by offset for the metadata
    // version in use. Recognisers must look fields up here, not scatter literals.
    public enum Il2CppClassField
    {
        ElementType,
        InterfaceOffsets,
        StaticFields,
        RgctxData,
        TypeHierarchy,
        CctorFinished,
        InterfaceOffsetsCount,
        TypeHierarchyDepth,
        Flags1,
        Flags2,
    }

    private readonly record struct FieldRow(Il2CppClassField Field, string Name, uint Offset, Type Type, bool Is32Bit, float MinMetadataVersion, float MaxMetadataVersion = float.MaxValue);

    // 64-bit rows. Metadata >= 29 (Unity 2023+/6) inserted fields that pushed cctor_finished to
    // 0xE4 and interface_offsets_count to 0x12E; older versions keep 0xE0/0x12A.
    private static readonly FieldRow[] FieldRows =
    [
        new(Il2CppClassField.ElementType, "elementType", 0x40, typeof(IntPtr), false, 0),
        new(Il2CppClassField.InterfaceOffsets, "interfaceOffsets", 0xB0, typeof(IntPtr), false, 0),
        new(Il2CppClassField.StaticFields, "static_fields", 0xB8, typeof(IntPtr), false, 0),
        new(Il2CppClassField.RgctxData, "rgctx_data", 0xC0, typeof(IntPtr), false, 0),
        new(Il2CppClassField.TypeHierarchy, "typeHierarchy", 0xC8, typeof(IntPtr), false, 0),
        new(Il2CppClassField.CctorFinished, "cctor_finished", 0xE0, typeof(uint), false, 0, 29f),
        new(Il2CppClassField.CctorFinished, "cctor_finished", 0xE4, typeof(uint), false, 29f),
        new(Il2CppClassField.InterfaceOffsetsCount, "interface_offsets_count", 0x12A, typeof(ushort), false, 0, 29f),
        new(Il2CppClassField.InterfaceOffsetsCount, "interface_offsets_count", 0x12E, typeof(ushort), false, 29f),
        new(Il2CppClassField.TypeHierarchyDepth, "typeHierarchyDepth", 0x130, typeof(byte), false, 0),
        new(Il2CppClassField.Flags1, "flags1", 0x132, typeof(byte), false, 0),
        new(Il2CppClassField.Flags2, "flags2", 0x133, typeof(byte), false, 0),

        // 32-bit rows
        new(Il2CppClassField.CctorFinished, "cctor_finished", 0x74, typeof(uint), true, 0),
        new(Il2CppClassField.Flags1, "flags1", 0xBB, typeof(byte), true, 0),
        new(Il2CppClassField.InterfaceOffsets, "interfaceOffsets", X86_INTERFACE_OFFSETS_OFFSET, typeof(IntPtr), true, 0),
        new(Il2CppClassField.StaticFields, "static_fields", 0x5C, typeof(IntPtr), true, 0),
    ];

    /// <summary>
    /// The field read at <paramref name="offset"/> in an Il2CppClass for the given metadata
    /// version, or null when the offset names no modeled field (e.g. inside the vtable).
    /// </summary>
    public static bool TryGetField(uint offset, float metadataVersion, bool is32Bit,
        out Il2CppClassField field, out string name)
    {
        field = default;
        name = null!;
        foreach (var row in FieldRows)
        {
            if (row.Is32Bit != is32Bit || row.Offset != offset
                || metadataVersion < row.MinMetadataVersion || metadataVersion >= row.MaxMetadataVersion)
                continue;
            field = row.Field;
            name = row.Name;
            return true;
        }
        return false;
    }

    public static string? GetOffsetName(uint offset, float metadataVersion, bool is32Bit) =>
        TryGetField(offset, metadataVersion, is32Bit, out _, out var name) ? name : null;

    /// <summary>
    /// The vtable slot an addend refers to: vtable entries are 16-byte VirtualInvokeData pairs at
    /// <see cref="GetVtableOffset"/> + 16 * slot. Null when the addend is before the vtable or not
    /// slot-aligned.
    /// </summary>
    public static int? GetVTableSlot(long addend, float metadataVersion, bool is32Bit)
    {
        var vtableOffset = GetVtableOffset(metadataVersion, is32Bit);
        if (addend < vtableOffset || (addend - vtableOffset) % 16 != 0)
            return null;
        return (int)((addend - vtableOffset) / 16);
    }

    public static readonly List<UsefulOffset> UsefulOffsets =
    [
        new("cctor_finished", 0x74, typeof(uint), true),
        new("flags1", 0xBB, typeof(byte), true),
        //new UsefulOffset("interface_offsets_count", 0x12A, typeof(ushort), true), //TODO
        // new UsefulOffset("rgctx_data", 0xC0, typeof(IntPtr), true), //TODO
        new("interfaceOffsets", X86_INTERFACE_OFFSETS_OFFSET, typeof(IntPtr), true),
        new("static_fields", 0x5C, typeof(IntPtr), true),
        //new UsefulOffset("vtable", 0x138, typeof(IntPtr), true), //TODO

        //64-bit offsets:
        new("elementType", 0x40, typeof(IntPtr), false),
        new("interfaceOffsets", X86_64_INTERFACE_OFFSETS_OFFSET, typeof(IntPtr), false),
        new("static_fields", 0xB8, typeof(IntPtr), false),
        new("rgctx_data", 0xC0, typeof(IntPtr), false),
        new("cctor_finished", 0xE0, typeof(uint), false),
        new("interface_offsets_count", 0x12A, typeof(ushort), false),
        new("flags1", 0x132, typeof(byte), false),
        new("flags2", 0x133, typeof(byte), false),
        new("vtable", 0x138, typeof(IntPtr), false)
    ];

    public static bool IsStaticFieldsPtr(uint offset, bool is32Bit)
    {
        return GetOffsetName(offset, is32Bit) == "static_fields";
    }

    public static bool IsInterfaceOffsetsPtr(uint offset, bool is32Bit)
    {
        return GetOffsetName(offset, is32Bit) == "interfaceOffsets";
    }

    public static bool IsInterfaceOffsetsCount(uint offset, bool is32Bit)
    {
        return GetOffsetName(offset, is32Bit) == "interface_offsets_count";
    }

    public static bool IsRGCTXDataPtr(uint offset, bool is32Bit)
    {
        return GetOffsetName(offset, is32Bit) == "rgctx_data";
    }

    public static bool IsElementTypePtr(uint offset, bool is32Bit)
    {
        return GetOffsetName(offset, is32Bit) == "elementType";
    }

    public static bool IsPointerIntoVtable(uint offset, float metadataVersion, bool is32Bit)
    {
        return offset >= GetVtableOffset(metadataVersion, is32Bit);
    }

    public static string? GetOffsetName(uint offset, bool is32Bit) =>
        UsefulOffsets.FirstOrDefault(o => o.is32Bit == is32Bit && o.offset == offset)?.name;

    public class UsefulOffset(string name, uint offset, Type type, bool is32Bit)
    {
        public string name = name;
        public uint offset = offset;
        public Type type = type;
        public bool is32Bit = is32Bit;
    }
}
