using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using LibCpp2IL.Logging;

namespace LibCpp2IL.Elf;

/// <summary>
/// Reads the DWARF unwind tables of an ELF image: <c>.eh_frame_hdr</c> lists every function's
/// frame description entry, each FDE in <c>.eh_frame</c> gives the function's true extent and
/// may point at an LSDA in <c>.gcc_except_table</c> whose call-site table names the landing
/// pads - the code only the unwinder enters (catch and finally handlers, cleanups).
/// </summary>
public static class ElfEhTables
{
    private const byte DwEhPeOmit = 0xFF;

    /// <summary>
    /// Parses the unwind tables and returns them keyed by function start (virtual address).
    /// Returns null when the binary has no such sections or the header table uses an encoding
    /// other than datarel sdata4 (the only layout linkers emit), in which case the binary is
    /// treated as if it carried no unwind information.
    /// </summary>
    public static IReadOnlyDictionary<ulong, EhFunctionInfo>? Read(
        ReadOnlySpan<byte> fileContents,
        IReadOnlyList<ElfSectionHeaderEntry> sections,
        bool is32Bit = false)
    {
        var sectionsByName = new Dictionary<string, ElfSectionHeaderEntry>();
        foreach (var section in sections)
            if (section.Name is { } name)
                sectionsByName[name] = section;

        if (!sectionsByName.TryGetValue(".eh_frame_hdr", out var headerSection))
            return null;

        // All the mappings the parser needs: named sections with a load address.
        var maps = sections
            .Where(s => s.VirtualAddress != 0 && s.Size != 0)
            .Select(s => (s.VirtualAddress, s.RawAddress, s.Size))
            .OrderBy(s => s.VirtualAddress)
            .ToList();

        long FileOffset(ulong address)
        {
            // Binary search the section map for the section containing the address.
            var lo = 0;
            var hi = maps.Count - 1;
            while (lo <= hi)
            {
                var mid = (lo + hi) / 2;
                var (vaddr, raw, size) = maps[mid];
                if (address < vaddr)
                    hi = mid - 1;
                else if (address >= vaddr + size)
                    lo = mid + 1;
                else
                    return (long)raw + (long)(address - vaddr);
            }

            throw new InvalidDataException($"No ELF section contains virtual address 0x{address:X}");
        }

        var file = fileContents;
        var headerOffset = checked((int)headerSection.RawAddress);
        var headerEnd = headerOffset + (int)Math.Min(headerSection.Size, int.MaxValue);
        if (headerOffset + 4 > file.Length)
            return null;

        var pointerEncoding = file[headerOffset + 1];
        var countEncoding = file[headerOffset + 2];
        var tableEncoding = file[headerOffset + 3];
        if (tableEncoding != 0x3B) // datarel sdata4
            return null;

        var pos = headerOffset + 4;
        (_, pos) = ReadEncoded(file, pos, pointerEncoding, headerSection.VirtualAddress + 4, is32Bit);
        var (fdeCountRaw, tablePos) = ReadEncoded(file, pos, countEncoding, headerSection.VirtualAddress + (ulong)(pos - headerOffset), is32Bit);
        var fdeCount = (long)fdeCountRaw;

        // The binary-search table is count pairs of signed 32-bit datarel offsets relative to
        // .eh_frame_hdr; the first column (the function's own start) is superseded by the FDE's
        // own pc_begin and ignored here, same as the reference reader.
        var capacity = (headerEnd - (int)tablePos) / 8;
        if (fdeCount > capacity)
        {
            LibLogger.VerboseNewline($"[EhTables] .eh_frame_hdr declares {fdeCount} entries but only {capacity} fit in the section; clamping.");
            fdeCount = capacity;
        }

        var cies = new Dictionary<ulong, (string Augmentation, byte LsdaEncoding, byte FdeEncoding)>();

        var result = new Dictionary<ulong, EhFunctionInfo>((int)Math.Min(fdeCount, int.MaxValue));
        var skipped = 0;
        for (var index = 0; index < fdeCount; index++)
        {
            try
            {
                var fde = (ulong)ReadI32(file, (int)tablePos + 8 * index + 4) + headerSection.VirtualAddress;
                var position = checked((int)FileOffset(fde));

                var (augmentation, lsdaEncoding, fdeEncoding) = ReadCie(file, FileOffset, fde + 4 - ReadU32(file, position + 4), cies, is32Bit);
                // A CIE without an 'R' augmentation letter gives no FDE encoding; the pointers
                // are then plain pointer-size absolute values.
                var fdePtrEncoding = fdeEncoding == DwEhPeOmit ? (byte)0x00 : fdeEncoding;
                var (start, cursor) = ReadEncoded(file, position + 8, fdePtrEncoding, fde + 8, is32Bit);
                var (size, sizeEnd) = ReadEncoded(file, cursor, (byte)(fdePtrEncoding & 0x0F), 0, is32Bit);

                ulong lsda = 0;
                if (augmentation.StartsWith("z") && lsdaEncoding != DwEhPeOmit)
                {
                    var (augmentationLength, lsdaPos) = ReadUleb(file, sizeEnd);
                    if (augmentationLength != 0)
                        (lsda, _) = ReadEncoded(file, lsdaPos, lsdaEncoding, fde + (ulong)(lsdaPos - position), is32Bit);
                }

                var entry = new EhFunctionInfo { Start = start, Size = size };
                if (lsda != 0)
                    ReadCallSites(file, checked((int)FileOffset(lsda)), lsda, start, is32Bit, FileOffset, entry.CallSites);
                result[start] = entry;
            }
            catch (Exception e) when (e is InvalidDataException or ArgumentOutOfRangeException or IndexOutOfRangeException or OverflowException)
            {
                skipped++;
            }
        }

        if (skipped > 0)
            LibLogger.VerboseNewline($"[EhTables] Skipped {skipped} malformed frame entries.");

        return result;
    }

    private static (string Augmentation, byte LsdaEncoding, byte FdeEncoding) ReadCie(
        ReadOnlySpan<byte> file,
        Func<ulong, long> fileOffset,
        ulong address,
        Dictionary<ulong, (string, byte, byte)> cies,
        bool is32Bit = false)
    {
        if (cies.TryGetValue(address, out var cached))
            return cached;

        var position = checked((int)fileOffset(address)) + 9; // length + id + version
        var end = file.Slice(position).IndexOf((byte)0);
        if (end < 0)
            throw new InvalidDataException("CIE augmentation string is unterminated");
        end += position;
        var augmentation = Encoding.ASCII.GetString(file.Slice(position, end - position).ToArray());
        position = end + 1;

        // code alignment, data alignment, return address register
        (_, position) = ReadUleb(file, position);
        (_, position) = ReadSleb(file, position);
        (_, position) = ReadUleb(file, position);

        byte lsdaEncoding = DwEhPeOmit, fdeEncoding = DwEhPeOmit;
        if (augmentation.StartsWith("z"))
        {
            (_, position) = ReadUleb(file, position); // augmentation data length
            foreach (var letter in augmentation[1..])
                switch (letter)
                {
                    case 'P':
                        (_, position) = ReadEncoded(file, position + 1, file[position], 0, is32Bit);
                        break;
                    case 'L':
                        lsdaEncoding = file[position];
                        position++;
                        break;
                    case 'R':
                        fdeEncoding = file[position];
                        position++;
                        break;
                }
        }

        var result = (augmentation, lsdaEncoding, fdeEncoding);
        cies[address] = result;
        return result;
    }

    private static void ReadCallSites(ReadOnlySpan<byte> file, int offset, ulong lsda, ulong functionStart, bool is32Bit, Func<ulong, long> fileOffset, List<EhCallSiteInfo> sites)
    {
        var lsdaOffset = offset;
        var landingBase = functionStart;
        var encoding = file[offset++];
        if (encoding != DwEhPeOmit)
            (landingBase, offset) = ReadEncoded(file, offset, encoding, 0, is32Bit);

        var typeEncoding = file[offset++];
        var typeBase = 0;
        if (typeEncoding != DwEhPeOmit)
        {
            var (distance, after) = ReadUleb(file, offset);
            offset = after;
            typeBase = checked(after + (int)distance);
        }

        encoding = file[offset++];
        var (tableLength, cursor) = ReadUleb(file, offset);
        var end = cursor + (int)tableLength;
        while (cursor < end)
        {
            ulong start, size, pad;
            (start, cursor) = ReadEncoded(file, cursor, encoding, 0, is32Bit);
            (size, cursor) = ReadEncoded(file, cursor, encoding, 0, is32Bit);
            (pad, cursor) = ReadEncoded(file, cursor, encoding, 0, is32Bit);
            var (action, after) = ReadUleb(file, cursor);
            cursor = after;
            if (pad != 0)
                sites.Add(new EhCallSiteInfo(functionStart + start, size, landingBase + pad, action)
                {
                    Actions = ReadActions(file, end, action, typeBase, typeEncoding,
                        lsda, lsdaOffset, is32Bit, fileOffset)
                });
        }
    }

    private static IReadOnlyList<EhActionInfo>? ReadActions(ReadOnlySpan<byte> file, int tableStart,
        ulong action, int typeBase, byte typeEncoding, ulong lsda, int lsdaOffset,
        bool is32Bit, Func<ulong, long> fileOffset)
    {
        if (action == 0)
            return [new EhActionInfo(0, null)];
        try
        {
            var cursor = checked(tableStart + (int)action - 1);
            var visited = new HashSet<int>();
            var result = new List<EhActionInfo>();
            // A malformed action chain must not consume arbitrary following LSDAs.
            while (visited.Add(cursor) && visited.Count <= 64)
            {
                if (cursor < tableStart || typeBase != 0 && cursor >= typeBase) return null;
                var (filter, nextField) = ReadSleb(file, cursor);
                var (next, _) = ReadSleb(file, nextField);
                ulong? typeInfo = null;
                if (filter > 0 && typeBase != 0)
                {
                    var width = (typeEncoding & 0x0F) switch
                    {
                        0 => is32Bit ? 4 : 8,
                        2 or 0x0A => 2,
                        3 or 0x0B => 4,
                        4 or 0x0C => 8,
                        _ => 0,
                    };
                    if (width == 0)
                        return null;
                    var position = checked(typeBase - (int)filter * width);
                    var address = lsda + (ulong)(position - lsdaOffset);
                    // A zero RTTI entry denotes catch-all, even with pcrel/indirect encoding.
                    var (raw, _) = ReadEncoded(file, position, (byte)(typeEncoding & 0x0F), 0, is32Bit);
                    if (raw == 0)
                        typeInfo = 0;
                    else
                    {
                        var (value, _) = ReadEncoded(file, position, typeEncoding, address, is32Bit);
                        if ((typeEncoding & 0x80) != 0)
                        {
                            var pointer = checked((int)fileOffset(value));
                            value = is32Bit ? ReadU32(file, pointer) : ReadU64(file, pointer);
                        }
                        typeInfo = value;
                    }
                }
                result.Add(new EhActionInfo(filter, typeInfo));
                if (next == 0)
                    return result;
                cursor = checked(nextField + (int)next);
                if (cursor < tableStart)
                    return null;
            }
        }
        catch (Exception e) when (e is InvalidDataException or ArgumentOutOfRangeException or IndexOutOfRangeException or OverflowException)
        {
            // Keep the call-site and its unproven-pad diagnostic when only its actions fail.
        }
        return null;
    }

    private static (ulong, int) ReadEncoded(ReadOnlySpan<byte> file, int offset, byte encoding, ulong address, bool is32Bit)
    {
        if (encoding == DwEhPeOmit)
            return (0, offset);

        ulong value;
        int end;
        switch (encoding & 0x0F)
        {
            case 0x01:
                (value, end) = ReadUleb(file, offset);
                break;
            case 0x09:
                (var signed, end) = ReadSleb(file, offset);
                value = (ulong)signed;
                break;
            case 0x00:
                value = is32Bit ? ReadU32(file, offset) : ReadU64(file, offset);
                end = offset + (is32Bit ? 4 : 8);
                break;
            case 0x04:
                value = ReadU64(file, offset);
                end = offset + 8;
                break;
            case 0x02:
                value = ReadU16(file, offset);
                end = offset + 2;
                break;
            case 0x03:
                value = ReadU32(file, offset);
                end = offset + 4;
                break;
            case 0x0A:
                value = (ulong)(short)ReadU16(file, offset);
                end = offset + 2;
                break;
            case 0x0B:
                value = (ulong)ReadI32(file, offset);
                end = offset + 4;
                break;
            case 0x0C:
                value = ReadU64(file, offset);
                end = offset + 8;
                break;
            default:
                throw new InvalidDataException($"Unsupported DW_EH_PE form 0x{encoding & 0x0F:X} in unwind table");
        }

        // Only pcrel (relative to the field's own address), absptr and aligned are produced by
        // linkers in these records; indirect, datarel and funcrel are not expected.
        if ((encoding & 0x70) == 0x10)
            value += address;
        else if ((encoding & 0x70) is not 0 and not 0x50)
            throw new InvalidDataException($"Unsupported DW_EH_PE application 0x{encoding & 0x70:X} in unwind table");

        return (value, end);
    }

    private static (ulong, int) ReadUleb(ReadOnlySpan<byte> file, int offset)
    {
        ulong result = 0;
        var shift = 0;
        while (true)
        {
            var b = file[offset++];
            result |= (ulong)(b & 0x7F) << shift;
            shift += 7;
            if ((b & 0x80) == 0)
                return (result, offset);
        }
    }

    private static (long, int) ReadSleb(ReadOnlySpan<byte> file, int offset)
    {
        long result = 0;
        var shift = 0;
        while (true)
        {
            var b = file[offset++];
            result |= (long)(b & 0x7F) << shift;
            shift += 7;
            if ((b & 0x80) == 0)
                return ((b & 0x40) != 0 ? result - (1L << shift) : result, offset);
        }
    }

    private static ushort ReadU16(ReadOnlySpan<byte> file, int offset) => BinaryPrimitives.ReadUInt16LittleEndian(file.Slice(offset));

    private static uint ReadU32(ReadOnlySpan<byte> file, int offset) => BinaryPrimitives.ReadUInt32LittleEndian(file.Slice(offset));

    private static int ReadI32(ReadOnlySpan<byte> file, int offset) => BinaryPrimitives.ReadInt32LittleEndian(file.Slice(offset));

    private static ulong ReadU64(ReadOnlySpan<byte> file, int offset) => BinaryPrimitives.ReadUInt64LittleEndian(file.Slice(offset));
}
