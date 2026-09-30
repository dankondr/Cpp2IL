using System.Collections.Generic;
using LibCpp2IL.Elf;
using Xunit;

namespace LibCpp2ILTests;

// Regression tests for the .eh_frame_hdr / .eh_frame / .gcc_except_table reader
// (castle-recovery#206): a hand-assembled unwind layout, virtual addresses equal
// to file offsets so pc-relative values are easy to reason about.
public class ElfEhTablesTests
{
    private const ulong Hdr = 0x1000, Frame = 0x2000, Except = 0x3000;

    private static void U32(byte[] file, int offset, uint value)
    {
        file[offset] = (byte)value;
        file[offset + 1] = (byte)(value >> 8);
        file[offset + 2] = (byte)(value >> 16);
        file[offset + 3] = (byte)(value >> 24);
    }

    private static void S32(byte[] file, int offset, int value) => U32(file, offset, (uint)value);

    private static int Uleb(byte[] file, int offset, ulong value)
    {
        do
        {
            var b = (byte)(value & 0x7F);
            value >>= 7;
            file[offset++] = (byte)(b | (value != 0 ? 0x80 : 0));
        } while (value != 0);
        return offset;
    }

    // One frame record: length-prefixed payload.
    private static int Record(byte[] file, int offset, params byte[] payload)
    {
        U32(file, offset, (uint)payload.Length);
        payload.CopyTo(file, offset + 4);
        return offset + 4 + payload.Length;
    }

    private static List<byte> Concat(params object[] parts)
    {
        var list = new List<byte>();
        foreach (var part in parts)
            switch (part)
            {
                case byte b: list.Add(b); break;
                case string s: foreach (var c in s) list.Add((byte)c); break;
                case byte[] a: list.AddRange(a); break;
            }
        return list;
    }

    // CIE with version 1, code align 1, data align -4, return register 30.
    private static byte[] Cie(string augmentation, params byte[] augmentationData)
    {
        var body = Concat((byte)0, (byte)0, (byte)0, (byte)0, (byte)1, augmentation, (byte)0,
            (byte)1, (byte)0x78, (byte)30);
        if (augmentation.StartsWith("z"))
        {
            body.Add((byte)augmentationData.Length);
            body.AddRange(augmentationData);
        }
        return body.ToArray();
    }

    private static byte[] Fde(uint cieDistanceBack, int pcBegin, int pcRange, params byte[] augmentationData)
    {
        var body = new List<byte>
        {
            (byte)cieDistanceBack, (byte)(cieDistanceBack >> 8), (byte)(cieDistanceBack >> 16), (byte)(cieDistanceBack >> 24),
            (byte)pcBegin, (byte)(pcBegin >> 8), (byte)(pcBegin >> 16), (byte)(pcBegin >> 24),
            (byte)pcRange, (byte)(pcRange >> 8), (byte)(pcRange >> 16), (byte)(pcRange >> 24),
        };
        if (augmentationData.Length > 0)
        {
            body.Add((byte)augmentationData.Length);
            body.AddRange(augmentationData);
        }
        else
        {
            body.Add(0);
        }
        return body.ToArray();
    }

    // Builds the three-section layout: a plain function, a function whose LSDA omits the
    // landing base (defaults to the function start) and a function with an explicit one.
    private static (byte[] File, List<ElfSectionHeaderEntry> Sections) Build(byte tableEncoding = 0x3B)
    {
        var file = new byte[0x3100];

        var frame = (int)Frame;
        var ciePlain = frame;
        frame = Record(file, frame, Cie("zR", (byte)0x1B));
        var cieLsda = frame;
        frame = Record(file, frame, Cie("zRPL", (byte)0x1B, (byte)0x9B, (byte)0, (byte)0, (byte)0, (byte)0, (byte)0x1B));

        var fde1 = frame;
        frame = Record(file, frame, Fde((uint)(fde1 + 4 - ciePlain),
            (int)(0x8000 - (fde1 + 8)), 0x40));

        var fde2 = frame;
        var fde2Lsda = fde2 + 4 + 4 + 4 + 4 + 1; // cie off + pc begin + range + aug len
        frame = Record(file, frame, Fde((uint)(fde2 + 4 - cieLsda),
            (int)(0x8100 - (fde2 + 8)), 0x50,
            (byte)(Except - (ulong)fde2Lsda), (byte)((Except - (ulong)fde2Lsda) >> 8), (byte)((Except - (ulong)fde2Lsda) >> 16), (byte)((Except - (ulong)fde2Lsda) >> 24)));

        var fde3 = frame;
        var fde3Lsda = fde3 + 4 + 4 + 4 + 4 + 1;
        var lsda2 = (int)Except + 0x40;
        frame = Record(file, frame, Fde((uint)(fde3 + 4 - cieLsda),
            (int)(0x8200 - (fde3 + 8)), 0x30,
            (byte)((ulong)lsda2 - (ulong)fde3Lsda), (byte)(((ulong)lsda2 - (ulong)fde3Lsda) >> 8), (byte)(((ulong)lsda2 - (ulong)fde3Lsda) >> 16), (byte)(((ulong)lsda2 - (ulong)fde3Lsda) >> 24)));

        // LSDA 1: landing base omitted (= function start 0x8100), no type table, uleb call sites.
        // Three rows, the last with pad 0 - it must be filtered out.
        var cursor = (int)Except;
        file[cursor++] = 0xFF; // landing-pad base encoding: omit
        file[cursor++] = 0xFF; // type-table encoding: omit
        file[cursor++] = 0x01; // call-site encoding: uleb128
        var lengthAt = cursor++;
        var entriesStart = cursor;
        foreach (var (start, size, pad, action) in new (ulong, ulong, ulong, ulong)[]
        {
            (0x00, 0x10, 0x20, 1), (0x10, 0x08, 0x20, 2), (0x18, 0x04, 0x00, 0),
        })
        {
            cursor = Uleb(file, cursor, start);
            cursor = Uleb(file, cursor, size);
            cursor = Uleb(file, cursor, pad);
            cursor = Uleb(file, cursor, action);
        }
        file[lengthAt] = (byte)(cursor - entriesStart);

        // LSDA 2: explicit sdata4 landing base 0x8080, a type-table base, udata4 call sites.
        cursor = lsda2;
        file[cursor++] = 0x0B;
        U32(file, cursor, 0x8080);
        cursor += 4;
        file[cursor++] = 0x9B;
        cursor = Uleb(file, cursor, 0);
        file[cursor++] = 0x03;
        lengthAt = cursor++;
        entriesStart = cursor;
        U32(file, cursor, 0x10); U32(file, cursor + 4, 0x20); U32(file, cursor + 8, 0x38);
        cursor += 12;
        cursor = Uleb(file, cursor, 1);
        file[lengthAt] = (byte)(cursor - entriesStart);

        // .eh_frame_hdr: version 1, pcrel sdata4 frame pointer, udata4 count, datarel sdata4 table.
        var hdr = (int)Hdr;
        file[hdr] = 1;
        file[hdr + 1] = 0x1B;
        file[hdr + 2] = 0x03;
        file[hdr + 3] = tableEncoding;
        S32(file, hdr + 4, (int)(Frame - (Hdr + 4)));
        U32(file, hdr + 8, 3);
        var table = hdr + 12;
        foreach (var fde in new[] { fde1, fde2, fde3 })
        {
            S32(file, table, 0); // initial location: ignored, the FDE's pc_begin wins
            S32(file, table + 4, (int)((ulong)fde - Hdr));
            table += 8;
        }

        var sections = new List<ElfSectionHeaderEntry>
        {
            new() { Name = ".eh_frame_hdr", VirtualAddress = Hdr, RawAddress = Hdr, Size = (ulong)(table - hdr) },
            new() { Name = ".eh_frame", VirtualAddress = Frame, RawAddress = Frame, Size = (ulong)frame - Frame },
            new() { Name = ".gcc_except_table", VirtualAddress = Except, RawAddress = Except, Size = (ulong)cursor - Except },
        };
        return (file, sections);
    }

    [Fact]
    public void ReadsFunctionsCallSitesAndLandingPads()
    {
        var (file, sections) = Build();

        var functions = ElfEhTables.Read(file, sections);

        Assert.NotNull(functions);
        Assert.Equal(3, functions!.Count);

        Assert.Equal(0x40UL, functions[0x8000].Size);
        Assert.Empty(functions[0x8000].CallSites);

        var withPads = functions[0x8100];
        Assert.Equal(0x50UL, withPads.Size);
        Assert.Equal(2, withPads.CallSites.Count); // the pad-0 call-site row is not a landing pad
        Assert.Equal(0x8100UL, withPads.CallSites[0].Start);
        Assert.Equal(0x10UL, withPads.CallSites[0].Length);
        Assert.Equal(0x8120UL, withPads.CallSites[0].LandingPad);
        Assert.Equal(1UL, withPads.CallSites[0].Action);
        Assert.Equal(0x8110UL, withPads.CallSites[1].Start);
        Assert.Equal(0x8120UL, withPads.CallSites[1].LandingPad);
        Assert.Equal(2UL, withPads.CallSites[1].Action);

        var explicitBase = functions[0x8200];
        Assert.Single(explicitBase.CallSites);
        Assert.Equal(0x8210UL, explicitBase.CallSites[0].Start);
        Assert.Equal(0x80B8UL, explicitBase.CallSites[0].LandingPad); // 0x8080 landing base + 0x38
    }

    [Fact]
    public void MissingEhFrameHdrReturnsNull()
    {
        var (file, sections) = Build();
        sections.RemoveAt(0);

        Assert.Null(ElfEhTables.Read(file, sections));
    }

    [Fact]
    public void NoSectionsReturnsNull()
    {
        var (file, _) = Build();

        Assert.Null(ElfEhTables.Read(file, new List<ElfSectionHeaderEntry>()));
    }

    [Fact]
    public void UnsupportedTableEncodingReturnsNull()
    {
        // A non-datarel-sdata4 lookup table is not the layout this reader supports.
        var (file, sections) = Build(tableEncoding: 0x00);

        Assert.Null(ElfEhTables.Read(file, sections));
    }
}
