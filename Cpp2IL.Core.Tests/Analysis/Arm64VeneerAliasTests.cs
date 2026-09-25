using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Il2CppApiFunctions;
using Disarm;

namespace Cpp2IL.Core.Tests.Analysis;

// Structural (position-independent) discovery of ARM64 helper veneers:
// single-instruction tail-call veneers and adrp/ldr/(add)/br GOT trampolines.
// Every case runs the same synthetic blob at two different image bases and
// requires identical results after relocation.
public class Arm64VeneerAliasTests
{
    private const uint Ret = 0xd65f03c0;
    private const uint BrX17 = 0xd61f0220;
    private const uint BrX16 = 0xd61f0200;
    private const uint MovX0X1 = 0xaa0103e0;
    private const uint MovX2Xzr = 0xaa1f03e2;
    private const uint StpX30 = 0xa9be5bfd; // stp x30, xzr, [sp, #-0x20]!
    private const uint LdpX30 = 0xa8c15ffe; // ldp x30, x23, [sp], #0x20

    private static uint B(long deltaBytes) => 0x14000000 | (uint)((deltaBytes >> 2) & 0x03ffffff);

    private static uint BCond(long deltaBytes, uint cond) => 0x54000000 | (uint)((deltaBytes >> 2) & 0x7ffff) << 5 | cond;

    private static uint Adrp(int rd, long deltaBytes)
    {
        var imm = deltaBytes >> 12;
        var immlo = (uint)(imm & 0x3);
        var immhi = (uint)((imm >> 2) & 0x7ffff);
        return 0x90000000 | immlo << 29 | immhi << 5 | (uint)rd;
    }

    private static uint Ldr64(int rt, int rn, int byteOffset) =>
        0xf9400000 | (uint)((byteOffset / 8) << 10) | (uint)(rn << 5) | (uint)rt;

    private static uint Add64(int rd, int rn, int imm) =>
        0x91000000 | (uint)(imm << 10) | (uint)(rn << 5) | (uint)rd;

    private static byte[] Blob(uint[] words)
    {
        var bytes = new byte[words.Length * 4];
        for (var i = 0; i < words.Length; i++)
            BitConverter.GetBytes(words[i]).CopyTo(bytes, i * 4);
        return bytes;
    }

    private static List<Arm64Instruction> Disassemble(byte[] blob, ulong va) =>
        Disassembler.Disassemble(blob, va, new Disassembler.Options(true, true, false)).ToList();

    [Test]
    public void TailCallVeneerTargetIsPositionIndependent()
    {
        // veneer entry: b leaf (leaf 0x40 bytes ahead)
        var words = new Dictionary<ulong, uint> { [0x1000] = B(0x40) };
        Assert.That(NewArm64KeyFunctionAddresses.MatchTailCallVeneerTarget(0x1000, a => words[a]), Is.EqualTo(0x1040UL));
        words = new Dictionary<ulong, uint> { [0x801000] = B(0x40) };
        Assert.That(NewArm64KeyFunctionAddresses.MatchTailCallVeneerTarget(0x801000, a => words[a]), Is.EqualTo(0x801040UL));
    }

    [Test]
    public void TailCallVeneerRejectsNonUnconditionalEntries()
    {
        var words = new Dictionary<ulong, uint>
        {
            [0x1000] = Ret,
            [0x1004] = 0x94000002,            // bl
            [0x1008] = BCond(0x10, 0),        // b.eq
            [0x100c] = MovX0X1,
        };
        foreach (var va in words.Keys)
            Assert.That(NewArm64KeyFunctionAddresses.MatchTailCallVeneerTarget(va, a => words[a]), Is.Zero, $"at {va:X}");
    }

    // Blob layout shared by the scan tests. LeafA/LeafB are resolved targets;
    // Unproven is not in the name map and must be rejected.
    private static uint[] ScanBlobWords()
    {
        var words = new uint[0x94 / 4];
        words[0x00 / 4] = Ret;                 // +0x00 end of a prior function
        words[0x04 / 4] = B(0x7c);             // +0x04 veneer -> LeafA @0x80
        words[0x08 / 4] = B(0x7c);             // +0x08 veneer -> LeafB @0x84
        words[0x0c / 4] = MovX2Xzr;            // +0x0c fixup veneer start (arg fixup)
        words[0x10 / 4] = B(0x70);             // +0x10 tail of fixup veneer -> LeafA (not fn start)
        words[0x14 / 4] = StpX30;              // +0x14 real function start
        words[0x18 / 4] = LdpX30;              // +0x18 epilogue
        words[0x1c / 4] = B(0x64);             // +0x1c epilogue tail -> LeafA (not fn start)
        words[0x20 / 4] = B(0x60);             // +0x20 veneer -> LeafA
        words[0x24 / 4] = B(0x6c);             // +0x24 veneer -> Unproven @0x90 (unresolved)
        words[0x28 / 4] = BCond(0x58, 0);      // +0x28 b.eq -> LeafA (conditional)
        words[0x2c / 4] = B(0x58);             // +0x2c -> LeafB, but prev b.eq falls through (not fn start)
        words[0x30 / 4] = Ret;
        words[0x34 / 4] = B(0x50);             // +0x34 veneer -> LeafB
        for (var i = 0x38 / 4; i < 0x80 / 4; i++)
            words[i] = MovX0X1;                // filler
        words[0x80 / 4] = MovX0X1;             // +0x80 LeafA
        words[0x84 / 4] = MovX0X1;             // +0x84 LeafB
        words[0x88 / 4] = MovX0X1;
        words[0x8c / 4] = MovX0X1;
        words[0x90 / 4] = MovX0X1;             // +0x90 Unproven
        return words;
    }

    private static void AssertScanAtBase(ulong @base)
    {
        var disassembly = Disassemble(Blob(ScanBlobWords()), @base);
        var names = new Dictionary<ulong, string>
        {
            [@base + 0x80] = "leaf_a",
            [@base + 0x84] = "leaf_b",
        };
        var aliases = NewArm64KeyFunctionAddresses.FindTailCallVeneerAliases(disassembly, names, new HashSet<ulong>())
            .ToDictionary(kv => kv.Key - @base, kv => kv.Value);

        Assert.That(aliases, Is.EqualTo(new Dictionary<ulong, string>
        {
            [0x04] = "leaf_a",
            [0x08] = "leaf_b",
            [0x20] = "leaf_a",
            [0x34] = "leaf_b",
        }), $"at base {@base:X}");
    }

    [Test]
    public void TailCallVeneerScanIsIdenticalAfterRelocation()
    {
        AssertScanAtBase(0x100000);
        AssertScanAtBase(0x50000000);
    }

    private static uint[] GotVeneerWords(long veneerPageDelta, int slotOffset, bool withAdd) =>
        withAdd
            ? [Adrp(16, veneerPageDelta), Ldr64(17, 16, slotOffset), Add64(16, 16, slotOffset), BrX17]
            : [Adrp(16, veneerPageDelta), Ldr64(17, 16, slotOffset), BrX17];

    private static ulong PageOf(ulong va) => va & ~0xfffUL;

    [TestCase(true)]
    [TestCase(false)]
    public void GotVeneerDecodesSlotAcrossBases(bool withAdd)
    {
        foreach (var veneerVa in new[] { 0x80000UL, 0x7fff000UL })
        {
            // GOT page two pages above the veneer page, slot at +0x38
            var pageDelta = (long)(PageOf(veneerVa) + 0x2000 - PageOf(veneerVa));
            var words = GotVeneerWords(pageDelta, 0x38, withAdd);
            var dict = new Dictionary<ulong, uint>();
            for (var i = 0; i < words.Length; i++)
                dict[veneerVa + (ulong)i * 4] = words[i];

            Assert.That(NewArm64KeyFunctionAddresses.TryDecodeGotVeneerSlot(veneerVa, a => dict[a], out var slot),
                Is.True, $"withAdd={withAdd} at {veneerVa:X}");
            Assert.That(slot, Is.EqualTo(PageOf(veneerVa) + 0x2000 + 0x38));
        }
    }

    [Test]
    public void GotVeneerRejectsNearMatches()
    {
        var veneerVa = 0x80000UL;
        var pageDelta = 0x2000L;
        var cases = new[]
        {
            // ldr bases the wrong register
            new[] { Adrp(16, pageDelta), Ldr64(17, 15, 0x38), Add64(16, 16, 0x38), BrX17 },
            // br jumps the wrong register
            new[] { Adrp(16, pageDelta), Ldr64(17, 16, 0x38), Add64(16, 16, 0x38), BrX16 },
            // missing ldr
            new[] { Adrp(16, pageDelta), Add64(16, 16, 0x38), BrX17, Ret },
            // not an adrp
            new[] { MovX0X1, Ldr64(17, 16, 0x38), Add64(16, 16, 0x38), BrX17 },
            // 32-bit ldr
            new[] { Adrp(16, pageDelta), 0xb9404c11u, Add64(16, 16, 0x38), BrX17 },
        };
        foreach (var words in cases)
        {
            var dict = new Dictionary<ulong, uint>();
            for (var i = 0; i < words.Length; i++)
                dict[veneerVa + (ulong)i * 4] = words[i];
            Assert.That(NewArm64KeyFunctionAddresses.TryDecodeGotVeneerSlot(veneerVa, a => dict[a], out _),
                Is.False, string.Join(",", words.Select(w => w.ToString("x8"))));
        }
    }
}
