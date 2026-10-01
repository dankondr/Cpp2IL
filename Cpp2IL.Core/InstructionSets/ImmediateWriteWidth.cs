using System;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.InstructionSets;

/// <summary>
/// Applies a register write's width marks to an immediate operand, resolving
/// it to the value and proven byte count the write actually proved.
/// </summary>
internal static class ImmediateWriteWidth
{
    // A Move's write-width mark caps both the bytes the immediate may claim
    // and the value it carries: an S or W write keeps only its own bytes of
    // the source, and a lane destination claims only its lane. Only the
    // bytes the write produced are recorded; a wider slot read of a narrower
    // write stays diagnosed - zero-extension is not the slot's bytes.
    public static void ApplyToMove(Instruction move)
    {
        var writeBits = move.NativeFloatWriteBits ?? move.NativeIntegerWidthBits;
        if (writeBits is not { } bits || move.Operands[1] is not Immediate immediate)
            return;
        move.SetOperand(1, ForWrite(immediate, bits,
            move.Operands[0] is Register destination ? destination.Name : null));
    }

    public static Immediate ForWrite(Immediate immediate, int writeBits, string? destinationName)
    {
        var writeBytes = writeBits / 8;
        var extent = Math.Min(writeBytes, LaneExtentBytes(destinationName) ?? writeBytes);
        var filled = Math.Min(immediate.EffectiveProvenBytes, extent);
        // Keep the write's low bytes, sign-extended back to the long: a lane
        // that spelled -1 reads -1 whatever its width.
        var masked = writeBytes < 8
            ? (immediate.Value << (64 - writeBytes * 8)) >> (64 - writeBytes * 8)
            : immediate.Value;
        return masked == immediate.Value && filled == immediate.EffectiveProvenBytes
            ? immediate
            : new(masked, filled);
    }

    // "V0.S1"-style lane names denote a window of the register, not the whole
    // register: the letter after the dot is the lane extent in bytes.
    private static int? LaneExtentBytes(string? registerName) =>
        registerName is { } name && name.IndexOf('.') is >= 0 and var dot && dot + 1 < name.Length
            ? name[dot + 1] switch { 'B' => 1, 'H' => 2, 'S' => 4, 'D' => 8, _ => null }
            : null;
}
