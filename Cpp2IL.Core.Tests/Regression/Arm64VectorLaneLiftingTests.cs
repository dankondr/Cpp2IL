using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Tests.Regression;

// Regression fixtures for the vector opcodes the r241 re-baseline reported as
// "Instruction X not yet implemented" (castle-recovery#75). Each test feeds raw
// instruction words through the real disassembler and instruction set, then
// asserts the folded lane semantics — which lanes were written, with which
// ops, and which width marks carry the wraparound — not merely that no
// diagnostic was raised.
public class Arm64VectorLaneLiftingTests
{
    private static List<Instruction> Lift(params uint[] words)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Test",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        return new NewArmV8InstructionSet().ConvertInstructions(
            Disassembler.Disassemble(words.SelectMany(BitConverter.GetBytes).ToArray(), 0), context);
    }

    private static Instruction? FindOp(List<Instruction> il, OpCode op, string dest)
        => il.FirstOrDefault(i => i.OpCode == op && i.Operands[0] is Register r && r.Name == dest);

    private static int OpsInto(List<Instruction> il, OpCode op, string dest)
        => il.Count(i => i.OpCode == op && i.Operands[0] is Register r && r.Name == dest);

    private static string Diagnostics(List<Instruction> il)
        => string.Join(" | ", il.Where(i => i.OpCode == OpCode.NotImplemented));

    // USHLL Vd.4S, Vn.4H zero-extends every halfword lane — with a constant
    // source the extension folds to the widened immediate in each S element.
    [Test]
    public void UshllZeroExtendsHalfwordLanes()
    {
        var il = Lift(
            0x0f01a420, // movi v0.4h, #0x21, lsl #8   => each lane 0x2100
            0x2f10a401); // ushll v1.4s, v0.4h, #0

        Assert.Multiple(() =>
        {
            Assert.That(Diagnostics(il), Is.Empty);
            for (var lane = 0; lane < 4; lane++)
            {
                var move = FindOp(il, OpCode.Move, $"V1.S{lane}");
                Assert.That(move, Is.Not.Null);
                Assert.That(move!.Operands[1], Is.EqualTo(new Immediate(0x2100)),
                    $"lane {lane} must hold the zero-extended halfword");
                Assert.That(move.NativeIntegerWidthBits, Is.EqualTo(32));
            }
        });
    }

    // The long shift applies after the extension.
    [Test]
    public void UshllShiftsExtendedLanes()
    {
        var il = Lift(
            0x0f018420, // movi v0.4h, #0x21
            0x2f14a401); // ushll v1.4s, v0.4h, #4

        Assert.Multiple(() =>
        {
            Assert.That(Diagnostics(il), Is.Empty);
            for (var lane = 0; lane < 4; lane++)
                Assert.That(FindOp(il, OpCode.Move, $"V1.S{lane}")?.Operands[1],
                    Is.EqualTo(new Immediate(0x210)),
                    $"lane {lane} folds the extension and shift to 0x21 << 4");
        });
    }

    // SSHLL sign-extends: a 0xFFFF halfword lane becomes -1 in the S lane.
    [Test]
    public void SshllSignExtendsNegativeLanes()
    {
        var il = Lift(
            0x2f00a400, // mvni v0.4h, #0, lsl #8   => each lane 0xFFFF
            0x0f10a402); // sshll v2.4s, v0.4h, #0

        Assert.Multiple(() =>
        {
            Assert.That(Diagnostics(il), Is.Empty);
            for (var lane = 0; lane < 4; lane++)
            {
                var move = FindOp(il, OpCode.Move, $"V2.S{lane}");
                Assert.That(move, Is.Not.Null);
                Assert.That(move!.Operands[1], Is.EqualTo(new Immediate(-1)),
                    $"lane {lane} must hold the sign-extended halfword");
            }
        });
    }

    // USHLL2 reads the high half of the source: a 64-bit MOVI leaves the high
    // half zeroed and proven, so the fold produces zeroed S lanes.
    [Test]
    public void Ushll2ReadsHighSourceLanes()
    {
        var il = Lift(
            0x0f018420, // movi v0.4h, #0x21  — 64-bit form; V0's high half is 0
            0x6f10a401); // ushll2 v1.4s, v0.8h, #0

        Assert.Multiple(() =>
        {
            Assert.That(Diagnostics(il), Is.Empty);
            for (var lane = 0; lane < 4; lane++)
            {
                var move = FindOp(il, OpCode.Move, $"V1.S{lane}");
                Assert.That(move, Is.Not.Null);
                Assert.That(move!.Operands[1], Is.EqualTo(new Immediate(0)));
            }
        });
    }

    // ADDV reduces every lane; four proven lanes produce a three-Add chain.
    [Test]
    public void AddvSumsAllLanesIntoScalar()
    {
        var il = Lift(
            0x4f002621, // movi v1.4s, #0x11, lsl #8   => each lane 0x1100
            0x4eb1b820); // addv s0, v1.4s

        Assert.Multiple(() =>
        {
            Assert.That(Diagnostics(il), Is.Empty);
            // constant lanes fold all the way: 0x1100 * 4 = 0x4400
            Assert.That(FindOp(il, OpCode.Move, "V0.S0")?.Operands[1],
                Is.EqualTo(new Immediate(0x4400)));
        });

        // opaque-but-proven lanes keep the explicit reduction chain
        var opaque = Lift(
            0x4e041d01, // mov v1.s[0], w8
            0x4e0c1d21, // mov v1.s[1], w9
            0x4e141d41, // mov v1.s[2], w10
            0x4e1c1d61, // mov v1.s[3], w11
            0x4eb1b820); // addv s0, v1.4s
        Assert.Multiple(() =>
        {
            Assert.That(Diagnostics(opaque), Is.Empty);
            Assert.That(opaque.Count(i => i.OpCode == OpCode.Add), Is.EqualTo(3),
                "four lanes fold to three adds");
            Assert.That(FindOp(opaque, OpCode.Move, "V0.S0"), Is.Not.Null);
        });
        Assert.That(opaque.Where(i => i.OpCode == OpCode.Add)
            .All(i => i.NativeIntegerWidthBits == 32), Is.True,
            "lane adds keep the 32-bit wraparound");
    }

    // UMINV keeps unsigned order on zero-extended lanes: min(a,b) emits
    // b ^ ((a^b) & -(a<b)) per step.
    [Test]
    public void UminvReducesByteLanes()
    {
        var il = Lift(
            0x0f00e784, // movi v4.8b, #0x1c
            0x2e31a884); // uminv b4, v4.8b

        Assert.Multiple(() =>
        {
            Assert.That(Diagnostics(il), Is.Empty);
            Assert.That(il.Count(i => i.OpCode == OpCode.CheckLess), Is.EqualTo(7),
                "eight lanes fold to seven compare steps");
            Assert.That(FindOp(il, OpCode.Move, "V4.B0"), Is.Not.Null);
        });
    }

    // A reduction over an opaque vector cannot name the remaining addends — it
    // must stay an explicit diagnostic, not a partial fold.
    [Test]
    public void AddvOnUnprovenLanesStaysDiagnosed()
    {
        var il = Lift(
            0x4e041d00, // mov v0.s[0], w8 — proves element 0 only
            0x4eb1b801); // addv s1, v0.4s   — lanes 1..3 are opaque

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.True);
            Assert.That(FindOp(il, OpCode.Move, "V1.S0"), Is.Null,
                "an unproven reduction must not fabricate a scalar lane");
        });
    }

    // FMAXNM V2.2S: each proven lane calls the managed Max.
    [Test]
    public void FmaxnmVectorFormCallsMaxPerLane()
    {
        var il = Lift(
            0x0f00f420, // fmov v0.2s, #2.125
            0x0f01f421, // fmov v1.2s, #8.5
            0x0e21c402); // fmaxnm v2.2s, v0.2s, v1.2s

        Assert.Multiple(() =>
        {
            Assert.That(Diagnostics(il), Is.Empty);
            Assert.That(il.Any(i => i.OpCode == OpCode.Call
                && i.Operands[1] is Register { Name: "V2.S0" }), Is.True);
            Assert.That(il.Any(i => i.OpCode == OpCode.Call
                && i.Operands[1] is Register { Name: "V2.S1" }), Is.True);
        });
    }

    // USHR is a logical shift: `shr` plus a mask clearing the fill bits — the
    // emitted CIL `shr` is arithmetic and would sign-extend an unsigned lane.
    [Test]
    public void UshrMasksFillBitsOn32BitLanes()
    {
        var il = Lift(
            0x0f046406, // movi v6.2s, #0x80, lsl #24  => lane 0x80000000
            0x2f3f04c3); // ushr v3.2s, v6.2s, #1

        var mask = il.Where(i => i.OpCode == OpCode.And
            && i.Operands[0] is Register { Name: { } n } && n.StartsWith("V3.S")
            && i.Operands[2] is Immediate { Value: 0x7FFFFFFF }).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(Diagnostics(il), Is.Empty);
            Assert.That(FindOp(il, OpCode.ShiftRight, "V3.S0"), Is.Not.Null);
            Assert.That(mask.Count, Is.EqualTo(2),
                "each lane's arithmetic shr must be masked back to logical");
        });
    }

    // CMGE Vd.T, Vn.T, #0: per-lane CheckGreaterOrEqual negated to all-ones.
    [Test]
    public void CmgeEmitsPerLaneMask()
    {
        var opaque = Lift(0x6ea08821); // cmge v1.4s, v1.4s, #0 — never written
        Assert.That(opaque.Any(i => i.OpCode == OpCode.NotImplemented), Is.True);

        var il = Lift(
            0x4f002621, // movi v1.4s, #0x11, lsl #8
            0x6ea08821); // cmge v1.4s, v1.4s, #0

        Assert.Multiple(() =>
        {
            Assert.That(Diagnostics(il), Is.Empty);
            for (var lane = 0; lane < 4; lane++)
            {
                Assert.That(FindOp(il, OpCode.CheckGreaterOrEqual, $"V1.S{lane}"), Is.Not.Null);
                Assert.That(FindOp(il, OpCode.Negate, $"V1.S{lane}"), Is.Not.Null,
                    "the mask lane must negate the compare's 0/1 to all-ones");
            }
        });
    }

    // ST1 single-element form: a proven lane moves to memory at element size.
    [Test]
    public void St1ElementStoreWritesProvenLane()
    {
        var il = Lift(
            0x4f000620, // movi v0.4s, #0x11
            0x4d009140); // st1 v0.s[3], [x10]

        var store = il.FirstOrDefault(i => i.OpCode == OpCode.Move
            && i.Operands[0] is MemoryOperand);
        Assert.Multiple(() =>
        {
            Assert.That(Diagnostics(il), Is.Empty);
            Assert.That(store, Is.Not.Null);
            Assert.That(store!.NativeMemoryAccessSize, Is.EqualTo(4));
            Assert.That(store.Operands[1], Is.EqualTo(new Immediate(0x11)),
                "lane 3 of the constant vector stores as the lane value");
        });
    }

    // XTN writes the truncated low halves into the narrow destination's lanes.
    [Test]
    public void XtnTruncatesIntoDestinationLanes()
    {
        var il = Lift(
            0x4f010422, // movi v2.4s, #0x21  => lanes 0x21
            0x0e612840); // xtn v0.4h, v2.4s

        Assert.Multiple(() =>
        {
            Assert.That(Diagnostics(il), Is.Empty);
            // two truncated halfword lanes pack into each 32-bit window
            Assert.That(FindOp(il, OpCode.Move, "V0.S0")?.Operands[1],
                Is.EqualTo(new Immediate(0x00210021)));
            Assert.That(FindOp(il, OpCode.Move, "V0.S1")?.Operands[1],
                Is.EqualTo(new Immediate(0x00210021)));
        });
    }

    // A proven vector MOV materializes per-window copies so a later write to
    // the source register cannot fabricate stale lanes in the copy.
    [Test]
    public void VectorMovCopiesIntoDestinationLanes()
    {
        var il = Lift(
            0x4f000620, // movi v0.4s, #0x11
            0x4ea01c05); // mov v5.16b, v0.16b

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.Move
                && i.Operands[0] is Register { Name: "V5" }
                && i.Operands[1] is Register { Name: "V0" }), Is.True);
            Assert.That(FindOp(il, OpCode.Move, "V5.S0"), Is.Not.Null);
            Assert.That(FindOp(il, OpCode.Move, "V5.S3"), Is.Not.Null);
            Assert.That(Diagnostics(il), Is.Empty);
        });
    }

    // MVN vector: bitwise NOT per 32-bit window.
    [Test]
    public void VectorMvnFoldsWindows()
    {
        var il = Lift(
            0x4f000620, // movi v0.4s, #0x11
            0x6e205800); // mvn v0.16b, v0.16b

        Assert.Multiple(() =>
        {
            Assert.That(Diagnostics(il), Is.Empty);
            Assert.That(FindOp(il, OpCode.Not, "V0.S0"), Is.Not.Null);
            Assert.That(FindOp(il, OpCode.Not, "V0.S3"), Is.Not.Null);
        });
    }

    // USHL: the variable per-lane shift — the sign of each count lane's low
    // byte selects truncating left vs masked logical right, both emitted and
    // merged with a branchless mask.
    [Test]
    public void UshlEmitsBranchlessLaneShift()
    {
        var il = Lift(
            0x0f010400, // movi v0.2s, #0x20
            0x0f010408, // movi v8.2s, #0x20
            0x2ea84400); // ushl v0.2s, v0.2s, v8.2s

        Assert.Multiple(() =>
        {
            Assert.That(Diagnostics(il), Is.Empty);
            Assert.That(il.Any(i => i.OpCode == OpCode.ShiftLeft
                && i.Operands[0] is Register r && r.Name.StartsWith("TEMP_VEC")), Is.True);
            Assert.That(il.Any(i => i.OpCode == OpCode.ShiftRight
                && i.Operands[0] is Register r && r.Name.StartsWith("TEMP_VEC")), Is.True);
            Assert.That(il.Count(i => i.OpCode == OpCode.CheckLess), Is.GreaterThanOrEqualTo(2));
            Assert.That(FindOp(il, OpCode.Move, "V0.S0"), Is.Not.Null);
            Assert.That(FindOp(il, OpCode.Move, "V0.S1"), Is.Not.Null);
        });
    }

    // SSHL on an opaque source reports rather than guessing.
    [Test]
    public void SshlOnOpaqueSourceIsDiagnosed()
    {
        var il = Lift(
            0x0f010400, // movi v0.2s, #0x20
            0x0ea14441); // sshl v1.2s, v2.2s, v1.2s — v1/v2 were never written

        Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.True);
    }

    // SMIN folds to the branchless select per lane.
    [Test]
    public void SminEmitsLaneSelect()
    {
        var il = Lift(
            0x0f010400, // movi v0.2s, #0x20
            0x0f010421, // movi v1.2s, #0x21
            0x0ea16c01); // smin v1.2s, v0.2s, v1.2s

        Assert.Multiple(() =>
        {
            Assert.That(Diagnostics(il), Is.Empty);
            Assert.That(il.Count(i => i.OpCode == OpCode.CheckLess), Is.GreaterThanOrEqualTo(2));
            Assert.That(FindOp(il, OpCode.Move, "V1.S0"), Is.Not.Null);
        });
    }

    // An unproven USHLL stays an explicit diagnostic and writes no lanes.
    [Test]
    public void UnprovenUshllIsDiagnosedNotGuessed()
    {
        var il = Lift(
            0x4e041d00, // mov v0.s[0], w8 — proves slot 0 only
            0x2f08a401); // ushll v1.8h, v0.8b, #0 — reads B lanes 0..7

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.True);
            Assert.That(il.Any(i => i.OpCode == OpCode.Move
                && i.Operands[0] is Register { Name: { } n } && n.StartsWith("V1.")), Is.False);
        });
    }
}
