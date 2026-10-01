using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Tests.Isil;

public class Arm64VectorScalarizerTests
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

    private static bool IsMove(Instruction i, string dest, string src)
        => i.OpCode == OpCode.Move && i.Operands[0] is Register d && d.Name == dest
            && i.Operands[1] is Register s && s.Name == src;

    private static Instruction? FindOp(List<Instruction> il, OpCode op, string dest)
        => il.FirstOrDefault(i => i.OpCode == op && i.Operands[0] is Register r && r.Name == dest);

    [Test]
    public void DupBroadcastFeedsScalarLanes()
    {
        // w8 = 0x811c9dc6 broadcast over both S lanes; add lanes; extract lane 1.
        var il = Lift(
            0x5293b8c8, // mov w8, #0x9dc6
            0x72b02388, // movk w8, #0x811c, lsl #16
            0x0e040d02, // dup v2.2s, w8
            0x0ea28443, // add v3.2s, v2.2s, v2.2s
            0x0e0c3c48); // mov w8, v2.s[1]

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
            Assert.That(il.Any(i => IsMove(i, "V2.S0", "X8")), Is.True);
            Assert.That(il.Any(i => IsMove(i, "V2.S1", "X8")), Is.True);
            Assert.That(FindOp(il, OpCode.Add, "V3.S0"), Is.Not.Null);
            Assert.That(FindOp(il, OpCode.Add, "V3.S1"), Is.Not.Null);
            Assert.That(il.Any(i => IsMove(i, "X8", "V2.S1")), Is.True);
        });
        // the folded add must retain 32-bit wraparound
        Assert.That(FindOp(il, OpCode.Add, "V3.S0")!.NativeIntegerWidthBits, Is.EqualTo(32));
    }

    [Test]
    public void DupBroadcast64FeedsDoubleLanes()
    {
        var il = Lift(
            0x4e080d02, // dup v2.2d, x8
            0x4ee28442, // add v2.2d, v2.2d, v2.2d
            0x4e083c48); // mov x8, v2.d[0]

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
            Assert.That(il.Any(i => IsMove(i, "V2.D0", "X8")), Is.True);
            Assert.That(il.Any(i => IsMove(i, "V2.D1", "X8")), Is.True);
            Assert.That(il.Any(i => IsMove(i, "X8", "V2.D0")), Is.True);
        });
        var add = FindOp(il, OpCode.Add, "V2.D0");
        Assert.That(add, Is.Not.Null);
        Assert.Multiple(() =>
        {
            Assert.That(add!.NativeIntegerWidthBits, Is.Null); // 64-bit lanes are not truncated to 32
            Assert.That(add.Operands[1], Is.EqualTo(new Register(null, "V2.D0")));
        });
    }

    [Test]
    public void BroadcastXorMultiplyHashSequenceFolds()
    {
        // Shaped after a vectorized scalar hash: broadcast constant, mask, xor,
        // multiply at 32-bit wraparound, then extract the high lane.
        var il = Lift(
            0x1e270101, // fmov s1, w8
            0x4e0c1c01, // mov v1.s[1], w0
            0x2f00e620, // movi d0, #0x0000_00ff_0000_00ff
            0x5293b8c8, // mov w8, #0x9dc6
            0x72b02388, // movk w8, #0x811c, lsl #16       => w8 = 0x811c9dc6
            0x0e040d02, // dup v2.2s, w8
            0x52803248, // mov w8, #0x192
            0x72a02008, // movk w8, #0x0100, lsl #16       => w8 = 0x01000192
            0x0e040d04, // dup v4.2s, w8
            0x0e201c23, // and v3.8b, v1.8b, v0.8b
            0x2e221c62, // eor v2.8b, v3.8b, v2.8b
            0x0ea49c42, // mul v2.2s, v2.2s, v4.2s
            0x0e0c3c48); // mov w8, v2.s[1]

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False,
                $"diagnostics: {string.Join(" | ", il.Where(i => i.OpCode == OpCode.NotImplemented))}");
            Assert.That(FindOp(il, OpCode.And, "V3.S0"), Is.Not.Null);
            Assert.That(FindOp(il, OpCode.Xor, "V2.S0"), Is.Not.Null);
            Assert.That(FindOp(il, OpCode.Xor, "V2.S1"), Is.Not.Null);
            Assert.That(il.Any(i => IsMove(i, "X8", "V2.S1")), Is.True);
        });
        var mul = FindOp(il, OpCode.Multiply, "V2.S0");
        Assert.That(mul, Is.Not.Null);
        Assert.That(mul!.NativeIntegerWidthBits, Is.EqualTo(32)); // wraps mod 2^32 like the vector op
    }

    [Test]
    public void BroadcastBoundaryValueWrapsAtLaneWidth()
    {
        // 0xffffffff * 0xffffffff wraps to 1 at 32-bit width — the folded
        // multiply must keep the 32-bit seed so downstream typing wraps too.
        var il = Lift(
            0x12800008, // mov w8, #0xffffffff
            0x0e040d02, // dup v2.2s, w8
            0x0e040d04, // dup v4.2s, w8
            0x0ea49c42); // mul v2.2s, v2.2s, v4.2s

        var mul = FindOp(il, OpCode.Multiply, "V2.S0");
        Assert.That(mul, Is.Not.Null);
        Assert.That(mul!.NativeIntegerWidthBits, Is.EqualTo(32));
        Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
    }

    [Test]
    public void UnequalLanesAreNotCollapsed()
    {
        // v0.s0 = w8 via fmov, v0.s1 = w1 via ins: distinct values in distinct
        // lanes must fold lane-wise, not collapse into a broadcast.
        var il = Lift(
            0x1e270100, // fmov s0, w8
            0x4e0c1c20, // mov v0.s[1], w1
            0x0ea08403); // add v3.2s, v0.2s, v0.2s

        var lo = FindOp(il, OpCode.Add, "V3.S0");
        var hi = FindOp(il, OpCode.Add, "V3.S1");
        Assert.Multiple(() =>
        {
            Assert.That(lo, Is.Not.Null);
            Assert.That(hi, Is.Not.Null);
            Assert.That(((Register)lo!.Operands[1]).Name, Is.EqualTo("V0"));
            Assert.That(((Register)hi!.Operands[1]).Name, Is.EqualTo("V0.S1"));
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        });
    }

    [Test]
    public void SingleStructureLoadProvesLanes()
    {
        // A single-structure LD1 materializes every element as a lane local,
        // so a later extract reads the loaded lane rather than guessing it.
        var il = Lift(
            0x0e040d00, // dup v0.2s, w8
            0x4c407880, // ld1 {v0.4s}, [x4]
            0x0e0c3c08); // mov w8, v0.s[1]

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.Move
                && i.Operands[0] is Register { Name: "V0.S1" }
                && i.Operands[1] is MemoryOperand { Base: Register { Name: "X4" }, Addend: 4 }), Is.True);
            Assert.That(il.Any(i => IsMove(i, "X8", "V0.S1")), Is.True,
                "the extract reads the lane local the load materialized");
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        });
    }

    [Test]
    public void PartiallyWrittenVectorReadsEntryLanes()
    {
        // lane 0 was never written in the method — before any merge or
        // clobber it still carries the value v2 was entered with, so the add
        // reads the entry lane (the register local) rather than diagnosing
        var il = Lift(
            0x4e0c1d02, // mov v2.s[1], w8
            0x0ea28440); // add v0.2s, v2.2s, v2.2s

        Assert.Multiple(() =>
        {
            Assert.That(FindOp(il, OpCode.Add, "V0.S1"), Is.Not.Null);
            Assert.That(il.Any(i => i.OpCode == OpCode.Add
                && i.Operands[0] is Register { Name: "V0.S0" }
                && i.Operands[1] is Register { Name: "V2" }), Is.True,
                "the unwritten lane is the entry scalar — the register local");
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        });
    }

    [Test]
    public void WholeVectorLoadProvesLanes()
    {
        // A plainly offset-addressed q-load materializes every 32-bit window
        // as an element local, so lane-wise math on loaded vectors folds to
        // scalar ops on real locals instead of a diagnostic.
        var il = Lift(
            0x3dc00100, // ldr v0, [x8]
            0x3dc00121, // ldr v1, [x9]
            0x0ea18402); // add v2.2s, v0.2s, v1.2s

        var lo = FindOp(il, OpCode.Add, "V2.S0");
        var hi = FindOp(il, OpCode.Add, "V2.S1");
        Assert.Multiple(() =>
        {
            Assert.That(lo, Is.Not.Null);
            Assert.That(hi, Is.Not.Null);
            Assert.That(((Register)lo!.Operands[1]).Name, Is.EqualTo("V0.S0"));
            Assert.That(((Register)hi!.Operands[1]).Name, Is.EqualTo("V0.S1"));
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        });
    }

    [Test]
    public void ReloadedRegisterStoresFieldsAgain()
    {
        // Two 8-byte copies through d0, each a pair of 4-byte fields. Every
        // reload re-materializes the register's windows as element locals, so
        // the second store copies the second value's lanes — not a stale lane
        // of the first.
        var il = Lift(
            0xfd402520, // ldr d0, [x9, #0x48]
            0xfc024260, // stur d0, [x19, #0x24]
            0xfd402500, // ldr d0, [x8, #0x48]
            0xfd001a60); // str d0, [x19, #0x30]

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.ShiftRight), Is.False, () => string.Join("\n", il));
            Assert.That(il.Any(i => i.OpCode == OpCode.Move
                && i.Operands[0] is Register { Name: "V0.S0" }
                && i.Operands[1] is MemoryOperand { Base: Register { Name: "X8" }, Addend: 0x48 }), Is.True);
            Assert.That(il.Any(i => i.OpCode == OpCode.Move
                && i.Operands[0] is Register { Name: "V0.S1" }
                && i.Operands[1] is MemoryOperand { Base: Register { Name: "X8" }, Addend: 0x4C }), Is.True);
            Assert.That(il.Any(i => i.OpCode == OpCode.Move
                && i.Operands[0] is MemoryOperand { Base: Register { Name: "X19" }, Addend: 0x30 }
                && i.Operands[1] is Register { Name: "V0.S0" }), Is.True);
            Assert.That(il.Any(i => i.OpCode == OpCode.Move
                && i.Operands[0] is MemoryOperand { Base: Register { Name: "X19" }, Addend: 0x34 }
                && i.Operands[1] is Register { Name: "V0.S1" }), Is.True);
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        });
    }

    [Test]
    public void StackVectorLoadProvesLanes()
    {
        // A stack-addressed q-load materializes the same window locals through
        // StackOffset operands, so extracts read real provenance.
        var il = Lift(
            0x3dc003e0, // ldr v0, [x31]
            0x0e0c3c08); // mov w8, v0.s[1]

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => IsMove(i, "X8", "V0.S1")), Is.True);
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        });
    }

    [Test]
    public void FullyOpaqueVectorKeepsNormalPath()
    {
        // v1 is never written and the post-indexed ldr v0 has no lane
        // provenance: the fold must not fire and the caller's whole-register
        // path runs unchanged.
        var il = Lift(
            0x3cc01500, // ldr v0, [x8], #0x1
            0x0e201c23, // and v3.8b, v1.8b, v0.8b
            0x0e0c3c28); // mov w8, v1.s[1]

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.And
                && i.Operands[0] is Register r && r.Name == "V3"), Is.True);
            Assert.That(il.Any(i => IsMove(i, "X8", "V1.S1")), Is.True);
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        });
    }

    [Test]
    public void PermutedVectorScalarizes()
    {
        // zip1 interleaves lanes: v2 = [v1.s0, v2.s0] — each destination lane
        // names a proven source lane, so a later extract reads the element local
        var il = Lift(
            0x0e040d02, // dup v2.2s, w8
            0x0e823822, // zip1 v2.2s, v1.2s, v2.2s
            0x0e0c3c48); // mov w8, v2.s[1]

        Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        Assert.That(il.Any(i => IsMove(i, "X8", "V2.S1")), Is.True);
    }

    [Test]
    public void DupOfElementBroadcastsTheSourceLane()
    {
        // dup v0.4s, v9.s[2]: v9 is opaque, so the broadcast reads its element
        // local — but every produced lane is still proven (each equals that source).
        var il = Lift(0x4e140520);

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
            for (var lane = 0; lane < 4; lane++)
                Assert.That(il.Any(i => IsMove(i, $"V0.S{lane}", "V9.S2")), Is.True);
        });
    }

    [Test]
    public void SmovSignExtendsToWideDestination()
    {
        var il = Lift(
            0x0e040d00, // dup v0.2s, w8
            0x4e0c2c08); // smov x8, v0.s[1]

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.SignExtend32
                && i.Operands[0] is Register r && r.Name == "X8"
                && i.Operands[1] is Register s && s.Name == "V0.S1"), Is.True);
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        });
    }

    [Test]
    public void MergeOfWrittenAndEntryEdgesStaysUnproven()
    {
        // A lane merged from two predecessors: the CBZ edge never wrote V0 so
        // its lane 1 is only the entry value — it can name the element local
        // V0.S1 only if that local is defined at method entry, which is a
        // lane:types-ssa question — while the B edge wrote it via DUP. The
        // merge cannot express that phi, so the window stays unproven and the
        // extract diagnoses rather than guessing.
        var entryBranch = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.CBZ);
            Set(m, "Address", (ulong)0);
            Set(m, "Op0Kind", Arm64OperandKind.Register);
            Set(m, "Op0Reg", Arm64Register.W9);
            Set(m, "Op1Imm", (long)16); // target = Address + Op1Imm = 16
        });
        var dup = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.DUP);
            Set(m, "Address", (ulong)4);
            Set(m, "Op0Kind", Arm64OperandKind.Register);
            Set(m, "Op0Reg", Arm64Register.V0);
            Set(m, "Op0Arrangement", Arm64ArrangementSpecifier.TwoS);
            Set(m, "Op1Kind", Arm64OperandKind.Register);
            Set(m, "Op1Reg", Arm64Register.W8);
        });
        var branch = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.B);
            Set(m, "Address", (ulong)8);
            Set(m, "Op0Kind", Arm64OperandKind.ImmediatePcRelative);
            Set(m, "Op0Imm", (long)8); // BranchTarget = Address + Op0Imm = 16
        });
        var extract = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.MOV);
            Set(m, "Address", (ulong)16);
            Set(m, "Op0Kind", Arm64OperandKind.Register);
            Set(m, "Op0Reg", Arm64Register.W8);
            Set(m, "Op1Kind", Arm64OperandKind.VectorRegisterElement);
            Set(m, "Op1Reg", Arm64Register.V0);
            Set(m, "Op1VectorElement", new Arm64VectorElement(Arm64VectorElementWidth.S, 1));
        });

        var emitted = new List<Instruction>();
        Instruction Add(ulong address, OpCode opCode, List<IOperand> operands)
        {
            var insn = new Instruction(emitted.Count, opCode, operands);
            emitted.Add(insn);
            return insn;
        }
        Func<Arm64Instruction, int, IOperand> conv = (_, _) => new Register(null, "X8");

        var scalarizer = new Arm64VectorScalarizer();
        scalarizer.Begin([entryBranch, dup, branch, extract]);
        scalarizer.BeginInstruction(entryBranch, Add);
        scalarizer.TryBroadcastDup(dup, Add, conv);
        scalarizer.BeginInstruction(branch, Add);
        scalarizer.BeginInstruction(extract, Add); // merge target: V0.S1 meets an unwritten edge
        Assert.Multiple(() =>
        {
            Assert.That(scalarizer.TryConvert(extract, Add, conv), Is.True,
                "an unproven merge lane is diagnosed, not left to guess");
            Assert.That(emitted.Any(i => i.OpCode == OpCode.NotImplemented
                && i.Operands[0] is StringLiteral s && s.Value.Contains("unproven")), Is.True);
            Assert.That(emitted.Any(i => i.OpCode == OpCode.Move
                && i.Operands[1] is Register { Name: "V0.S1" }), Is.False);
        });
    }

    [Test]
    public void UshrFoldsOnManualFixture()
    {
        // Disarm does not yet decode shift-right-by-immediate (Task 1), so the
        // pass is exercised on a hand-built instruction instead.
        var dup = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.DUP);
            Set(m, "Op0Kind", Arm64OperandKind.Register);
            Set(m, "Op0Reg", Arm64Register.V2);
            Set(m, "Op0Arrangement", Arm64ArrangementSpecifier.TwoS);
            Set(m, "Op1Kind", Arm64OperandKind.Register);
            Set(m, "Op1Reg", Arm64Register.W8);
        });
        var ushr = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.USHR);
            Set(m, "Address", (ulong)4);
            Set(m, "Op0Kind", Arm64OperandKind.Register);
            Set(m, "Op0Reg", Arm64Register.V3);
            Set(m, "Op0Arrangement", Arm64ArrangementSpecifier.TwoS);
            Set(m, "Op1Kind", Arm64OperandKind.Register);
            Set(m, "Op1Reg", Arm64Register.V2);
            Set(m, "Op2Kind", Arm64OperandKind.Immediate);
            Set(m, "Op2Imm", (long)24);
        });

        var emitted = new List<Instruction>();
        Instruction Add(ulong address, OpCode opCode, List<IOperand> operands)
        {
            var insn = new Instruction(emitted.Count, opCode, operands);
            emitted.Add(insn);
            return insn;
        }

        var scalarizer = new Arm64VectorScalarizer();
        scalarizer.Begin([]);
        scalarizer.TryBroadcastDup(dup, Add, (_, _) => new Register(null, "X8"));
        scalarizer.BeginInstruction(ushr, Add);
        Assert.That(scalarizer.TryConvert(ushr, Add, (_, _) => throw new InvalidOperationException()), Is.True);

        Assert.Multiple(() =>
        {
            Assert.That(FindOp(emitted, OpCode.ShiftRight, "V3.S0"), Is.Not.Null);
            Assert.That(FindOp(emitted, OpCode.ShiftRight, "V3.S1"), Is.Not.Null);
            Assert.That(emitted.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        });
        var shr = FindOp(emitted, OpCode.ShiftRight, "V3.S0")!;
        Assert.Multiple(() =>
        {
            Assert.That(shr.Operands[1], Is.EqualTo(new Register(null, "V2.S0")));
            Assert.That(shr.Operands[2], Is.EqualTo(new Immediate(24)));
            Assert.That(shr.NativeIntegerWidthBits, Is.EqualTo(32));
        });
    }

    [Test]
    public void IndirectCallClobbersVectorProvenance()
    {
        // An indirect call clobbers the argument/temporary vector registers
        // and writes its result to v0: lane state from before the call must
        // not fold the following lane op.
        var il = Lift(
            0x0e040d00, // dup v0.2s, w8
            0xd63f0100, // blr x8
            0x0ea08401, // add v1.2s, v0.2s, v0.2s
            0xd65f03c0);

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => IsMove(i, "V0.S0", "X8")), Is.True, "dup folded before the call");
            Assert.That(FindOp(il, OpCode.Add, "V1.S0"), Is.Null, "stale v0 lanes must not be reused");
            Assert.That(FindOp(il, OpCode.Add, "V1"), Is.Not.Null, "falls back to the whole-register op");
        });
    }

    [Test]
    public void DirectCallClobbersVectorProvenance()
    {
        // A direct BL has no indirect target to enumerate, but it clobbers the
        // same argument/temporary registers: NoteUnhandled must drop lane
        // state before the following instruction converts.
        var dup = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.DUP);
            Set(m, "Op0Kind", Arm64OperandKind.Register);
            Set(m, "Op0Reg", Arm64Register.V0);
            Set(m, "Op0Arrangement", Arm64ArrangementSpecifier.TwoS);
            Set(m, "Op1Kind", Arm64OperandKind.Register);
            Set(m, "Op1Reg", Arm64Register.W8);
        });
        var call = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.BL);
            Set(m, "Address", (ulong)4);
            Set(m, "Op0Kind", Arm64OperandKind.ImmediatePcRelative);
            Set(m, "Op0Imm", (long)0x14);
        });
        var add = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.ADD);
            Set(m, "Address", (ulong)8);
            Set(m, "Op0Kind", Arm64OperandKind.Register);
            Set(m, "Op0Reg", Arm64Register.V1);
            Set(m, "Op0Arrangement", Arm64ArrangementSpecifier.TwoS);
            Set(m, "Op1Kind", Arm64OperandKind.Register);
            Set(m, "Op1Reg", Arm64Register.V0);
            Set(m, "Op2Kind", Arm64OperandKind.Register);
            Set(m, "Op2Reg", Arm64Register.V0);
        });

        var emitted = new List<Instruction>();
        Instruction Add(ulong address, OpCode opCode, List<IOperand> operands)
        {
            var insn = new Instruction(emitted.Count, opCode, operands);
            emitted.Add(insn);
            return insn;
        }
        Func<Arm64Instruction, int, IOperand> conv = (_, _) => new Register(null, "X8");

        var scalarizer = new Arm64VectorScalarizer();
        scalarizer.Begin([dup, call, add]);
        scalarizer.TryBroadcastDup(dup, Add, conv);
        scalarizer.BeginInstruction(call, Add);
        scalarizer.NoteUnhandled(call);
        scalarizer.BeginInstruction(add, Add); // BL just invalidated every tracked lane
        Assert.That(scalarizer.TryConvert(add, Add, conv), Is.False,
            "the consumer after a direct call must fall back, not reuse stale v0 lanes");
    }

    [Test]
    public void UndecodedInstructionClobbersVectorProvenance()
    {
        // An undecoded word may write any vector register (the real USHLL in
        // the hash routines rewrites v3), so it invalidates all lane state.
        var dup = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.DUP);
            Set(m, "Op0Kind", Arm64OperandKind.Register);
            Set(m, "Op0Reg", Arm64Register.V0);
            Set(m, "Op0Arrangement", Arm64ArrangementSpecifier.TwoS);
            Set(m, "Op1Kind", Arm64OperandKind.Register);
            Set(m, "Op1Reg", Arm64Register.W8);
        });
        var undecoded = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.UNIMPLEMENTED);
            Set(m, "Address", (ulong)4);
        });
        var add = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.ADD);
            Set(m, "Address", (ulong)8);
            Set(m, "Op0Kind", Arm64OperandKind.Register);
            Set(m, "Op0Reg", Arm64Register.V1);
            Set(m, "Op0Arrangement", Arm64ArrangementSpecifier.TwoS);
            Set(m, "Op1Kind", Arm64OperandKind.Register);
            Set(m, "Op1Reg", Arm64Register.V0);
            Set(m, "Op2Kind", Arm64OperandKind.Register);
            Set(m, "Op2Reg", Arm64Register.V0);
        });

        var emitted = new List<Instruction>();
        Instruction Add(ulong address, OpCode opCode, List<IOperand> operands)
        {
            var insn = new Instruction(emitted.Count, opCode, operands);
            emitted.Add(insn);
            return insn;
        }
        Func<Arm64Instruction, int, IOperand> conv = (_, _) => new Register(null, "X8");

        var scalarizer = new Arm64VectorScalarizer();
        scalarizer.Begin([dup, undecoded, add]);
        scalarizer.TryBroadcastDup(dup, Add, conv);
        scalarizer.BeginInstruction(undecoded, Add);
        scalarizer.NoteUnhandled(undecoded); // Op0Kind None — unidentifiable destination
        scalarizer.BeginInstruction(add, Add);
        Assert.That(scalarizer.TryConvert(add, Add, conv), Is.False,
            "the consumer after an undecoded word must fall back, not reuse stale v0 lanes");
    }

    [Test]
    public void ElementOperandBroadcastsProvenScalar()
    {
        // FMUL Vd.2S, Vn.2S, Vm.S[0] multiplies every lane by one element: the
        // element reads the scalar the caller left in the register local.
        var il = Lift(
            0x0e040d23, // dup v3.2s, w9
            0x1e270104, // fmov s4, w8
            0x0f849063); // fmul v3.2s, v3.2s, v4.s[0]

        var lo = FindOp(il, OpCode.Multiply, "V3.S0");
        var hi = FindOp(il, OpCode.Multiply, "V3.S1");
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
            Assert.That(lo, Is.Not.Null);
            Assert.That(hi, Is.Not.Null);
            Assert.That(lo!.Operands[2], Is.EqualTo(new Register(null, "V4")));
            Assert.That(hi!.Operands[2], Is.EqualTo(new Register(null, "V4")));
        });
    }

    [Test]
    public void MergedLaneFromTwoPredecessorsFeedsPackedMultiply()
    {
        // A vector register is a tuple of lanes: two paths build V0/V2
        // differently (a DUP broadcast versus an LDR D pair), and the FMUL
        // below the merge still lifts as one scalar multiply per lane.
        // Lane 0's canonical home is the register local itself — its low
        // 32 bits are the lane and the field-recovery layer resolves a
        // whole-register read as that window — so the merged lane-0 op
        // reads V0/V2 while lane 1 reads the element locals V0.S1/V2.S1.
        var il = Lift(
            0x34000088, // cbz w8, #0x10        -> else-path
            0x0e040d00, // dup v0.2s, w8         then: broadcast
            0x0e040d02, // dup v2.2s, w8
            0x54000061, // b.ne #0x18            -> merge (ConditionalJump, not a tail call)
            0xfd400100, // ldr d0, [x8]          else: two floats
            0xfd400902, // ldr d2, [x8, #0x10]
            0x2e22dc00, // fmul v0.2s, v0.2s, v2.2s   merge: both preds prove V0/V2
            0xfd000100); // str d0, [x8]

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
            var lo = FindOp(il, OpCode.Multiply, "V0.S0");
            var hi = FindOp(il, OpCode.Multiply, "V0.S1");
            Assert.That(lo, Is.Not.Null);
            Assert.That(hi, Is.Not.Null);
            Assert.That(lo!.Operands[1], Is.EqualTo(new Register(null, "V0")));
            Assert.That(lo.Operands[2], Is.EqualTo(new Register(null, "V2")));
            Assert.That(hi!.Operands[1], Is.EqualTo(new Register(null, "V0.S1")));
            Assert.That(hi.Operands[2], Is.EqualTo(new Register(null, "V2.S1")));
        });
    }

    [Test]
    public void InsAndDupFeedPackedDivide()
    {
        // INS copies one element across registers, DUP broadcasts an element
        // over a register, and the packed FDIV reads each lane's value.
        var il = Lift(
            0xfd400100, // ldr d0, [x8]
            0xfd400902, // ldr d2, [x8, #0x10]
            0xfd401101, // ldr d1, [x8, #0x20]
            0xfd401903, // ldr d3, [x8, #0x30]
            0x6e0c0462, // mov v2.s[1], v3.s[0]
            0x0e040420, // dup v0.2s, v1.s[0]
            0x2e20fc40, // fdiv v0.2s, v2.2s, v0.2s
            0xfd000100); // str d0, [x8]

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
            Assert.That(il.Any(i => IsMove(i, "V2.S1", "V3.S0")), Is.True); // INS
            Assert.That(il.Any(i => IsMove(i, "V0.S0", "V1.S0")), Is.True); // DUP
            Assert.That(il.Any(i => IsMove(i, "V0.S1", "V1.S0")), Is.True);
            var lo = FindOp(il, OpCode.Divide, "V0.S0");
            var hi = FindOp(il, OpCode.Divide, "V0.S1");
            Assert.That(lo, Is.Not.Null);
            Assert.That(hi, Is.Not.Null);
            Assert.That(lo!.Operands[1], Is.EqualTo(new Register(null, "V2.S0")));
            Assert.That(lo.Operands[2], Is.EqualTo(new Register(null, "V0.S0")));
            Assert.That(hi!.Operands[1], Is.EqualTo(new Register(null, "V2.S1")));
            Assert.That(hi.Operands[2], Is.EqualTo(new Register(null, "V0.S1")));
        });
    }

    [Test]
    public void DoubleLoadStoresFieldsNotShift()
    {
        // LDR D + STUR D copies two adjacent float fields: the load
        // materializes each 32-bit window as its element local, so the store
        // writes the fields one per lane instead of shifting the register.
        var il = Lift(
            0xfd402520, // ldr d0, [x9, #0x48]
            0xfc024260); // stur d0, [x19, #0x24]

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
            Assert.That(il.Any(i => i.OpCode == OpCode.ShiftRight), Is.False,
                "a D store must not materialize its high float by shifting");
            var lo = il.FirstOrDefault(i => i.OpCode == OpCode.Move
                && i.Operands[0] is MemoryOperand { Addend: 0x24 }
                && i.Operands[1] is Register { Name: "V0.S0" });
            var hi = il.FirstOrDefault(i => i.OpCode == OpCode.Move
                && i.Operands[0] is MemoryOperand { Addend: 0x28 }
                && i.Operands[1] is Register { Name: "V0.S1" });
            Assert.That(lo, Is.Not.Null);
            Assert.That(hi, Is.Not.Null);
        });
    }

    [Test]
    public void PermutesMoveLanesIntoElementLocals()
    {
        // EXT/ZIP/UZP/TRN/REV are pure permutations: each destination lane is a
        // verbatim copy of one source lane.
        var il = Lift(
            0x3dc00101, // ldr q1, [x8]
            0x3dc00502, // ldr q2, [x8, #0x10]
            0x6e026024, // ext v4.16b, v1.16b, v2.16b, #0xc -> [v1.s3, v2.s0..s2]
            0x4e823826, // zip1 v6.4s, v1.4s, v2.4s          -> [v1.s0, v2.s0, v1.s1, v2.s1]
            0x4e82184c, // uzp1 v12.4s, v2.4s, v2.4s        -> [v2.s0, v2.s2, v2.s0, v2.s2]
            0x4ea0082a); // rev64 v10.4s, v1.4s             -> [v1.s1, v1.s0, v1.s3, v1.s2]

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
            Assert.That(il.Any(i => IsMove(i, "V4.S0", "V1.S3")), Is.True); // EXT
            Assert.That(il.Any(i => IsMove(i, "V4.S1", "V2.S0")), Is.True);
            Assert.That(il.Any(i => IsMove(i, "V6.S0", "V1.S0")), Is.True); // ZIP1
            Assert.That(il.Any(i => IsMove(i, "V6.S1", "V2.S0")), Is.True);
            Assert.That(il.Any(i => IsMove(i, "V12.S0", "V2.S0")), Is.True); // UZP1
            Assert.That(il.Any(i => IsMove(i, "V12.S1", "V2.S2")), Is.True);
            Assert.That(il.Any(i => IsMove(i, "V10.S0", "V1.S1")), Is.True); // REV64
            Assert.That(il.Any(i => IsMove(i, "V10.S1", "V1.S0")), Is.True);
        });
    }

    [Test]
    public void ReplicateLoadBroadcastsEveryLane()
    {
        // LD1R loads one element into every lane: one memory read feeds each
        // element local.
        var il = Lift(
            0x4d40c900, // ld1r {v0.4s}, [x8]
            0xfd000100); // str d0, [x8]

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
            for (var lane = 0; lane < 4; lane++)
                Assert.That(il.Any(i => i.OpCode == OpCode.Move
                    && i.Operands[0] is Register { Name: var n } && n == $"V0.S{lane}"
                    && i.Operands[1] is MemoryOperand { Addend: 0 }), Is.True,
                    $"lane {lane} must read the same memory");
        });
    }

    [Test]
    public void StructureLoadMaterializesLanes()
    {
        // LD1 (multiple structures) is a contiguous fill: register k's window
        // j reads mem + k*regBytes + 4*j.
        var il = Lift(
            0x0c40a900, // ld1 {v0.2s, v1.2s}, [x8]
            0xfd000100); // str d0, [x8]

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
            Assert.That(il.Any(i => i.OpCode == OpCode.Move
                && i.Operands[0] is Register { Name: "V0.S1" }
                && i.Operands[1] is MemoryOperand { Addend: 4 }), Is.True);
            Assert.That(il.Any(i => i.OpCode == OpCode.Move
                && i.Operands[0] is Register { Name: "V1.S0" }
                && i.Operands[1] is MemoryOperand { Addend: 8 }), Is.True);
            Assert.That(il.Any(i => i.OpCode == OpCode.Move
                && i.Operands[0] is Register { Name: "V1.S1" }
                && i.Operands[1] is MemoryOperand { Addend: 12 }), Is.True);
        });
    }

    [Test]
    public void BackwardEdgeLeavesLanesUnproven()
    {
        // A lane whose value is not proven stays diagnosed: a backward edge
        // (a loop) has no converted predecessor state to merge, so extracting
        // a lane under the loop head reports rather than guessing an element
        // local no edge materialized.
        var il = Lift(
            0xfd400100, // ldr d0, [x8]
            0xfd400902, // ldr d2, [x8, #0x10]
            0x2e22dc00, // fmul v0.2s, v0.2s, v2.2s   loop head: back-edge pred unconverted
            0x35ffffe9, // cbnz w9, #-4            -> the fmul: a backward edge
            0x0e0c3c08); // mov w8, v0.s[1]         consumes the loop-carried lane

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented
                && i.Operands[0] is StringLiteral s && s.Value.Contains("unproven")), Is.True,
                () => string.Join("\n", il));
            Assert.That(il.Any(i => IsMove(i, "X8", "V0.S1")), Is.False,
                "a lane under an unconverted backward edge must not be guessed");
        });
    }

    // Arm64Instruction is a struct with internal setters: build it boxed so
    // the properties mutate the same instance that gets returned.
    private static Arm64Instruction MakeInsn(Action<object> init)
    {
        object insn = new Arm64Instruction();
        init(insn);
        return (Arm64Instruction)insn;
    }

    private static void Set(object insn, string property, object value)
        => typeof(Arm64Instruction).GetProperty(property)!.SetValue(insn, value);
}
