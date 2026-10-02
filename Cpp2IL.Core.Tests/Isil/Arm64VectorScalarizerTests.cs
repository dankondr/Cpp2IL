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
    private static List<Instruction> Lift(params uint[] words) => LiftAt(0, words);

    private static List<Instruction> LiftAt(ulong baseAddress, params uint[] words)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Test",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        return new NewArmV8InstructionSet().ConvertInstructions(
            Disassembler.Disassemble(words.SelectMany(BitConverter.GetBytes).ToArray(), baseAddress), context);
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
    public void UnprovenLaneConsumptionIsDiagnosed()
    {
        // A single-element LD1 proves only the lane it writes; extracting a
        // lane it never loaded must leave an explicit diagnostic, not a guess.
        var il = Lift(
            0x4d409140, // ld1 {v0.s}[3], [x10]
            0x0e043c08); // mov w8, v0.s[0]

        Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented
            && i.Operands[0] is StringLiteral s && s.Value.Contains("unproven")), Is.True);
    }

    [Test]
    public void PartiallyProvenVectorEmitsOnlyProvenLanes()
    {
        // Only lane 1 of v2 is written; lane 0 is hardware-stale. The pass must
        // emit the provable lane op and report the unprovable one, not guess.
        var il = Lift(
            0x4e0c1d02, // mov v2.s[1], w8
            0x0ea28440); // add v0.2s, v2.2s, v2.2s

        Assert.Multiple(() =>
        {
            Assert.That(FindOp(il, OpCode.Add, "V0.S1"), Is.Not.Null);
            Assert.That(FindOp(il, OpCode.Add, "V0.S0"), Is.Null);
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented
                && i.Operands[0] is StringLiteral s && s.Value.Contains("scalarized 1 of 2")), Is.True);
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
    public void StoreOfReloadedRegisterReadsReloadedValue()
    {
        // Two 8-byte copies through d0: each store reads the register local —
        // any carry-over of the first sequence (a cached high-half temporary,
        // a stale lane) would show the second store reading the first load's
        // source.
        var il = Lift(
            0xfd402520, // ldr d0, [x9, #0x48]
            0xfc024260, // stur d0, [x19, #0x24]
            0xfd402500, // ldr d0, [x8, #0x48]
            0xfd001a60); // str d0, [x19, #0x30]

        var stores = il.Where(i => i.OpCode == OpCode.Move
            && i.Operands[0] is MemoryOperand { Base: Register { Name: "X19" } }).ToList();
        Assert.Multiple(() =>
        {
            // each 8-byte store writes the whole d-register: a scratch-base
            // load keeps no memory provenance, so the store reads the local
            // the load defined — SSA dominance makes the second store read
            // the second load's value, never a stale temp.
            Assert.That(stores, Has.Count.EqualTo(2), () => string.Join("\n", il));
            Assert.That(stores[0].Operands[1], Is.EqualTo(new Register(null, "V0")));
            Assert.That(stores[1].Operands[1], Is.EqualTo(new Register(null, "V0")));
            Assert.That(((MemoryOperand)stores[0].Operands[0]).AccessSize, Is.EqualTo(8));
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        });
    }

    [Test]
    public void StoreOfLaneMixedValueWritesEachWindow()
    {
        // A d-store of a value written per lane (fmul .2s) is a two-float copy:
        // split it so an adjacent-float-fields target resolves each half.
        // The lane op itself is a Single result and is marked so — without the
        // mark the element local can inherit an aggregate operand's type.
        var il = Lift(
            0xfd402520, // ldr d0, [x9, #0x48]
            0x0e040d02, // dup v2.2s, w8
            0x2e22dc00, // fmul v0.2s, v0.2s, v2.2s
            0xfd001a60); // str d0, [x19, #0x30]

        var stores = il.Where(i => i.OpCode == OpCode.Move
            && i.Operands[0] is MemoryOperand { Base: Register { Name: "X19" } }).ToList();
        Assert.That(stores, Has.Count.EqualTo(2), () => string.Join("\n", il));
        Assert.Multiple(() =>
        {
            Assert.That(stores[0].Operands[1], Is.EqualTo(new Register(null, "V0.S0")));
            Assert.That(stores[1].Operands[1], Is.EqualTo(new Register(null, "V0.S1")));
            var mul = FindOp(il, OpCode.Multiply, "V0.S0");
            Assert.That(mul, Is.Not.Null);
            Assert.That(mul!.NativeFloatWidthBits, Is.EqualTo(32));
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        });
    }

    [Test]
    public void PairedStoreOfLanesFromOneVectorWritesOneWideStore()
    {
        // STP S,S is one 8-byte store: when both lanes were copied out of the
        // two 32-bit halves of one register, the store names that register so
        // an aggregate target keeps its type rather than two Single locals.
        var dup = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.DUP);
            Set(m, "Op0Kind", Arm64OperandKind.Register);
            Set(m, "Op0Reg", Arm64Register.V0);
            Set(m, "Op0Arrangement", Arm64ArrangementSpecifier.TwoS);
            Set(m, "Op1Kind", Arm64OperandKind.Register);
            Set(m, "Op1Reg", Arm64Register.W8);
        });
        var fmov = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.FMOV);
            Set(m, "Address", (ulong)4);
            Set(m, "Op0Kind", Arm64OperandKind.Register);
            Set(m, "Op0Reg", Arm64Register.S9);
            Set(m, "Op1Kind", Arm64OperandKind.Register);
            Set(m, "Op1Reg", Arm64Register.S0);
        });
        var ins = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.INS);
            Set(m, "Address", (ulong)8);
            Set(m, "Op0Kind", Arm64OperandKind.VectorRegisterElement);
            Set(m, "Op0Reg", Arm64Register.V8);
            Set(m, "Op0VectorElement", new Arm64VectorElement(Arm64VectorElementWidth.S, 0));
            Set(m, "Op1Kind", Arm64OperandKind.VectorRegisterElement);
            Set(m, "Op1Reg", Arm64Register.V0);
            Set(m, "Op1VectorElement", new Arm64VectorElement(Arm64VectorElementWidth.S, 1));
        });
        var stp = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.STP);
            Set(m, "Address", (ulong)12);
            Set(m, "Op0Kind", Arm64OperandKind.Register);
            Set(m, "Op0Reg", Arm64Register.S9);
            Set(m, "Op1Kind", Arm64OperandKind.Register);
            Set(m, "Op1Reg", Arm64Register.S8);
            Set(m, "MemBase", Arm64Register.X19);
            Set(m, "MemOffset", (long)8);
            Set(m, "MemIndexMode", Arm64MemoryIndexMode.Offset);
            Set(m, "MemAddendReg", Arm64Register.INVALID);
        });

        var emitted = new List<Instruction>();
        Instruction Add(ulong address, OpCode opCode, List<IOperand> operands)
        {
            var insn = new Instruction(emitted.Count, opCode, operands);
            emitted.Add(insn);
            return insn;
        }
        // operand conversion names the register each operand position reads
        Func<Arm64Instruction, int, IOperand> conv = (insn, op) => new Register(null,
            (op == 0 ? insn.Op0Reg : insn.Op1Reg) switch
            {
                Arm64Register.S9 => "V9",
                Arm64Register.S8 => "V8",
                Arm64Register.S0 => "V0",
                Arm64Register.S1 => "V1",
                var r => r.ToString()
            });

        var scalarizer = new Arm64VectorScalarizer();
        scalarizer.Begin([dup, fmov, ins, stp]);
        scalarizer.TryBroadcastDup(dup, Add, conv);
        scalarizer.BeginInstruction(fmov, Add);
        scalarizer.TryConvert(fmov, Add, conv);
        scalarizer.BeginInstruction(ins, Add);
        scalarizer.TryConvert(ins, Add, conv);
        scalarizer.BeginInstruction(stp, Add);
        scalarizer.TryConvert(stp, Add, conv);

        var stores = emitted.Where(i => i.OpCode == OpCode.Move
            && i.Operands[0] is MemoryOperand { Base: Register { Name: "X19" } }).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(stores, Has.Count.EqualTo(1), () => string.Join("\n", emitted));
            Assert.That(stores[0].Operands[1], Is.EqualTo(new Register(null, "V0")));
            Assert.That(stores[0].NativeMemoryAccessSize, Is.EqualTo(8));
            Assert.That(emitted.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        });
    }

    [Test]
    public void PairedStoreOfUnrelatedLanesWritesEachWindow()
    {
        // Two singles that did not come from one value are still one 8-byte
        // hardware store, but no single operand names them: split so each
        // half resolves its own field in the store target.
        var dup0 = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.DUP);
            Set(m, "Op0Kind", Arm64OperandKind.Register);
            Set(m, "Op0Reg", Arm64Register.V0);
            Set(m, "Op0Arrangement", Arm64ArrangementSpecifier.TwoS);
            Set(m, "Op1Kind", Arm64OperandKind.Register);
            Set(m, "Op1Reg", Arm64Register.W8);
        });
        var dup1 = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.DUP);
            Set(m, "Address", (ulong)4);
            Set(m, "Op0Kind", Arm64OperandKind.Register);
            Set(m, "Op0Reg", Arm64Register.V1);
            Set(m, "Op0Arrangement", Arm64ArrangementSpecifier.TwoS);
            Set(m, "Op1Kind", Arm64OperandKind.Register);
            Set(m, "Op1Reg", Arm64Register.W9);
        });
        var fmovLo = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.FMOV);
            Set(m, "Address", (ulong)8);
            Set(m, "Op0Kind", Arm64OperandKind.Register);
            Set(m, "Op0Reg", Arm64Register.S9);
            Set(m, "Op1Kind", Arm64OperandKind.Register);
            Set(m, "Op1Reg", Arm64Register.S0);
        });
        var fmovHi = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.FMOV);
            Set(m, "Address", (ulong)12);
            Set(m, "Op0Kind", Arm64OperandKind.Register);
            Set(m, "Op0Reg", Arm64Register.S8);
            Set(m, "Op1Kind", Arm64OperandKind.Register);
            Set(m, "Op1Reg", Arm64Register.S1);
        });
        var stp = MakeInsn(m =>
        {
            Set(m, "Mnemonic", Arm64Mnemonic.STP);
            Set(m, "Address", (ulong)16);
            Set(m, "Op0Kind", Arm64OperandKind.Register);
            Set(m, "Op0Reg", Arm64Register.S9);
            Set(m, "Op1Kind", Arm64OperandKind.Register);
            Set(m, "Op1Reg", Arm64Register.S8);
            Set(m, "MemBase", Arm64Register.X19);
            Set(m, "MemOffset", (long)8);
            Set(m, "MemIndexMode", Arm64MemoryIndexMode.Offset);
            Set(m, "MemAddendReg", Arm64Register.INVALID);
        });

        var emitted = new List<Instruction>();
        Instruction Add(ulong address, OpCode opCode, List<IOperand> operands)
        {
            var insn = new Instruction(emitted.Count, opCode, operands);
            emitted.Add(insn);
            return insn;
        }
        // operand conversion names the register each operand position reads
        Func<Arm64Instruction, int, IOperand> conv = (insn, op) => new Register(null,
            (op == 0 ? insn.Op0Reg : insn.Op1Reg) switch
            {
                Arm64Register.S9 => "V9",
                Arm64Register.S8 => "V8",
                Arm64Register.S0 => "V0",
                Arm64Register.S1 => "V1",
                var r => r.ToString()
            });

        var scalarizer = new Arm64VectorScalarizer();
        scalarizer.Begin([dup0, dup1, fmovLo, fmovHi, stp]);
        scalarizer.TryBroadcastDup(dup0, Add, conv);
        scalarizer.BeginInstruction(dup1, Add);
        scalarizer.TryBroadcastDup(dup1, Add, conv);
        scalarizer.BeginInstruction(fmovLo, Add);
        scalarizer.TryConvert(fmovLo, Add, conv);
        scalarizer.BeginInstruction(fmovHi, Add);
        scalarizer.TryConvert(fmovHi, Add, conv);
        scalarizer.BeginInstruction(stp, Add);
        scalarizer.TryConvert(stp, Add, conv);

        var stores = emitted.Where(i => i.OpCode == OpCode.Move
            && i.Operands[0] is MemoryOperand { Base: Register { Name: "X19" } }).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(stores, Has.Count.EqualTo(2), () => string.Join("\n", emitted));
            Assert.That(stores[0].Operands[1], Is.EqualTo(new Register(null, "V9")));
            Assert.That(stores[1].Operands[1], Is.EqualTo(new Register(null, "V8")));
            Assert.That(emitted.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
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
        // path runs unchanged. The extract of v1's never-written lane 1 is
        // diagnosed at the instruction — an unwritten lane has no proven value.
        var il = Lift(
            0x3cc01500, // ldr v0, [x8], #0x1
            0x0e201c23, // and v3.8b, v1.8b, v0.8b
            0x0e0c3c28); // mov w8, v1.s[1]

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.And
                && i.Operands[0] is Register r && r.Name == "V3"), Is.True);
            Assert.That(il.Any(i => IsMove(i, "X8", "V1.S1")), Is.False);
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.True);
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
    public void DupOfUnwrittenElementIsDiagnosed()
    {
        // dup v0.4s, v9.s[2]: element 2 of a never-written register has no
        // proven value — the broadcast is diagnosed, not guessed into lanes.
        var il = Lift(0x4e140520);

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.True);
            Assert.That(il.Any(i => i.OpCode == OpCode.Move
                && i.Operands[0] is Register { Name: { } n } && n.StartsWith("V0.")), Is.False);
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
            Assert.That(il.Any(i => IsMove(i, "V2.S1", "V3")), Is.True); // INS
            Assert.That(il.Any(i => IsMove(i, "V0.S0", "V1")), Is.True); // DUP
            Assert.That(il.Any(i => IsMove(i, "V0.S1", "V1")), Is.True);
            var lo = FindOp(il, OpCode.Divide, "V0.S0");
            var hi = FindOp(il, OpCode.Divide, "V0.S1");
            Assert.That(lo, Is.Not.Null);
            Assert.That(hi, Is.Not.Null);
            Assert.That(lo!.Operands[1], Is.EqualTo(new Register(null, "V2")));
            Assert.That(lo.Operands[2], Is.EqualTo(new Register(null, "V0.S0")));
            Assert.That(hi!.Operands[1], Is.EqualTo(new Register(null, "V2.S1")));
            Assert.That(hi.Operands[2], Is.EqualTo(new Register(null, "V0.S1")));
        });
    }

    [Test]
    public void DoubleFieldLoadIsNotSplit()
    {
        // ldr d0 on an untyped location could carry a double — it must stay
        // one wide register-local value; only a location proven to hold
        // adjacent float fields may split into lanes.
        var il = Lift(
            0xfd400000, // ldr d0, [x0]
            0xfd000020); // str d0, [x1]

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.Move
                && i.Operands[0] is Register { Name: "V0" }
                && i.Operands[1] is MemoryOperand), Is.True,
                "the D load stays one wide move into the register local");
            Assert.That(il.Any(i => i.OpCode == OpCode.Move
                && i.Operands[0] is Register { Name: "V0.S0" }
                && i.Operands[1] is MemoryOperand), Is.False,
                "an untyped 8-byte location must not split into lane loads");
        });
    }

    [Test]
    public void PermutesMoveLanesIntoElementLocals()
    {
        // EXT/ZIP/UZP/TRN/REV are pure permutations: each destination lane is a
        // verbatim copy of one source lane — the element local that holds it.
        var il = Lift(
            0x4e040d01, // dup v1.4s, w8
            0x4e040d22, // dup v2.4s, w9
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

    [Test]
    public void EntryScalarReadUsesRegisterLocal()
    {
        // Element 0 of a never-written register is its own scalar home: a
        // signature's float/aggregate argument lives in the register local,
        // so the extract reads it — higher lanes have no proven value.
        var il = Lift(
            0x0e043c08); // mov w8, v0.s[0]

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => IsMove(i, "X8", "V0")), Is.True);
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
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

    [Test]
    public void ConditionalBranchKeepsFallThroughLanes()
    {
        // b.cond shares the B mnemonic with the unconditional branch in Disarm
        // — only the conditional-branch category separates them. Treating it
        // as unconditional clears lane state on the fall-through path, so the
        // next instruction's edge snapshot is empty and the merge reports the
        // insert's source lane unproven.
        var il = LiftAt(0x180001000,
            0x2f00e400, // movi d0, #0            seeds V0's lanes
            0x7100011f, // cmp w8, #0
            0x54000060, // b.eq +0x0c           one edge into the merge
            0x14000002, // b +0x08             the other edge — its snapshot
                        //                    was empty when b.eq cleared
            0x52800028, // mov w8, #1          dead bytes after the branch
            0x6e0c0401, // mov v1.s[1], v0.s[0] reads the merged lane
            0xd65f03c0); // ret

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented
                && i.Operands[0] is StringLiteral s && s.Value.Contains("unproven")), Is.False,
                () => string.Join("\n", il));
            Assert.That(il.Any(i => IsMove(i, "V1.S1", "V0")), Is.True,
                "both edges carry the lane through the conditional branch");
        });
    }

    [Test]
    public void ScalarDoubleStoreIsOneWideStore()
    {
        // A `str d` of a register an `ldr d` just filled is one eight-byte
        // store of the register local: a scratch-base load keeps no memory
        // provenance, but the local's definition does — the resolver spells
        // the whole aggregate, a double member resolves the double, and
        // adjacent float members resolve their two halves.
        var il = Lift(
            0xfd400e60, // ldr d0, [x19, #0x18]
            0xfd402100, // ldr d0, [x8, #0x40]
            0xfd001280); // str d0, [x20, #0x20]

        var stores = il.Where(i => i.OpCode == OpCode.Move
            && i.Operands[0] is MemoryOperand { Base: Register { Name: "X20" } }).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(stores, Has.Count.EqualTo(1), () => string.Join("\n", il));
            Assert.That((MemoryOperand)stores[0].Operands[0],
                Is.EqualTo(new MemoryOperand(new Register(null, "X20"), addend: 0x20, accessSize: 8)));
            Assert.That(stores[0].Operands[1], Is.EqualTo(new Register(null, "V0")));
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False,
                () => string.Join("\n", il));
        });
    }

    [Test]
    public void PairStoreOfAdjacentVectorLoadsIsOneStructCopy()
    {
        // `ldp q1, q0` + `stp q1, q0` copies 32 bytes of one range to another —
        // the classic struct copy a C compiler emits for `dst = src` on a
        // 32-byte struct. Emit a single memory-to-memory move so the resolver
        // stores the whole aggregate instead of truncating to one field.
        var il = Lift(
            0xad410001, // ldp q1, q0, [x0, #0x20]
            0xad000021); // stp q1, q0, [x1]

        var stores = il.Where(i => i.OpCode == OpCode.Move
            && i.Operands[0] is MemoryOperand { Base: Register { Name: "X1" } }).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(stores, Has.Count.EqualTo(1), () => string.Join("\n", il));
            Assert.That((MemoryOperand)stores[0].Operands[0],
                Is.EqualTo(new MemoryOperand(new Register(null, "X1"), accessSize: 32)));
            Assert.That(stores[0].Operands[1], Is.EqualTo(
                new MemoryOperand(new Register(null, "X0"), addend: 0x20, accessSize: 32)));
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        });
    }

    [Test]
    public void VectorStoreOfReloadedRegisterIsMemoryCopy()
    {
        var il = Lift(
            0x3dc00400, // ldr q0, [x0, #0x10]
            0x3d800020); // str q0, [x1]

        var stores = il.Where(i => i.OpCode == OpCode.Move
            && i.Operands[0] is MemoryOperand { Base: Register { Name: "X1" } }).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(stores, Has.Count.EqualTo(1), () => string.Join("\n", il));
            Assert.That((MemoryOperand)stores[0].Operands[0],
                Is.EqualTo(new MemoryOperand(new Register(null, "X1"), accessSize: 16)));
            Assert.That(stores[0].Operands[1], Is.EqualTo(
                new MemoryOperand(new Register(null, "X0"), addend: 0x10, accessSize: 16)));
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        });
    }

    [Test]
    public void ZeroVectorStoresEmitWholeWidthImmediates()
    {
        // `movi` + vector stores is the compiler's struct/array zero-fill: each
        // store must carry its full width with an immediate zero source so the
        // resolver can split the range per field or merge a run into initobj.
        var il = Lift(
            0x6f00e400, // movi v0.2d, #0
            0xad008120, // stp q0, q0, [x9, #0x10]
            0x3d800120); // str q0, [x9]

        var stores = il.Where(i => i.OpCode == OpCode.Move
            && i.Operands[0] is MemoryOperand { Base: Register { Name: "X9" } }).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(stores, Has.Count.EqualTo(3), () => string.Join("\n", il));
            Assert.That(stores.Select(s => ((MemoryOperand)s.Operands[0]).Addend),
                Is.EqualTo(new long[] { 0x10, 0x20, 0x00 }));
            foreach (var store in stores)
            {
                Assert.That(((MemoryOperand)store.Operands[0]).AccessSize, Is.EqualTo(16));
                Assert.That(store.Operands[1], Is.EqualTo(new Immediate(0, 16)));
            }
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        });
    }

    [Test]
    public void DoubleStoreOfScalarValueWritesOneWideStore()
    {
        // `fmov d0, x0` leaves v0 holding one 64-bit scalar: `str d` stores the
        // register's low and high halves of that one operand, so emit the
        // eight-byte store a double member resolves whole.
        var il = Lift(
            0x9e670000, // fmov d0, x0
            0xfd000420); // str d0, [x1, #0x8]

        var stores = il.Where(i => i.OpCode == OpCode.Move
            && i.Operands[0] is MemoryOperand { Base: Register { Name: "X1" } }).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(stores, Has.Count.EqualTo(1), () => string.Join("\n", il));
            Assert.That((MemoryOperand)stores[0].Operands[0],
                Is.EqualTo(new MemoryOperand(new Register(null, "X1"), addend: 0x8, accessSize: 8)));
            Assert.That(stores[0].Operands[1], Is.EqualTo(new Register(null, "V0")));
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        });
    }
}
