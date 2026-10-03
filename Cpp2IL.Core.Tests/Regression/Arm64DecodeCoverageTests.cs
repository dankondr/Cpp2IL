using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: ARM64 decode coverage (castle-recovery#325, catalog
// entry arm64-decode-coverage). A W-register write zero-extends into X, so
// the ISIL it emits must be marked 32 bits or the value reads as a wider,
// unproven one. A conditional-select arm that is a literal must reach the
// analysis as a Move, not a Not that only constant folding would resolve.
// And an instruction with no operand writes no register: only a word the
// disassembler could not name (INVALID / UNIMPLEMENTED) may still write
// any vector register, so only those clobber lane provenance. A call
// unclobbers exactly the V registers its signature fills — an indirect or
// non-vector call leaves every caller-saved register clobbered, and a
// store of one stays refused.
public class Arm64DecodeCoverageTests
{
    private static List<Instruction> Lift(ApplicationAnalysisContext app, params uint[] words)
        => LiftAt(app, 0, words);

    private static List<Instruction> LiftAt(ApplicationAnalysisContext app, ulong va, params uint[] words)
    {
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Test",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        return new NewArmV8InstructionSet().ConvertInstructions(
            Disassembler.Disassemble(words.SelectMany(BitConverter.GetBytes).ToArray(), va), context);
    }

    private static List<Instruction> Lift(params uint[] words)
    {
        Cpp2IlApi.ResetInternalState();
        return Lift(TestGameLoader.LoadSimple2019Game(), words);
    }

    private static string Diagnostics(List<Instruction> il)
        => string.Join(" | ", il.Where(i => i.OpCode == OpCode.NotImplemented));

    // `movn w20, #0` writes 0xFFFFFFFF: the low word is proven all-ones, the
    // high word is zero — a proven 32-bit value, not an unmarked -1 that an
    // X-width read could take at 64 bits.
    [Test]
    public void MovnWDestIsAProvenWordMove()
    {
        var il = Lift(0x12800014); // movn w20, #0

        var move = il.Single(i => i.OpCode == OpCode.Move && i.Operands[0] is Register { Name: "X20" });
        Assert.Multiple(() =>
        {
            Assert.That(move.NativeIntegerWidthBits, Is.EqualTo(32));
            Assert.That(move.Operands[1], Is.EqualTo(new Immediate(-1, 4)));
        });
    }

    // `movn x20, #0` is a full-width all-ones: the folded immediate proves
    // all eight bytes.
    [Test]
    public void MovnXDestIsAProvenWideMove()
    {
        var il = Lift(0x92800014); // movn x20, #0

        var move = il.Single(i => i.OpCode == OpCode.Move && i.Operands[0] is Register { Name: "X20" });
        Assert.That(move.Operands[1], Is.EqualTo(new Immediate(-1, 8)));
    }

    // `csinv x0, x8, xzr` computes x8 when the condition holds and all-ones
    // otherwise: the false arm is a literal the packed-slot analysis reads
    // as a Move, spelled at decode time rather than left to a Not that only
    // later folding would resolve.
    [Test]
    public void CsinvXzrArmIsAMoveOfAllOnes()
    {
        var il = Lift(0xDA9F0100); // csinv x0, x8, xzr, eq

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.Move
                && i.Operands[0] is Register { Name: "X0" }
                && i.Operands[1] is Immediate { Value: -1, ProvenBytes: 8 }), Is.True,
                () => string.Join("\n", il));
            Assert.That(il.Any(i => i.OpCode == OpCode.Not
                && i.Operands[0] is Register { Name: "X0" }), Is.False,
                () => string.Join("\n", il));
        });
    }

    // `csinv w0` masks the inverted arm to the W width: all-ones at 32 bits.
    [Test]
    public void CsinvWDestMasksTheInvertedArm()
    {
        var il = Lift(0x5A9F0100); // csinv w0, w8, wzr, eq

        var move = il.First(i => i.OpCode == OpCode.Move
            && i.Operands[0] is Register { Name: "X0" }
            && i.Operands[1] is Immediate { Value: -1 });
        Assert.Multiple(() =>
        {
            Assert.That(move.NativeIntegerWidthBits, Is.EqualTo(32));
            Assert.That(move.Operands[1], Is.EqualTo(new Immediate(-1, 4)));
        });
    }

    // `mvn w20, w9` writes a W register: the write into its destination is
    // a 32-bit operation (Disarm decodes the alias to ORN, whose destination
    // write carries the width mark).
    [Test]
    public void MvnWDestMarksWordWidth()
    {
        var il = Lift(0x2A2903F4); // mvn w20, w9

        var write = il.FirstOrDefault(i => i.Operands.Count > 0 && i.Operands[0] is Register { Name: "X20" });
        Assert.That(write, Is.Not.Null, () => string.Join("\n", il));
        Assert.That(write!.NativeIntegerWidthBits, Is.EqualTo(32));
    }

    // `csel w8` writes a W register: both select arms mark the write 32 bits.
    [Test]
    public void CselWDestMarksWordWidth()
    {
        var il = Lift(0x1A890108); // csel w8, w8, w9, eq

        var moves = il.Where(i => i.OpCode == OpCode.Move && i.Operands[0] is Register { Name: "X8" }).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(moves, Has.Count.EqualTo(2));
            Assert.That(moves.All(m => m.NativeIntegerWidthBits == 32), Is.True);
        });
    }

    // `mov w8, #0x80000000` is a W write: the Move carries the 32-bit mark.
    [Test]
    public void MovWImmediateMarksWordWidth()
    {
        var il = Lift(0x52B00008); // mov w8, #-0x80000000

        var move = il.Single(i => i.OpCode == OpCode.Move && i.Operands[0] is Register { Name: "X8" });
        Assert.That(move.NativeIntegerWidthBits, Is.EqualTo(32));
    }

    // `ret` writes no register: provenance the block built survives it. An
    // instruction the disassembler could not name would clobber every vector
    // register, but a decoded operand-free instruction may not.
    [Test]
    public void OperandFreeInstructionsDoNotClobberVectors()
    {
        var il = Lift(
            0x1E201000, // fmov s0, #2.0
            0xD65F03C0, // ret
            0xBD0007A0); // str s0, [x29, #4]

        Assert.That(Diagnostics(il), Does.Not.Contain("clobbered"), () => string.Join("\n", il));
    }

    [Test]
    public void NopDoesNotClobberVectors()
    {
        var il = Lift(
            0x1E201000, // fmov s0, #2.0
            0xD503201F, // nop
            0xBD0007A0); // str s0, [x29, #4]

        Assert.That(Diagnostics(il), Is.Empty, () => string.Join("\n", il));
    }

    // An indirect call's result registers are unknown: V0 stays clobbered
    // and a store of it stays refused rather than reading a value the
    // callee may never have written.
    [Test]
    public void IndirectCallLeavesVectorResultClobbered()
    {
        var il = Lift(
            0x1E201000, // fmov s0, #2.0
            0xD63F0100, // blr x8
            0xBD0007A0); // str s0, [x29, #4]

        Assert.That(Diagnostics(il), Does.Contain("clobbered"), () => string.Join("\n", il));
    }

    // A managed call returning a homogeneous float aggregate defines V0..Vn
    // — one lane per member — so the stores of the extra lanes lift.
    [Test]
    public void CallDefinesItsVectorResultLanes()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var valueType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!;
        var pair = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Vec2",
            valueType, TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout);
        foreach (var name in new[] { "x", "y" })
            pair.Fields.Add(new InjectedFieldAnalysisContext(name, app.SystemTypes.SystemSingleType,
                FieldAttributes.Public, pair));
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Positions",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var callee = new InjectedMethodAnalysisContext(owner, "Get", pair,
            MethodAttributes.Public | MethodAttributes.Static, []);
        // the call target must map inside the binary image: borrow a real
        // method's address and put the synthetic callee on it
        var target = app.MethodsByAddress.Keys.First();
        app.MethodsByAddress[target] = [callee];

        var il = LiftAt(app, target - 4,
            0x94000001, // bl +4 -> the injected callee
            0xBD000BA1); // str s1, [x29, #8]

        Assert.Multiple(() =>
        {
            var call = il.Single(i => i.OpCode == OpCode.Call);
            Assert.That(call.Operands[1], Is.EqualTo(new Register(null, "V0")));
            Assert.That(call.ImplicitDefinitions.Select(lane => lane.Name), Is.EqualTo(new[] { "V1" }));
            Assert.That(Diagnostics(il), Is.Empty, () => string.Join("\n", il));
        });
    }
}
