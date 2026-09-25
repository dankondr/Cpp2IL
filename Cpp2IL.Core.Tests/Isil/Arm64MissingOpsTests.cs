using System;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Isil;

public class Arm64MissingOpsTests
{
    private static System.Collections.Generic.List<Instruction> Lift(uint word)
        => Lift([word]);

    private static System.Collections.Generic.List<Instruction> Lift(params uint[] words)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Test",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        return new NewArmV8InstructionSet().ConvertInstructions(
            Disassembler.Disassemble(words.SelectMany(BitConverter.GetBytes).ToArray(), 0), context);
    }

    [Test]
    public void FloatingAndDupWitnessesAreLowered()
    {
        foreach (var word in new uint[]
        {
            0x1e254000, // frintm s0, s0 (REPORT bytes 0040251e)
            0x1e21c000, // fsqrt s0, s0
            0x1e24c000, // frintp s0, s0
            0x1e20c000, // fabs s0, s0
            0x7ea1d400, // fabd s0, s0, s1 (REPORT bytes 00d4a17e)
            0x4e219800, // frintm v0.4s, v0.4s
            0x4e140420, // dup v0.4s, w1
            0x4e040c20, // dup v0.4s, v1.s[0]
        })
        {
            var il = Lift(word);
            var isVector = word is 0x4e219800 or 0x4e140420 or 0x4e040c20;
            if (isVector)
                Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.True, $"0x{word:x8}");
            else
                Assert.That(il.Any(i => i.OpCode is OpCode.Call or OpCode.NotImplemented), Is.True, $"0x{word:x8}");
        }
    }

    [Test]
    public void BicKeepsShiftedRegisterOperand()
    {
        var il = Lift(0x0aa87d00); // little-endian bytes 00 7d a8 0a, report word 007da80a
        Assert.That(il.Any(i => i.OpCode == OpCode.ShiftRight
            && i.Operands.Count == 3
            && i.Operands[1].ToString() == "X8"
            && i.Operands[2].Equals(new Immediate(31))), Is.True);
    }

    [Test]
    public void MoviShiftedSingleLanesBecomeBroadcastFloat()
    {
        var move = Lift(0x0f0167e2).Single(i => i.OpCode == OpCode.Move);
        Assert.That(move.Operands[1], Is.EqualTo(new Vector128Literal(0.5f, 0.5f, 0.5f, 0.5f)));
    }

    [Test]
    public void WordMaddRetainsIntegerWidthOnBothLoweredOperations()
    {
        var il = Lift(0x1b080288); // madd w8, w20, w8, w0
        Assert.That(il.Where(i => i.OpCode is OpCode.Multiply or OpCode.Add)
            .Select(i => i.NativeIntegerWidthBits), Is.EqualTo(new int?[] { 32, 32 }));
    }

    [Test]
    public void AddRetainsShiftedRegisterScale()
    {
        var il = Lift(0x8b0a0d29); // add x9, x9, x10, lsl #3
        var shift = il.Single(i => i.OpCode == OpCode.ShiftLeft);
        Assert.That(shift.Operands[1].ToString(), Is.EqualTo("X10"));
        Assert.That(shift.Operands[2], Is.EqualTo(new Immediate(3)));
        Assert.That(il.Any(i => i.OpCode == OpCode.Add && Equals(i.Operands[2], shift.Operands[0])), Is.True);
    }

    [TestCase(0x4a180ae8u, OpCode.ShiftLeft, 2)]  // eor w8, w23, w24, lsl #2
    [TestCase(0x4a990908u, OpCode.ShiftRight, 2)] // eor w8, w8, w25, asr #2
    [TestCase(0x4a800508u, OpCode.ShiftRight, 1)] // eor w8, w8, w0, asr #1
    public void LogicalOpsRetainShiftedRegisterOperand(uint word, OpCode shiftOp, long amount)
    {
        var il = Lift(word);
        var shift = il.Single(i => i.OpCode == shiftOp);
        Assert.That(shift.Operands[2], Is.EqualTo(new Immediate(amount)));
        Assert.That(il.Any(i => i.OpCode == OpCode.Xor && Equals(i.Operands[2], shift.Operands[0])), Is.True);
    }

    [Test]
    public void WordLogicalImmediateIsSignNormalized()
    {
        var and = Lift(0x721f791f).Single(i => i.OpCode == OpCode.And); // tst w8, #0xfffffffe
        Assert.That(and.Operands[2], Is.EqualTo(new Immediate(-2)));
    }

    [TestCase(0x10000000u)] // adr x0, #0
    [TestCase(0x90000000u)] // adrp x0, #0
    public void AddressInstructionsRetainPointerWidth(uint word)
    {
        var move = Lift(word).Single(i => i.OpCode == OpCode.Move);
        Assert.That(move.NativeIntegerWidthBits, Is.EqualTo(64));
    }

    [Test]
    public void AdrpAddKeepsExactAddressForFollowingLoad()
    {
        var il = Lift(
            0x90000008u, // adrp x8, #0
            0x91354108u, // add x8, x8, #0xd50
            0xf9400100u  // ldr x0, [x8]
        );

        Assert.That(il.Any(i => i.OpCode == OpCode.Move
            && i.Operands is [_, MemoryOperand { Base: null, Addend: 0xd50 }]), Is.True);
    }
}
