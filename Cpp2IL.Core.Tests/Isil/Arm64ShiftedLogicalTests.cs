using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;

namespace Cpp2IL.Core.Tests.Isil;

public class Arm64ShiftedLogicalTests
{
    private const int ShiftLsl = 0;
    private const int ShiftLsr = 1;
    private const int ShiftAsr = 2;
    private const int ShiftRor = 3;

    // Logical (shifted register): sf opc 01010 shift N Rm imm6 Rn Rd
    private static uint Word(bool is64, int opc, bool inverted, int shift, int imm6, int rm, int rn, int rd)
        => (is64 ? 1u << 31 : 0u)
           | ((uint)opc << 29)
           | (0b01010u << 24)
           | ((uint)shift << 22)
           | (inverted ? 1u << 21 : 0u)
           | ((uint)rm << 16)
           | ((uint)imm6 << 10)
           | ((uint)rn << 5)
           | (uint)rd;

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

    private static void AssertNoNotImplemented(System.Collections.Generic.List<Instruction> il, uint word)
        => Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False,
            $"0x{word:x8}: {string.Join("; ", il.Where(i => i.OpCode == OpCode.NotImplemented))}");

    [Test]
    public void EorWordLsrProducesMaskedShift()
    {
        var word = Word(false, 0b10, false, ShiftLsr, 4, 24, 23, 8); // eor w8, w23, w24, lsr #4
        var il = Lift(word);
        AssertNoNotImplemented(il, word);

        var shift = il.Single(i => i.OpCode == OpCode.ShiftRight);
        Assert.That(shift.Operands[1].ToString(), Is.EqualTo("X24"));
        Assert.That(shift.Operands[2], Is.EqualTo(new Immediate(4)));

        var mask = il.Single(i => i.OpCode == OpCode.And && Equals(i.Operands[1], shift.Operands[0]));
        Assert.That(mask.Operands[2], Is.EqualTo(new Immediate((1L << (32 - 4)) - 1)));
        Assert.That(mask.NativeIntegerWidthBits, Is.EqualTo(32));

        var xor = il.Single(i => i.OpCode == OpCode.Xor);
        Assert.That(xor.Operands[1].ToString(), Is.EqualTo("X23"));
        Assert.That(xor.Operands[2], Is.EqualTo(mask.Operands[0]));
        Assert.That(xor.NativeIntegerWidthBits, Is.EqualTo(32));
    }

    [Test]
    public void OrrXWordLslKeepsFullWidth()
    {
        var word = Word(true, 0b01, false, ShiftLsl, 12, 10, 9, 8); // orr x8, x9, x10, lsl #12
        var il = Lift(word);
        AssertNoNotImplemented(il, word);

        var shift = il.Single(i => i.OpCode == OpCode.ShiftLeft);
        Assert.That(shift.Operands[2], Is.EqualTo(new Immediate(12)));
        var or = il.Single(i => i.OpCode == OpCode.Or && Equals(i.Operands[2], shift.Operands[0]));
        Assert.That(or.NativeIntegerWidthBits, Is.Not.EqualTo(32));
    }

    [Test]
    public void AndsWordAsrSignExtendsAndKeepsFlags()
    {
        var word = Word(false, 0b11, false, ShiftAsr, 7, 10, 9, 8); // ands w8, w9, w10, asr #7
        var il = Lift(word);
        AssertNoNotImplemented(il, word);

        var extend = il.Single(i => i.OpCode == OpCode.SignExtend32);
        Assert.That(extend.Operands[1].ToString(), Is.EqualTo("X10"));

        var shift = il.Single(i => i.OpCode == OpCode.ShiftRight && Equals(i.Operands[1], extend.Operands[0]));
        Assert.That(shift.Operands[2], Is.EqualTo(new Immediate(7)));

        var and = il.Single(i => i.OpCode == OpCode.And && Equals(i.Operands[2], shift.Operands[0]));
        Assert.That(and.NativeIntegerWidthBits, Is.EqualTo(32));

        // flag writes for N and Z must survive for branch recovery
        Assert.That(il.Any(i => i.OpCode == OpCode.CheckLess && i.Operands[0].ToString() == "N"), Is.True);
        Assert.That(il.Any(i => i.OpCode == OpCode.CheckEqual && i.Operands[0].ToString() == "Z"), Is.True);
    }

    [Test]
    public void EonXWordRorComposesBothShifts()
    {
        var word = Word(true, 0b10, true, ShiftRor, 20, 10, 9, 8); // eon x8, x9, x10, ror #20
        var il = Lift(word);
        AssertNoNotImplemented(il, word);

        var lsr = il.Single(i => i.OpCode == OpCode.ShiftRight);
        var lsrMask = il.Single(i => i.OpCode == OpCode.And && Equals(i.Operands[1], lsr.Operands[0]));
        Assert.That(lsrMask.Operands[2], Is.EqualTo(new Immediate((1L << (64 - 20)) - 1)));

        var lsl = il.Single(i => i.OpCode == OpCode.ShiftLeft);
        Assert.That(lsl.Operands[2], Is.EqualTo(new Immediate(64 - 20)));

        var rotate = il.Single(i => i.OpCode == OpCode.Or
            && Equals(i.Operands[1], lsrMask.Operands[0])
            && Equals(i.Operands[2], lsl.Operands[0]));
        var not = il.Single(i => i.OpCode == OpCode.Not && Equals(i.Operands[1], rotate.Operands[0]));
        var xor = il.Single(i => i.OpCode == OpCode.Xor && Equals(i.Operands[2], not.Operands[0]));
        Assert.That(xor.NativeIntegerWidthBits, Is.Not.EqualTo(32));
    }

    [TestCase(0b00, false, ShiftLsr, 9)]   // bic w8, w9, w10, lsr #9
    [TestCase(0b01, true, ShiftLsl, 5)]   // orn x8, x9, x10, lsl #5
    [TestCase(0b11, true, ShiftRor, 33)]  // bics x8, x9, x10, ror #33
    [TestCase(0b10, false, ShiftRor, 1)]  // eor x8, x9, x10, ror #1
    [TestCase(0b10, false, ShiftLsr, 63)] // eor x8, x9, x10, lsr #63
    public void InvertedAndBoundaryFormsLower(int opc, bool inverted, int shift, int imm6)
    {
        var word = Word(true, opc, inverted, shift, imm6, 10, 9, 8);
        var il = Lift(word);
        AssertNoNotImplemented(il, word);
        Assert.That(il.Any(i => i.OpCode is OpCode.And or OpCode.Or or OpCode.Xor), Is.True);
    }

    [Test]
    public void ZeroShiftEmitsNoTemporaryOps()
    {
        var word = Word(false, 0b10, false, ShiftLsl, 0, 10, 9, 8); // eor w8, w9, w10
        var il = Lift(word);
        AssertNoNotImplemented(il, word);

        var xor = il.Single(i => i.OpCode == OpCode.Xor);
        Assert.That(xor.Operands[2].ToString(), Is.EqualTo("X10"));
        Assert.That(il.Any(i => i.OpCode is OpCode.ShiftLeft or OpCode.ShiftRight
            or OpCode.SignExtend32), Is.False);
    }

    [Test]
    public void LogicalImmediateFormIsUnshifted()
    {
        // and w8, w9, #0xff00: Op2 is the bitmask immediate, not a shifted register
        var word = 0x121a2528u;
        var il = Lift(word);
        AssertNoNotImplemented(il, word);

        var and = il.Single(i => i.OpCode == OpCode.And);
        Assert.That(and.Operands[2], Is.TypeOf<Immediate>());
        Assert.That(il.Any(i => i.OpCode is OpCode.ShiftLeft or OpCode.ShiftRight), Is.False);
    }

    [Test]
    public void AndsWithZeroShiftStillKeepsFlags()
    {
        var word = Word(false, 0b11, false, ShiftLsl, 0, 10, 9, 8); // ands w8, w9, w10
        var il = Lift(word);
        AssertNoNotImplemented(il, word);
        Assert.That(il.Any(i => i.OpCode == OpCode.CheckLess && i.Operands[0].ToString() == "N"), Is.True);
        Assert.That(il.Any(i => i.OpCode == OpCode.CheckEqual && i.Operands[0].ToString() == "Z"), Is.True);
    }

    // A small reference evaluator: executes the produced ISIL over an explicit
    // register map with the same arithmetic the folder uses (ShiftRight is
    // arithmetic on 64 bits), and compares the destination register against a
    // direct C# model of the ARM64 operation.
    private static ulong Evaluate(System.Collections.Generic.List<Instruction> il,
        Dictionary<string, ulong> inputs, string destination)
    {
        var registers = new Dictionary<string, ulong>(inputs);

        ulong Value(IOperand operand) => operand switch
        {
            Immediate immediate => unchecked((ulong)immediate.Value),
            Register register => registers[register.Name],
            _ => throw new NotSupportedException($"operand {operand}"),
        };

        void Set(IOperand destinationOperand, ulong value)
            => registers[((Register)destinationOperand).Name] = value;

        foreach (var instruction in il)
        {
            var operands = instruction.Operands;
            switch (instruction.OpCode)
            {
                case OpCode.Move:
                    Set(operands[0], Value(operands[1]));
                    break;
                case OpCode.ShiftLeft:
                    Set(operands[0], Value(operands[1]) << (int)(Value(operands[2]) & 63));
                    break;
                case OpCode.ShiftRight:
                    Set(operands[0], unchecked((ulong)((long)Value(operands[1]) >> (int)(Value(operands[2]) & 63))));
                    break;
                case OpCode.And:
                    Set(operands[0], Value(operands[1]) & Value(operands[2]));
                    break;
                case OpCode.Or:
                    Set(operands[0], Value(operands[1]) | Value(operands[2]));
                    break;
                case OpCode.Xor:
                    Set(operands[0], Value(operands[1]) ^ Value(operands[2]));
                    break;
                case OpCode.Not:
                    Set(operands[0], ~Value(operands[1]));
                    break;
                case OpCode.SignExtend32:
                    Set(operands[0], unchecked((ulong)(long)(int)(uint)Value(operands[1])));
                    break;
                case OpCode.CheckLess:
                    Set(operands[0], (long)Value(operands[1]) < (long)Value(operands[2]) ? 1UL : 0UL);
                    break;
                case OpCode.CheckEqual:
                    Set(operands[0], Value(operands[1]) == Value(operands[2]) ? 1UL : 0UL);
                    break;
                case OpCode.Nop:
                case OpCode.Return:
                    break;
                default:
                    Assert.Fail($"reference evaluator cannot run {instruction.OpCode}");
                    break;
            }
        }

        return registers[destination];
    }

    private static ulong ReferenceShifted(ulong rm, int amount, int shift, bool is32)
    {
        if (is32)
        {
            var m32 = (uint)rm;
            return shift switch
            {
                ShiftLsl => m32 << amount,
                ShiftLsr => m32 >> amount,
                ShiftAsr => unchecked((uint)((int)m32 >> amount)),
                ShiftRor => (m32 >> amount) | (m32 << (32 - amount)),
                _ => throw new ArgumentOutOfRangeException(nameof(shift)),
            };
        }

        return shift switch
        {
            ShiftLsl => rm << amount,
            ShiftLsr => rm >> amount,
            ShiftAsr => unchecked((ulong)((long)rm >> amount)),
            ShiftRor => (rm >> amount) | (rm << (64 - amount)),
            _ => throw new ArgumentOutOfRangeException(nameof(shift)),
        };
    }

    private static ulong ReferenceResult(int opc, bool inverted, ulong rn, ulong rm, int amount, int shift, bool is32)
    {
        var mask = is32 ? 0xFFFFFFFFUL : ulong.MaxValue;
        var shifted = ReferenceShifted(rm, amount, shift, is32) & mask;
        if (inverted)
            shifted = ~shifted & mask;
        var left = rn & mask;
        return (opc switch
        {
            0b00 => left & shifted,
            0b01 => left | shifted,
            0b10 => left ^ shifted,
            0b11 => left & shifted,
            _ => throw new ArgumentOutOfRangeException(nameof(opc)),
        }) & mask;
    }

    [TestCase(0b10, false, ShiftLsr, 4, false)]  // eor w8, w23, w24, lsr #4
    [TestCase(0b10, false, ShiftLsr, 31, false)] // eor w8, w9, w10, lsr #31 (boundary)
    [TestCase(0b10, false, ShiftAsr, 31, false)] // eor w8, w9, w10, asr #31 (boundary)
    [TestCase(0b10, false, ShiftRor, 9, false)]  // eor w8, w9, w10, ror #9
    [TestCase(0b00, true, ShiftLsr, 13, false)]  // bic w8, w9, w10, lsr #13
    [TestCase(0b10, false, ShiftLsr, 63, true)]  // eor x8, x9, x10, lsr #63 (boundary)
    [TestCase(0b10, false, ShiftRor, 1, true)]   // eor x8, x9, x10, ror #1 (boundary)
    [TestCase(0b10, false, ShiftRor, 63, true)]  // eor x8, x9, x10, ror #63 (boundary)
    [TestCase(0b10, true, ShiftRor, 20, true)]   // eon x8, x9, x10, ror #20
    [TestCase(0b01, true, ShiftLsl, 17, true)]   // orn x8, x9, x10, lsl #17
    [TestCase(0b00, false, ShiftAsr, 47, true)]  // and x8, x9, x10, asr #47
    public void ShiftedResultMatchesReferenceOnBoundaryValues(int opc, bool inverted, int shift, int imm6, bool is64)
    {
        var rm = 10;
        var rn = 9;
        var rd = 8;
        var word = Word(is64, opc, inverted, shift, imm6, rm, rn, rd);

        foreach (var (left, right) in new (ulong, ulong)[]
        {
            (0x0000000000000000UL, 0x0000000000000000UL),
            (0xFFFFFFFFFFFFFFFFUL, 0x0000000000000001UL),
            (0x00000000FFFFFFFFUL, 0x8000000000000000UL),
            (0xDEADBEEF12345678UL, 0x0123456789ABCDEFUL),
            (0x0000000180000000UL, 0xFFFFFFFF00000000UL),
        })
        {
            var il = Lift(word);
            var actual = Evaluate(il, new Dictionary<string, ulong>
            {
                ["X" + rn] = left,
                ["X" + rm] = right,
            }, "X" + rd);

            var expected = ReferenceResult(opc, inverted, left, right, imm6, shift, !is64);
            var compareMask = is64 ? ulong.MaxValue : 0xFFFFFFFFUL;
            Assert.That(actual & compareMask, Is.EqualTo(expected & compareMask),
                $"0x{word:x8} with x{rn}=0x{left:x16}, x{rm}=0x{right:x16}");
        }
    }
}
