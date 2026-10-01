using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using ReflectionMethodAttributes = System.Reflection.MethodAttributes;

namespace Cpp2IL.Core.Tests.Isil;

// The lifting contract of the scalar ARM64 numeric conversions: each lifts to
// the Convert opcode carrying the direction, sign and width of the hardware
// instruction, so the destination's type is its own register's width.
public class Arm64ConversionOpcodeShapeTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimpleV106Game();
    }

    private static List<Instruction> Lift(params uint[] words)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Test",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        var bytes = new byte[words.Length * 4];
        for (var i = 0; i < words.Length; i++)
            BitConverter.GetBytes(words[i]).CopyTo(bytes, i * 4);
        return new NewArmV8InstructionSet().ConvertInstructions(
            Disassembler.Disassemble(bytes, 0), context);
    }

    [Test]
    public void FcvtzsLiftsToConversionNotMove()
    {
        var il = Lift(0x1e780008); // fcvtzs w8, d0
        var convert = il.Single(i => i.OpCode == OpCode.Convert);
        Assert.Multiple(() =>
        {
            Assert.That(convert.Operands[0], Is.EqualTo(new Register(null, "X8")));
            Assert.That(convert.Operands[1], Is.EqualTo(new Register(null, "V0")));
            Assert.That(convert.ConversionFromFloat, Is.True);
            Assert.That(convert.ConversionUnsigned, Is.False);
            Assert.That(convert.ConversionSourceWidthBits, Is.EqualTo(64));
            Assert.That(convert.NativeIntegerWidthBits, Is.EqualTo(32));
        });
    }

    [Test]
    public void FcvtzuLiftsToUnsignedConversion()
    {
        var il = Lift(0x1e390009); // fcvtzu w9, s0
        var convert = il.Single(i => i.OpCode == OpCode.Convert);
        Assert.Multiple(() =>
        {
            Assert.That(convert.ConversionFromFloat, Is.True);
            Assert.That(convert.ConversionUnsigned, Is.True);
            Assert.That(convert.ConversionSourceWidthBits, Is.EqualTo(32));
            Assert.That(convert.NativeIntegerWidthBits, Is.EqualTo(32));
        });
    }

    [Test]
    public void ScvtfLiftsToIntegerToFloatConversion()
    {
        var il = Lift(0x1e220020); // scvtf s0, w1
        var convert = il.Single(i => i.OpCode == OpCode.Convert);
        Assert.Multiple(() =>
        {
            Assert.That(convert.ConversionFromFloat, Is.False);
            Assert.That(convert.ConversionUnsigned, Is.False);
            Assert.That(convert.ConversionSourceWidthBits, Is.EqualTo(32));
            Assert.That(convert.NativeFloatWidthBits, Is.EqualTo(32));
        });
    }

    [Test]
    public void UcvtfLiftsToUnsignedIntegerToFloatConversion()
    {
        var il = Lift(0x1e630020); // ucvtf d0, w1
        var convert = il.Single(i => i.OpCode == OpCode.Convert);
        Assert.Multiple(() =>
        {
            Assert.That(convert.ConversionFromFloat, Is.False);
            Assert.That(convert.ConversionUnsigned, Is.True);
            Assert.That(convert.NativeFloatWidthBits, Is.EqualTo(64));
        });
    }

    [Test]
    public void FcvtLiftsToConversion()
    {
        var il = Lift(0x1e624000); // fcvt s0, d0
        var convert = il.Single(i => i.OpCode == OpCode.Convert);
        Assert.Multiple(() =>
        {
            Assert.That(convert.ConversionFromFloat, Is.True);
            Assert.That(convert.ConversionSourceWidthBits, Is.EqualTo(64));
            Assert.That(convert.NativeFloatWidthBits, Is.EqualTo(32));
        });
    }

    // Rounding variants pre-round through Math before the truncating
    // conversion: fcvtms floors, fcvtps ceils, fcvtns rounds, fcvtas rounds
    // away from zero.
    [Test]
    public void RoundingConversionPreRoundsBeforeTruncating()
    {
        var il = Lift(0x1e700008); // fcvtms w8, d0
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == OpCode.Call
                && i.Operands[0] is MethodAnalysisContext { Name: "Floor" }), Is.True);
            Assert.That(il.Any(i => i.OpCode == OpCode.Convert), Is.True);
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
        });
    }
}
