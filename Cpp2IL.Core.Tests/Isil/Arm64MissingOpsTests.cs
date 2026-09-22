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
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Test",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        return new NewArmV8InstructionSet().ConvertInstructions(
            Disassembler.Disassemble(BitConverter.GetBytes(word), 0), context);
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
}
