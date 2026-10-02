using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.Tests.Regression;

// Regression fixture for castle-recovery#317: a flag-setting subtract whose destination aliases a
// compare operand (`subs wD, wD, #k`, `negs wD, wD`, `subs wD, wS, wD`) used to evaluate the flag
// temps on the post-subtraction value — the flag subtraction `TEMP1 = wD - k` read `wD` after it
// was already `wS - k`, so every conditional branch consuming it compared the *result* and the
// condition came out off by k. The flag math must be evaluated on the instruction's real inputs,
// before the destination register is written.
public class SubsFlagOperandAliasingTests
{
    // b.<cond> encodings branching forward by one instruction (+8 bytes).
    private const uint B_MI = 0x54000044;
    private const uint B_PL = 0x54000045;
    private const uint B_VS = 0x54000046;
    private const uint B_GE = 0x5400004A;
    private const uint B_LT = 0x5400004B;
    private const uint B_GT = 0x5400004C;
    private const uint B_LE = 0x5400004D;

    private const uint RET = 0xD65F03C0;

    // Lifts raw words and runs the real SSA + flag-condition pipeline, exactly like
    // MethodAnalysisContext does between GetIsilFromMethod and DeadCodeEliminator.
    private static List<Instruction> Analyze(params uint[] words)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Test",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);

        var il = new NewArmV8InstructionSet().ConvertInstructions(
            Disassembler.Disassemble(words.SelectMany(BitConverter.GetBytes).ToArray(), 0), context);

        var graph = new ISILControlFlowGraph(il);
        context.ControlFlowGraph = graph;
        context.DominatorInfo = new DominatorInfo(graph);
        SsaForm.Build(graph, context.DominatorInfo);
        LocalVariables.CreateAll(context);
        FlagConditionRecovery.Run(graph);
        return graph.Instructions;
    }

    private static Instruction DefOf(List<Instruction> il, IOperand operand)
        => il.FirstOrDefault(i => ReferenceEquals(i.Destination, operand))
            ?? throw new InvalidOperationException($"no def for {operand}");

    private static Instruction ResultSubtract(List<Instruction> il, string destRegister)
        => il.First(i => i.OpCode == OpCode.Subtract
            && i.Destination is LocalVariable d && d.Register.Name == destRegister);

    private static Instruction ConditionDef(List<Instruction> il)
    {
        var jump = il.First(i => i.OpCode == OpCode.ConditionalJump);
        var condition = (LocalVariable)jump.Operands[1];
        return DefOf(il, condition);
    }

    // The flag subtraction and the result subtraction of one `subs` compute the same value; in SSA
    // they must read the identical operand locals. When the flag side reads the result's local it
    // silently shifts the compared boundary by the subtracted amount.
    private static void AssertFlagTempsReadResultOperands(List<Instruction> il, string destRegister)
    {
        var result = ResultSubtract(il, destRegister);
        var flagSub = il.First(i => i.OpCode == OpCode.Subtract
            && i.Destination is LocalVariable d && d.Register.Name == "TEMP1");

        Assert.Multiple(() =>
        {
            Assert.That(flagSub.Operands[1], Is.SameAs(result.Operands[1]),
                "flag subtraction must read the same left operand as the result subtraction");
            Assert.That(flagSub.Operands[2], Is.SameAs(result.Operands[2]),
                "flag subtraction must read the same right operand as the result subtraction");
        });
    }

    private static void AssertCondition(List<Instruction> il, OpCode opCode, string destRegister, object k)
    {
        var def = ConditionDef(il);
        var result = ResultSubtract(il, destRegister);
        Assert.Multiple(() =>
        {
            Assert.That(def.OpCode, Is.EqualTo(opCode));
            Assert.That(def.Operands[1], Is.SameAs(result.Operands[1]),
                "condition must compare the pre-subtraction operand, not the result");
            Assert.That(def.Operands[2], Is.EqualTo(new Immediate(Convert.ToInt64(k))));
        });
    }

    // subs w8, w8, #1 ; b.<cond> — the condition the flags encode is (w8_before - 1) <cond> against
    // the *inputs*, i.e. w8 <cond> 1. Emitting the result first makes every flag expression read the
    // already-decremented w8, so the branch compared (w8 - 1) <cond> 1 — off by k.
    [Test]
    public void SubsInPlaceMinusOne_Bmi() => AssertCondition(Analyze(0x71000508, B_MI, RET, RET), OpCode.CheckLess, "X8", 1);

    [Test]
    public void SubsInPlaceMinusOne_Blt() => AssertCondition(Analyze(0x71000508, B_LT, RET, RET), OpCode.CheckLess, "X8", 1);

    [Test]
    public void SubsInPlaceMinusOne_Bge() => AssertCondition(Analyze(0x71000508, B_GE, RET, RET), OpCode.CheckGreaterOrEqual, "X8", 1);

    [Test]
    public void SubsInPlaceMinusOne_Bgt() => AssertCondition(Analyze(0x71000508, B_GT, RET, RET), OpCode.CheckGreater, "X8", 1);

    [Test]
    public void SubsInPlaceMinusOne_Ble() => AssertCondition(Analyze(0x71000508, B_LE, RET, RET), OpCode.CheckLessOrEqual, "X8", 1);

    [Test]
    public void SubsInPlaceMinusOne_Bpl() => AssertCondition(Analyze(0x71000508, B_PL, RET, RET), OpCode.CheckGreaterOrEqual, "X8", 1);

    // k other than 1: subs w8, w8, #5 ; b.lt must recover w8 < 5, not (w8 - 5) < 5.
    [Test]
    public void SubsInPlaceNonUnitImmediate_Blt() => AssertCondition(Analyze(0x71001508, B_LT, RET, RET), OpCode.CheckLess, "X8", 5);

    // 64-bit form: subs x8, x8, #1 ; b.lt.
    [Test]
    public void SubsInPlaceXForm_Blt() => AssertCondition(Analyze(0xF1000508, B_LT, RET, RET), OpCode.CheckLess, "X8", 1);

    // The destination can alias the subtrahend instead: subs w8, w0, w8 ; b.lt is w0 < w8_before.
    [Test]
    public void SubsAliasedSubtrahend_Blt()
    {
        var il = Analyze(0x6B080008, B_LT, RET, RET);

        AssertFlagTempsReadResultOperands(il, "X8");
        var def = ConditionDef(il);
        var result = ResultSubtract(il, "X8");
        Assert.Multiple(() =>
        {
            Assert.That(def.OpCode, Is.EqualTo(OpCode.CheckLess));
            Assert.That(def.Operands[1], Is.SameAs(result.Operands[1]));
            Assert.That(def.Operands[2], Is.SameAs(result.Operands[2]));
        });
    }

    // negs w8, w8 (subs w8, wzr, w8) ; b.mi — flags on 0 - w8_before.
    [Test]
    public void NegsInPlace_Bmi()
    {
        var il = Analyze(0x6B0803E8, B_MI, RET, RET);

        AssertFlagTempsReadResultOperands(il, "X8");
        var def = ConditionDef(il);
        var result = ResultSubtract(il, "X8");
        Assert.Multiple(() =>
        {
            Assert.That(def.OpCode, Is.EqualTo(OpCode.CheckLess));
            Assert.That(def.Operands[1], Is.SameAs(result.Operands[1]));
            Assert.That(def.Operands[2], Is.SameAs(result.Operands[2]));
        });
    }

    // Overflow flag: subs w8, w8, w9 ; b.vs keeps the V expression unrecovered, but its inputs must
    // still be the pre-subtraction operands — V = ((w8 ^ w9) & (w8 ^ result)) < 0 over the *old* w8.
    [Test]
    public void SubsInPlace_Bvs_KeepsInputsOnOverflowFlag()
    {
        var il = Analyze(0x6B090108, B_VS, RET, RET);

        AssertFlagTempsReadResultOperands(il, "X8");

        // V = CheckLess(TEMP4, 0), TEMP4 = And(Xor(a, b), Xor(a, r)) — the `a` operand is the
        // pre-subtraction register and must be the same local the result subtract reads.
        var result = ResultSubtract(il, "X8");
        var v = DefOf(il, (LocalVariable)il.First(i => i.OpCode == OpCode.ConditionalJump).Operands[1]);
        Assert.That(v.OpCode, Is.EqualTo(OpCode.CheckLess));
        var andDef = DefOf(il, v.Operands[1]);
        Assert.That(andDef.OpCode, Is.EqualTo(OpCode.And));
        foreach (var xorOperand in andDef.Operands.Skip(1))
        {
            var xorDef = DefOf(il, xorOperand);
            Assert.That(xorDef.OpCode, Is.EqualTo(OpCode.Xor));
            Assert.That(xorDef.Operands[1], Is.SameAs(result.Operands[1]),
                "overflow flag inputs must read the pre-subtraction operand");
        }
    }

    // A non-aliasing subs is the control case: `subs w8, w0, #5 ; b.lt` already compared w0 < 5 and
    // must keep doing so.
    [Test]
    public void SubsDistinctDest_Blt() => AssertCondition(Analyze(0x71001408, B_LT, RET, RET), OpCode.CheckLess, "X8", 5);

    // cmp w8, #1 (subs wzr, w8, #1) ; b.lt — no live destination at all; always w8 < 1.
    [Test]
    public void CmpImmediate_Blt()
    {
        var il = Analyze(0x7100051F, B_LT, RET, RET);
        var def = ConditionDef(il);
        Assert.Multiple(() =>
        {
            Assert.That(def.OpCode, Is.EqualTo(OpCode.CheckLess));
            Assert.That(def.Operands[1], Is.InstanceOf<LocalVariable>());
            Assert.That(((LocalVariable)def.Operands[1]).Register.Name, Is.EqualTo("X8"));
            Assert.That(def.Operands[2], Is.EqualTo(new Immediate(1)));
        });
    }
}
