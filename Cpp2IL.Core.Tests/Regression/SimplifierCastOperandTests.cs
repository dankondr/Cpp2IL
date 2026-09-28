using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: compile bucket CS0039 (castle-recovery#130). castle-recovery#123
// fixed the same blind spot in SsaSimplifier/CopyCoalescer; the post-SSA Simplifier
// shared it - a local read only by an isinst/castclass operand was invisible to
// IsLocalUsedAfterInstruction, so its copy could be dropped as dead while
// ReplaceLocalsUntilReassignment never forwarded into the cast, leaving the operand
// bound to a stale local with no producer.
public class SimplifierCastOperandTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [Test]
    public void CopyPropagationRewritesCastOperandToSourceLocal()
    {
        // x := y; result := isinst<T>(x). The copy must forward into the cast, so the
        // operand rebinds to y and the now-dead copy is removed - previously the cast
        // kept x, the copy was still dropped, and the operand dangled on a stale local.
        var app = Cpp2IlApi.CurrentAppContext!;
        var target = app.SystemTypes.SystemExceptionType;
        var x = new LocalVariable("x", new Register(null, "x"));
        var y = new LocalVariable("y", new Register(null, "y"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var copy = new Instruction(0, OpCode.Move, x, y);
        var cast = new Instruction(1, OpCode.Move, result, new ReferenceCast(x, target, true));
        var graph = new ISILControlFlowGraph([
            copy,
            cast,
            new Instruction(2, OpCode.CallVoid, Str("sink"), result),
            new Instruction(3, OpCode.Return)]);
        var method = CreateMethod(graph, x, y, result);

        Simplifier.Simplify(method);

        var liveCast = LiveCastOperand(graph);
        Assert.Multiple(() =>
        {
            Assert.That(liveCast.Value, Is.SameAs(y),
                "the cast operand must forward through the copy to its source local");
            Assert.That(method.Locals.Contains(x), Is.False,
                "the stale local must be removed once the cast no longer reads it");
            Assert.That(copy.OpCode, Is.EqualTo(OpCode.Nop),
                "the dead copy must be dropped");
        });
    }

    [Test]
    public void MultiplyDefinedCastOperandKeepsItsDefiningMoves()
    {
        // x has one definition per predecessor; the join's only use of x is the cast
        // operand. Neither definition may flow past the join, and neither may be read
        // as dead: without the cast counted as a use, both defining moves were nopped
        // and x left the local table while the cast still named it.
        var app = Cpp2IlApi.CurrentAppContext!;
        var target = app.SystemTypes.SystemExceptionType;
        var x = new LocalVariable("x", new Register(null, "x"));
        var y = new LocalVariable("y", new Register(null, "y"));
        var z = new LocalVariable("z", new Register(null, "z"));
        var cond = new LocalVariable("cond", new Register(null, "cond"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var moveA = new Instruction(2, OpCode.Move, x, y);
        var moveB = new Instruction(4, OpCode.Move, x, z);
        var cast = new Instruction(5, OpCode.Move, result, new ReferenceCast(x, target, true));
        var instructions = new List<Instruction>
        {
            new(0, OpCode.CheckNotEqual, cond, y, Imm(0)),
            new(1, OpCode.ConditionalJump, Imm(4), cond),
            moveA,
            new(3, OpCode.Jump, Imm(5)),
            moveB,
            cast,
            new(6, OpCode.CallVoid, Str("sink"), result),
            new(7, OpCode.Return),
        };

        foreach (var instruction in instructions)
        {
            if (instruction.OpCode is not (OpCode.Jump or OpCode.ConditionalJump))
                continue;

            instruction.SetOperand(0, instructions[(int)((Immediate)instruction.Operands[0]).Value]);
        }

        var graph = new ISILControlFlowGraph(instructions);
        var method = CreateMethod(graph, x, y, z, cond, result);

        Simplifier.Simplify(method);

        var liveCast = LiveCastOperand(graph);
        Assert.Multiple(() =>
        {
            Assert.That(liveCast.Value, Is.SameAs(x),
                "the cast operand must keep the join's local, not a branch definition");
            Assert.That(moveA.OpCode, Is.EqualTo(OpCode.Move),
                "the path-A definition must survive while the cast still reads x");
            Assert.That(moveB.OpCode, Is.EqualTo(OpCode.Move),
                "the path-B definition must survive while the cast still reads x");
            Assert.That(method.Locals.Contains(x), Is.True,
                "the join's local must stay in the local table");
        });
    }

    private static ReferenceCast LiveCastOperand(ISILControlFlowGraph graph) =>
        graph.Blocks.SelectMany(b => b.Instructions)
            .SelectMany(i => i.Operands)
            .OfType<ReferenceCast>()
            .Single();

    private static MethodAnalysisContext CreateMethod(ISILControlFlowGraph graph, params LocalVariable[] locals)
    {
        var method = (MethodAnalysisContext)RuntimeHelpers.GetUninitializedObject(typeof(MethodAnalysisContext));
        method.ControlFlowGraph = graph;
        method.Locals = locals.ToList();
        method.ParameterLocals = [];
        return method;
    }
}
