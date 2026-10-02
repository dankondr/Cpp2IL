using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Regression;

// `cbz x8, fail ... fail: bl ThrowNullReferenceException` falls, in the lifted CFG, into the code
// laid out after the noreturn call - a shared epilogue that returns x20. On the throw edge x20
// still holds the method-init flag page from the prologue's adrp, so once the call is a Throw the
// epilogue's phi hands that page to `return` (CastleClashers.Or::Description).
public class ThrowFallThroughTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static LocalVariable Local(string name) => new(name, new Register(null, name));

    [Test]
    public void ThrowBlockNoLongerFeedsTheBlockLaidOutAfterIt()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var page = Local("page");
        var list = Local("list");
        var isNull = Local("isNull");
        var built = Local("built");
        var merged = Local("merged");
        var fail = new Instruction(4, OpCode.CallVoid, new Immediate(0x37c2d20));
        var join = new Instruction(5, OpCode.Phi, merged);
        var graph = new ISILControlFlowGraph(
        [
            new(0, OpCode.Move, page, new Immediate(0x86fc000)),
            new(1, OpCode.CheckEqual, isNull, list, new Immediate(0)),
            new(2, OpCode.ConditionalJump, fail, isNull),
            new(3, OpCode.Jump, join),
            fail,
            join,
            new(6, OpCode.Return, merged),
        ]);
        var failBlock = graph.Blocks.Single(block => block.Instructions.Contains(fail));
        var joinBlock = graph.Blocks.Single(block => block.Instructions.Contains(join));
        join.SetOperands([merged, ..joinBlock.Predecessors.Select(IOperand (p) => p == failBlock ? page : built)]);
        Assume.That(joinBlock.Predecessors, Does.Contain(failBlock), "the lifted call falls through");

        // The helper is proven non-returning and lowered to a Throw.
        fail.OpCode = OpCode.Throw;
        fail.SetOperands(app.AssembliesByName["mscorlib"].GetTypeByFullName("System.NullReferenceException")!);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemObjectType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = graph,
        };

        KeyFunctionRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(failBlock.Successors, Is.EqualTo(new[] { graph.ExitBlock }));
            Assert.That(joinBlock.Predecessors, Does.Not.Contain(failBlock));
            Assert.That(join.Operands.Skip(1), Is.EqualTo(new IOperand[] { built }), "the page no longer reaches the return");
        });
    }

    // A raise inside a protected range natively falls into the catch-rethrow code laid out after it,
    // which nothing else reaches; exception recovery still reads that code, so the edge stays.
    [Test]
    public void SuccessorOnlyTheThrowReachesKeepsItsEdge()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var isNull = Local("isNull");
        var list = Local("list");
        var fail = new Instruction(3, OpCode.CallVoid, new Immediate(0x37c2d20));
        var after = new Instruction(4, OpCode.CallVoid, new Immediate(0x5000));
        var graph = new ISILControlFlowGraph(
        [
            new(0, OpCode.CheckEqual, isNull, list, new Immediate(0)),
            new(1, OpCode.ConditionalJump, fail, isNull),
            new(2, OpCode.Return),
            fail,
            after,
            new(5, OpCode.Return),
        ]);
        var failBlock = graph.Blocks.Single(block => block.Instructions.Contains(fail));
        var afterBlock = graph.Blocks.Single(block => block.Instructions.Contains(after));
        Assume.That(afterBlock.Predecessors, Is.EqualTo(new[] { failBlock }));
        fail.OpCode = OpCode.Throw;
        fail.SetOperands(app.AssembliesByName["mscorlib"].GetTypeByFullName("System.NullReferenceException")!);

        NonReturningHelperRecovery.CutThrowFallThrough(graph);

        Assert.That(failBlock.Successors, Does.Contain(afterBlock));
    }
}
