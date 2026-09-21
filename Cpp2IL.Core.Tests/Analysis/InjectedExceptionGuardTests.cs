using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class InjectedExceptionGuardTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [TestCase(true, true)]
    [TestCase(false, false)]
    public void NullGuardRequiresSameReferenceDereference(bool sameReference, bool expected)
    {
        var reference = Local("reference");
        reference.Type = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemStringType;
        var dereferenced = sameReference ? reference : Local("other");
        var value = Local("value");
        Assert.That(Matches("System.NullReferenceException", reference,
            new Instruction(3, OpCode.Move, value, new MemoryOperand(dereferenced))), Is.EqualTo(expected));
    }

    [TestCase(32, true)]
    [TestCase(40, false)]
    public void BoundsGuardRequiresSameArrayElementZeroRead(long elementOffset, bool expected)
    {
        var array = Local("array");
        var length = Local("length");
        var value = Local("value");
        Assert.That(Matches("System.IndexOutOfRangeException", length,
            new Instruction(3, OpCode.Move, value, new MemoryOperand(array, addend: elementOffset)),
            new Instruction(0, OpCode.Move, length, new MemoryOperand(array, addend: 24))), Is.EqualTo(expected));
    }

    [Test]
    public void NullElementGuardMatchesSameElementAsInstanceReceiver()
    {
        var array = Local("array");
        var element = new ArrayAccess(array, new Immediate(0));
        var result = Local("result");
        var trim = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemStringType.Methods
            .First(method => method.Name == "Trim" && !method.IsStatic);
        var call = new Instruction(3, OpCode.Call, trim, result, element);
        Assert.That(Matches("System.NullReferenceException", element, call), Is.True);
    }

    private static bool Matches(string exception, IOperand checkedValue, Instruction implicitFailure,
        Instruction? setup = null)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        var condition = Local("condition");
        var helperResult = Local("helperResult");
        var helper = new Instruction(5, OpCode.Call, new Immediate(0x1000), helperResult);
        var instructions = new List<Instruction>();
        if (setup != null)
            instructions.Add(setup);
        instructions.Add(new Instruction(1, OpCode.CheckEqual, condition, checkedValue, new Immediate(0)));
        instructions.Add(new Instruction(2, OpCode.ConditionalJump, helper, condition));
        instructions.Add(implicitFailure);
        instructions.Add(new Instruction(4, OpCode.Return));
        instructions.Add(helper);
        instructions.Add(new Instruction(6, OpCode.Return));
        method.ControlFlowGraph = new(instructions);
        var helperBlock = method.ControlFlowGraph.Blocks.Single(block => block.Instructions.Contains(helper));
        HashSet<Block> recoveredHelpers = [];
        if (exception == "System.NullReferenceException")
        {
            var array = Local("sharedArray");
            array.Type = new SzArrayTypeAnalysisContext(app.SystemTypes.SystemStringType);
            var element = new ArrayAccess(array, new Immediate(0));
            var trim = app.SystemTypes.SystemStringType.Methods.First(method => method.Name == "Trim" && !method.IsStatic);
            if (checkedValue is ArrayAccess)
            {
                var reference = Local("sharedReference");
                reference.Type = app.SystemTypes.SystemStringType;
                AddGuard(method.ControlFlowGraph, helperBlock, reference,
                    new Instruction(12, OpCode.Move, Local("value12"), new MemoryOperand(reference)), 10);
            }
            else
                AddGuard(method.ControlFlowGraph, helperBlock, element,
                    new Instruction(12, OpCode.Call, trim, Local("value12"), element), 10);
            AddGuard(method.ControlFlowGraph, helperBlock, array,
                new Instruction(22, OpCode.Move, Local("value22"), new MemoryOperand(array, addend: 24)), 20);
        }
        else
        {
            var terminal = new Block { BlockType = BlockType.Return, Instructions = [new Instruction(10, OpCode.Throw)] };
            terminal.Successors.Add(helperBlock);
            helperBlock.Predecessors.Add(terminal);
            method.ControlFlowGraph.Blocks.Add(terminal);
            recoveredHelpers.Add(terminal);
        }
        return InjectedCheckRemover.HasEquivalentImplicitFailure(method, helperBlock, exception, recoveredHelpers);
    }

    private static void AddGuard(ISILControlFlowGraph graph, Block helper, IOperand checkedValue,
        Instruction implicitFailure, int index)
    {
        var condition = Local($"condition{index}");
        var survivor = new Block
        {
            BlockType = BlockType.Fall,
            Instructions = [new Instruction(index + 2, implicitFailure.OpCode, implicitFailure.Operands.ToList())]
        };
        var guard = new Block
        {
            BlockType = BlockType.TwoWay,
            Instructions =
            [
                new Instruction(index, OpCode.CheckEqual, condition, checkedValue, new Immediate(0)),
                new Instruction(index + 1, OpCode.ConditionalJump, helper, condition)
            ],
            Successors = [survivor, helper]
        };
        survivor.Predecessors.Add(guard);
        helper.Predecessors.Add(guard);
        graph.EntryBlock.Successors.Add(guard);
        guard.Predecessors.Add(graph.EntryBlock);
        graph.Blocks.AddRange([guard, survivor]);
    }

    private static LocalVariable Local(string name) => new(name, new Register(null, name));
}
