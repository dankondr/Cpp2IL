using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: memory — address-takes and hidden-return windows follow control
// flow, not the linear instruction list (castle-recovery#319). Two shapes from the
// game's store traffic regressed in the same way: a write whose effective position
// was computed from list order lost the value, because the block holding the store
// (or the copy) sat further down the flat list than the next branch arm's code.
public class MemoryStoreWindowTests
{
    private static ISILControlFlowGraph Graph(IReadOnlyList<Instruction> instructions)
    {
        foreach (var instruction in instructions)
            if (instruction.OpCode is OpCode.Jump or OpCode.ConditionalJump
                && instruction.Operands[0] is Immediate { Value: { } immediate })
                instruction.SetOperand(0, instructions[(int)immediate]);
        return new ISILControlFlowGraph(instructions.ToList());
    }

    // A hoisted `mov ptr, &slot` whose block ends with the pointer live and no slot
    // definition: the store can sit in a dominated successor before the pointer is
    // read. The take must be sunk to just before that first read or it binds the
    // stale pre-store version and the real store dies unread.
    [Test]
    public void AddressTakeSinksIntoDominatedReadBlock()
    {
        var slot = new Register(101, "slot");
        var pointer = new Register(102, "ptr");
        var value = new Register(103, "val");
        var condition = new Register(104, "cond");
        var sink = new Register(105, "sink");

        var take = new Instruction(1, OpCode.Move, pointer, new AddressOf(slot));
        var store = new Instruction(3, OpCode.Move, slot, value);
        var read = new Instruction(4, OpCode.Move, sink, pointer);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, slot, new Immediate(0)),
            take,
            new(2, OpCode.ConditionalJump, new Immediate(6), condition),
            store,
            read,
            new(5, OpCode.Jump, new Immediate(8)),
            new(6, OpCode.Nop),
            new(7, OpCode.Jump, new Immediate(8)),
            new(8, OpCode.Return),
        };
        var graph = Graph(instructions);
        var blocks = graph.Blocks;
        var readBlock = blocks.First(b => b.Instructions.Contains(read));

        SsaForm.Build(graph, new DominatorInfo(graph));

        Assert.Multiple(() =>
        {
            Assert.That(readBlock.Instructions, Does.Contain(take));
            Assert.That(readBlock.Instructions.IndexOf(take),
                Is.LessThan(readBlock.Instructions.IndexOf(read)));
        });
    }

    // Two arms each call a >16B-struct-returning method through x8 into the same
    // stack cell and copy the result on. In the flat list the first arm's copy sits
    // below the second arm's call, so an index-bounded window let the later call
    // claim (or strand) the earlier read. Each arm's reads must bind that arm's
    // result instead.
    [Test]
    public void HiddenReturnCopiesBindTheirOwnArm()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var structType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests",
            "WideStruct", app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!,
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout);
        var target = new InjectedMethodAnalysisContext(owner, "Produce", structType,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var method = new InjectedMethodAnalysisContext(owner, "Consume",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);

        var buffer = new LocalVariable("buffer", new Register(null, "stack_-60"), structType);
        var pointer1 = new LocalVariable("p1", new Register(null, "p1"));
        var pointer2 = new LocalVariable("p2", new Register(null, "p2"));
        var out1 = new LocalVariable("out1", new Register(null, "stack_-80"), structType);
        var out2 = new LocalVariable("out2", new Register(null, "stack_-A0"), structType);
        var condition = new LocalVariable("cond", new Register(null, "cond"));

        var call1 = new Instruction(2, OpCode.Call, target, new MemoryOperand(pointer1));
        var call2 = new Instruction(5, OpCode.Call, target, new MemoryOperand(pointer2));
        var copy1 = new Instruction(7, OpCode.Move, out1, buffer);
        var copy2 = new Instruction(9, OpCode.Move, out2, buffer);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.ConditionalJump, new Immediate(4), condition),
            new(1, OpCode.Move, pointer1, new AddressOf(buffer)),
            call1,
            new(3, OpCode.Jump, new Immediate(7)),
            new(4, OpCode.Move, pointer2, new AddressOf(buffer)),
            call2,
            new(6, OpCode.Jump, new Immediate(9)),
            copy1,
            new(8, OpCode.Jump, new Immediate(10)),
            copy2,
            new(10, OpCode.Return),
        };
        var graph = Graph(instructions);
        method.ControlFlowGraph = graph;
        method.DominatorInfo = new DominatorInfo(graph);
        method.Locals.AddRange([buffer, pointer1, pointer2, out1, out2]);

        LocalVariables.ResolveHiddenReturnBuffers(method);

        Assert.Multiple(() =>
        {
            Assert.That(call1.Destination, Is.SameAs(out1), "arm 1 call should land in arm 1's result local");
            Assert.That(call2.Destination, Is.SameAs(out2), "arm 2 call should land in arm 2's result local");
            Assert.That(copy1.Operands[1], Is.SameAs(out1),
                () => $"arm 1's buffer copy reads {copy1.Operands[1]} instead of its own result");
            Assert.That(copy2.Operands[1], Is.SameAs(out2),
                () => $"arm 2's buffer copy reads {copy2.Operands[1]} instead of its own result");
        });
    }
}
