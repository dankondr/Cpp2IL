using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class GotMetadataTests
{
    [Test]
    public void ResolvesOnlyTheSecondLoadThroughAKnownGotSlot()
    {
        var address = new LocalVariable("slot", new Register(null, "x20"));
        var value = new LocalVariable("value", new Register(null, "x0"));
        var unknown = new LocalVariable("unknown", new Register(null, "x19"));
        var gotLoad = new Instruction(0, OpCode.Move, address, new MemoryOperand(addend: 0x1000));
        var valueLoad = new Instruction(1, OpCode.Move, value, new MemoryOperand(address));
        var offsetLoad = new Instruction(2, OpCode.Move, value, new MemoryOperand(address, addend: 8));
        var unknownAddress = new Instruction(3, OpCode.Move, unknown, new MemoryOperand(addend: 0x1010));
        var unknownLoad = new Instruction(4, OpCode.Move, value, new MemoryOperand(unknown));
        var graph = new ISILControlFlowGraph(new List<Instruction> { gotLoad, valueLoad, offsetLoad, unknownAddress, unknownLoad, new(5, OpCode.Return) });

        MetadataResolver.ResolveGotLoads(graph, location => location == 0x1000 ? 0x2000UL : null);

        Assert.That(valueLoad.Operands[1], Is.EqualTo(new MemoryOperand(addend: 0x2000)));
        Assert.That(gotLoad.Operands[1], Is.EqualTo(new MemoryOperand(addend: 0x1000)));
        Assert.That(offsetLoad.Operands[1], Is.EqualTo(new MemoryOperand(address, addend: 8)));
        Assert.That(unknownLoad.Operands[1], Is.EqualTo(new MemoryOperand(unknown)));
        Assert.That(unknownAddress.Operands[1], Is.EqualTo(new MemoryOperand(addend: 0x1010)));
    }
}
