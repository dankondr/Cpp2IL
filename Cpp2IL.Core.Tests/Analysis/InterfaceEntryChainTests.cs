using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Tests.Analysis;

public class InterfaceEntryChainTests
{
    [TestCase(4, 2, 0x138, true)]
    [TestCase(3, 2, 0x138, false)]
    [TestCase(4, 1, 0x138, false)]
    [TestCase(4, 2, 0x130, false)]
    public void Arm64EntryAddressRequiresExactScaleSlotAndLayout(int shift, int slot, int offset, bool matches)
    {
        LocalVariable Local(string name) => new(name, new Register(null, name));
        var receiver = Local("receiver");
        var klass = Local("klass");
        var tableEntry = Local("tableEntry");
        var entryOffset = Local("entryOffset");
        var index = Local("index");
        var extended = Local("extended");
        var scaled = Local("scaled");
        var sum = Local("sum");
        var address = Local("address");
        var definitions = new Dictionary<LocalVariable, Instruction>
        {
            [klass] = new(0, OpCode.Move, klass, new MemoryOperand(receiver)),
            [entryOffset] = new(1, OpCode.Move, entryOffset, new MemoryOperand(tableEntry)),
            [index] = new(2, OpCode.Add, index, entryOffset, new Immediate(slot)),
            [extended] = new(3, OpCode.SignExtend32, extended, index),
            [scaled] = new(4, OpCode.ShiftLeft, scaled, extended, new Immediate(shift)),
            [sum] = new(5, OpCode.Add, sum, klass, scaled),
        };
        var result = InterfaceDispatchRecovery.MatchVTableEntryChain(definitions,
            new Instruction(6, OpCode.Add, address, sum, new Immediate(offset)), 2);
        Assert.That(result, matches ? Is.SameAs(klass) : Is.Null);
    }
}
