using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Analysis;

public class GotMetadataTests
{
    [Test]
    public void ConcreteHiddenMethodInfoOverridesSingleSharedThunkCandidate()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = app.SystemTypes.SystemObjectType;
        var represented = new InjectedMethodAnalysisContext(owner, "Resolved", app.SystemTypes.SystemObjectType,
            R.MethodAttributes.Public, []);
        var wrong = new InjectedMethodAnalysisContext(owner, "Wrong", app.SystemTypes.SystemObjectType,
            R.MethodAttributes.Public, []);
        const ulong address = 0x123456;
        app.MethodsByAddress[address] = [wrong];
        var result = new LocalVariable("result", new Register(null, "x0"));
        var receiver = new LocalVariable("receiver", new Register(null, "x1")) { Type = owner };
        var hidden = new LocalVariable("hidden", new Register(null, "x2"));
        var caller = new InjectedMethodAnalysisContext(owner, "Caller", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public, []);
        var call = new Instruction(0, OpCode.Call, new Immediate((long)address), result, receiver, hidden);
        caller.ControlFlowGraph = new ISILControlFlowGraph([call, new Instruction(1, OpCode.Return)]);

        Assert.That(MetadataResolver.ResolveCallsViaMethodInfo(caller), Is.False);
        call.SetOperand(3, new RuntimeMethodInfoAnalysisContext(represented, owner.DeclaringAssembly));
        Assert.That(MetadataResolver.ResolveCallsViaMethodInfo(caller), Is.True);
        Assert.That(call.Operands[0], Is.SameAs(represented));
    }

    [Test]
    public void LiftsKnownRelroSlotBeforeDereference()
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

        Assert.That(valueLoad.Operands[1], Is.SameAs(address));
        Assert.That(gotLoad.Operands[1], Is.EqualTo(new MemoryOperand(addend: 0x2000)));
        Assert.That(offsetLoad.Operands[1], Is.EqualTo(new MemoryOperand(address, addend: 8)));
        Assert.That(unknownLoad.Operands[1], Is.EqualTo(new MemoryOperand(unknown)));
        Assert.That(unknownAddress.Operands[1], Is.EqualTo(new MemoryOperand(addend: 0x1010)));
    }

    [Test]
    public void PropagatesMetadataSlotsThroughPhiBeforeDereference()
    {
        var left = new LocalVariable("left", new Register(null, "x9", 1));
        var right = new LocalVariable("right", new Register(null, "x9", 2));
        var merged = new LocalVariable("merged", new Register(null, "x9", 3));
        var leftLoad = new Instruction(0, OpCode.Move, left, new MemoryOperand(addend: 0x1000));
        var rightLoad = new Instruction(1, OpCode.Move, right, new MemoryOperand(addend: 0x1010));
        var phi = new Instruction(2, OpCode.Phi, merged, left, right);
        var ret = new Instruction(3, OpCode.Return, new MemoryOperand(merged));
        var graph = new ISILControlFlowGraph(new List<Instruction> { leftLoad, rightLoad, phi, ret });

        MetadataResolver.ResolveGotLoads(graph, location => location switch
        {
            0x1000 => 0x2000,
            0x1010 => 0x2010,
            _ => null
        });

        Assert.That(leftLoad.Operands[1], Is.EqualTo(new MemoryOperand(addend: 0x2000)));
        Assert.That(rightLoad.Operands[1], Is.EqualTo(new MemoryOperand(addend: 0x2010)));
        Assert.That(ret.Operands[0], Is.SameAs(merged));
    }
}
