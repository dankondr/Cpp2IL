using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: locals read only inside an address-take's compound target
// (castle-recovery#127). A slot copies the instance (`copy := this`) and is then used
// only as the receiver of field-address expressions (`&copy.field`), which later flow
// into pointer phis and reloads. The copy-forwarding passes used to substitute the
// field receiver at operand level but never inside `AddressOf`, and the liveness walk
// never counted a local read there either. The forwarding move (`copy := this`) was
// dropped while `&copy.field` still named the copy, so the emitted IL read a local
// that was never stored - decompiling to a C#-illegal `use of unassigned local`.
public class AddressOfReceiverForwardTests
{
    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static LocalVariable Local(string name, TypeAnalysisContext? type = null) =>
        new(name, new Register(null, name), type);

    private static FieldAnalysisContext Field(string name)
    {
        var app = App;
        return new InjectedFieldAnalysisContext(name, app.SystemTypes.SystemObjectType,
            R.FieldAttributes.Public, app.SystemTypes.SystemObjectType);
    }

    private static FieldReference ReceiverField(LocalVariable receiver) =>
        new(Field("value"), receiver, 16);

    private static FieldReference FieldInsideAddressOfUsedBy(Instruction call)
    {
        var address = (AddressOf)call.Operands[1];
        return (FieldReference)address.Target;
    }

    // The SSA-shape repro: `copy := receiver` is forwarded while `&copy.field` still names it.
    [Test]
    public void SsaSimplifierForwardsCopyIntoAddressOfFieldTarget()
    {
        var receiver = Local("receiver");
        var copy = Local("copy");
        var pointer = Local("pointer");

        var move = new Instruction(0, OpCode.Move, copy, receiver);
        var take = new Instruction(1, OpCode.Move, pointer, new AddressOf(ReceiverField(copy)));
        var call = new Instruction(2, OpCode.CallVoid, new StringLiteral("Read"), pointer, new Immediate(0));
        var graph = new ISILControlFlowGraph([move, take, call, new Instruction(3, OpCode.Return)]);

        SsaSimplifier.Run(graph, [receiver]);

        Assert.That(FieldInsideAddressOfUsedBy(call).Local, Is.SameAs(receiver),
            "the field receiver inside the address-take is forwarded to the copy's source");

        Assert.That(move.OpCode, Is.EqualTo(OpCode.Nop),
            "the copy has no remaining reads once the address-take names its source");
    }

    // A copy addressed only by cell identity (&copy) is a different cell, not a value: the
    // target must keep naming the copy so its defining move survives.
    [Test]
    public void SsaSimplifierKeepsBareAddressTargetAndItsDefinition()
    {
        var receiver = Local("receiver");
        var copy = Local("copy");
        var pointer = Local("pointer");

        var move = new Instruction(0, OpCode.Move, copy, receiver);
        var take = new Instruction(1, OpCode.Move, pointer, new AddressOf(copy));
        var call = new Instruction(2, OpCode.CallVoid, new StringLiteral("Store"), pointer, new Immediate(0));
        var graph = new ISILControlFlowGraph([move, take, call, new Instruction(3, OpCode.Return)]);

        SsaSimplifier.Run(graph, [receiver]);

        var address = (AddressOf)call.Operands[1];
        Assert.That(address.Target, Is.SameAs(copy),
            "&copy names the copy's own cell - forwarding would alias it with the source's");

        Assert.That(move.OpCode, Is.EqualTo(OpCode.Move),
            "the addressed local's defining move must stay");
    }

    // A slot copied from a local whose type can never hold the slot's declared type is a
    // bit-pattern copy with no legal managed store: forwarding the source into the field
    // receiver would emit an invalid ldflda, keeping the move emits an invalid stloc. The move
    // is dropped and the address-take keeps naming the unassigned slot, so the site stays a
    // decompiler diagnostic instead of invalid IL.
    [Test]
    public void SsaSimplifierDropsTypeIncompatibleCopy()
    {
        var other = Local("other", App.SystemTypes.SystemExceptionType);
        var copy = Local("copy", App.SystemTypes.SystemStringType);
        var pointer = Local("pointer");

        var move = new Instruction(0, OpCode.Move, copy, other);
        var take = new Instruction(1, OpCode.Move, pointer, new AddressOf(ReceiverField(copy)));
        var call = new Instruction(2, OpCode.CallVoid, new StringLiteral("Read"), pointer, new Immediate(0));
        var graph = new ISILControlFlowGraph([move, take, call, new Instruction(3, OpCode.Return)]);

        SsaSimplifier.Run(graph, [other]);

        Assert.That(move.OpCode, Is.EqualTo(OpCode.Nop),
            "a copy between mutually incompatible reference types has no legal managed store");
        Assert.That(FieldInsideAddressOfUsedBy(call).Local, Is.SameAs(copy),
            "the mismatched source is never forwarded into the field receiver position");
    }

    // The post-SSA form of the same bit-pattern copy.
    [Test]
    public void SimplifierDropsTypeIncompatibleCopy()
    {
        var other = Local("other", App.SystemTypes.SystemExceptionType);
        var copy = Local("copy", App.SystemTypes.SystemStringType);
        var pointer = Local("pointer");

        var move = new Instruction(0, OpCode.Move, copy, other);
        var take = new Instruction(1, OpCode.Move, pointer, new AddressOf(ReceiverField(copy)));
        var call = new Instruction(2, OpCode.CallVoid, new StringLiteral("Read"), pointer, new Immediate(0));
        var graph = new ISILControlFlowGraph([move, take, call, new Instruction(3, OpCode.Return)]);
        var method = CreateMethod(graph, other, copy, pointer);

        Simplifier.Simplify(method);

        Assert.That(move.OpCode, Is.EqualTo(OpCode.Nop),
            "a copy between mutually incompatible reference types has no legal managed store");
        Assert.That(FieldInsideAddressOfUsedBy(call).Local, Is.SameAs(copy),
            "the mismatched source is never forwarded into the field receiver position");
    }

    // The post-SSA shape: phi lowering emits plain `pointer := &copy.field` copies, which the
    // non-SSA simplifier must forward the same way.
    [Test]
    public void SimplifierForwardsCopyIntoAddressOfFieldTarget()
    {
        var receiver = Local("receiver");
        var copy = Local("copy");
        var pointer = Local("pointer");

        var move = new Instruction(0, OpCode.Move, copy, receiver);
        var take = new Instruction(1, OpCode.Move, pointer, new AddressOf(ReceiverField(copy)));
        var call = new Instruction(2, OpCode.CallVoid, new StringLiteral("Read"), pointer, new Immediate(0));
        var graph = new ISILControlFlowGraph([move, take, call, new Instruction(3, OpCode.Return)]);
        var method = CreateMethod(graph, receiver, copy, pointer);

        Simplifier.Simplify(method);

        Assert.That(FieldInsideAddressOfUsedBy(call).Local, Is.SameAs(receiver),
            "the field receiver inside the address-take is forwarded to the copy's source");

        Assert.That(move.OpCode, Is.EqualTo(OpCode.Nop),
            "the copy has no remaining reads once the address-take names its source");
    }

    // A memory-operand target is a compound like a field receiver: its base/index locals are
    // value positions that forwarding must reach too.
    [Test]
    public void SimplifierForwardsCopyIntoAddressOfMemoryTarget()
    {
        var receiver = Local("receiver");
        var copy = Local("copy");
        var pointer = Local("pointer");

        var move = new Instruction(0, OpCode.Move, copy, receiver);
        var take = new Instruction(1, OpCode.Move, pointer, new AddressOf(new MemoryOperand(copy, null, 8, 0)));
        var call = new Instruction(2, OpCode.CallVoid, new StringLiteral("Read"), pointer, new Immediate(0));
        var graph = new ISILControlFlowGraph([move, take, call, new Instruction(3, OpCode.Return)]);
        var method = CreateMethod(graph, receiver, copy, pointer);

        Simplifier.Simplify(method);

        var address = (AddressOf)call.Operands[1];
        Assert.That(((MemoryOperand)address.Target).Base, Is.SameAs(receiver),
            "the memory base inside the address-take is forwarded to the copy's source");

        Assert.That(move.OpCode, Is.EqualTo(OpCode.Nop),
            "the copy has no remaining reads once the address-take names its source");
    }

    private static MethodAnalysisContext CreateMethod(ISILControlFlowGraph graph, params LocalVariable[] locals)
    {
        var method = (MethodAnalysisContext)RuntimeHelpers.GetUninitializedObject(typeof(MethodAnalysisContext));
        method.ControlFlowGraph = graph;
        method.Locals = locals.ToList();
        method.ParameterLocals = [];
        return method;
    }
}
