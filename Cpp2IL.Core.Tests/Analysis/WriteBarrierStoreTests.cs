using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class WriteBarrierStoreTests
{
    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;
    private static AssemblyAnalysisContext Mscorlib => App.AssembliesByName["mscorlib"];

    private static InjectedMethodAnalysisContext Caller()
        => new(App.SystemTypes.SystemObjectType, "Store",
            App.SystemTypes.SystemVoidType, MethodAttributes.Static, []);

    private static StringLiteral WriteBarrier => new("il2cpp_codegen_write_barrier");

    [Test]
    public void WriteBarrierRewritesToTheStoreItPerforms()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var method = Caller();
        var cell = new LocalVariable("cell", new Register(null, "stack_-20"));
        var address = new LocalVariable("address", new Register(null, "address"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var value = new LocalVariable("value", new Register(null, "value"),
            App.SystemTypes.SystemStringType);
        var barrier = new Instruction(2, OpCode.Call, WriteBarrier, result, address, value);
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, address, new AddressOf(cell)),
            new(1, OpCode.Move, cell, new Immediate(0)),
            barrier,
            new(3, OpCode.Return)]);

        KeyFunctionRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(barrier.OpCode, Is.EqualTo(OpCode.Move));
            Assert.That(barrier.Operands, Has.Count.EqualTo(2));
            Assert.That(barrier.Operands[0], Is.SameAs(cell));
            Assert.That(barrier.Operands[1], Is.SameAs(value));
        });
    }

    [Test]
    public void WriteBarrierValueFollowsRegisterCopiesToTheStoredObject()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var method = Caller();
        var cell = new LocalVariable("cell", new Register(null, "stack_-20"));
        var address = new LocalVariable("address", new Register(null, "address"));
        var copy = new LocalVariable("copy", new Register(null, "copy"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var value = new LocalVariable("value", new Register(null, "value"),
            App.SystemTypes.SystemStringType);
        var barrier = new Instruction(3, OpCode.Call, WriteBarrier, result, address, copy);
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, address, new AddressOf(cell)),
            new(1, OpCode.Move, copy, value),
            new(2, OpCode.Move, cell, new Immediate(0)),
            barrier,
            new(4, OpCode.Return)]);

        KeyFunctionRecovery.Run(method);

        // the barrier's arg register is a copy of `value`; the recovered store writes what was
        // actually stored - `value`, whose declared type survives to type the cell
        Assert.Multiple(() =>
        {
            Assert.That(barrier.OpCode, Is.EqualTo(OpCode.Move));
            Assert.That(barrier.Operands[0], Is.SameAs(cell));
            Assert.That(barrier.Operands[1], Is.SameAs(value));
        });
    }

    [Test]
    public void WriteBarrierWithoutResolvableCellFallsBackToNop()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var method = Caller();
        var address = new LocalVariable("address", new Register(null, "address"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var value = new LocalVariable("value", new Register(null, "value"),
            App.SystemTypes.SystemStringType);
        // the destination came from arithmetic, not `&cell` - the written slot cannot be named
        var barrier = new Instruction(2, OpCode.Call, WriteBarrier, result, address, value);
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Add, address, new Immediate(0), new Immediate(0)),
            new(1, OpCode.Move, result, new Immediate(0)),
            barrier,
            new(3, OpCode.Return)]);

        KeyFunctionRecovery.Run(method);

        Assert.That(barrier.OpCode, Is.EqualTo(OpCode.Nop));
    }

    [Test]
    public void ClobberedCellVersionInheritsTypeOfTheWrittenValue()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        // a versioned stack cell that is used but never defined is the clobbered content of an
        // escape - it inherits the type of the cell's most recent typed earlier version, so a
        // later reader still sees the object the slot holds.
        var owner = new InjectedTypeAnalysisContext(Mscorlib, "Tests", "Holder",
            App.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var payload = new InjectedFieldAnalysisContext("payload",
            App.SystemTypes.SystemInt32Type, FieldAttributes.Public, owner, 16);
        owner.Fields.Add(payload);

        var method = Caller();
        var cellV1 = new LocalVariable("cellV1", new Register(null, "stack_-20", 1));
        var cellV2 = new LocalVariable("cellV2", new Register(null, "stack_-20", 2));
        var value = new LocalVariable("value", new Register(null, "value"), owner);
        var reader = new LocalVariable("reader", new Register(null, "reader"));
        var loaded = new LocalVariable("loaded", new Register(null, "loaded"));
        var read = new Instruction(2, OpCode.Move, loaded,
            new MemoryOperand(reader, addend: 16, accessSize: 4));
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, cellV1, value),
            new(1, OpCode.Move, reader, cellV2),
            read,
            new(3, OpCode.Return)]);
        method.Locals = [cellV1, cellV2, value, reader, loaded];
        method.ParameterLocals = [];

        LocalVariables.ResolveTypesAndFields(method);

        Assert.Multiple(() =>
        {
            Assert.That(cellV2.Type, Is.SameAs(owner));
            Assert.That(reader.Type, Is.SameAs(owner));
            Assert.That(read.Operands[1], Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)read.Operands[1]).Field, Is.SameAs(payload));
        });
    }
}
