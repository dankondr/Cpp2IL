using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: compile bucket CS0039 (castle-recovery#123). A register reused
// for a differently-typed value binds its stale SSA version to an isinst/castclass
// source slot: SsaSimplifier did not count the cast operand as a read and never
// forwarded it, so the producing Move was dead-code eliminated and the emitted
// local fell back to object or kept a register-reuse type. CopyCoalescer had the
// same blind spot - the operand was neither liveness-counted nor rebound to the
// merged representative. The slot is a use like any other: the operand must
// forward to the produced version, or the producing Move must survive.
public class CastOperandUseTests
{
    // The cast reads its operand's emitted local, so that local's declared type
    // is the type the isinst sees. Read from the locals signature: the fixtures
    // produce the value with a stubbed (throwing) load, so the cast itself is
    // unreachable and never emitted.
    private static string? CastOperandLocalType(MethodAnalysisContext caller, AsmResolver.DotNet.MethodDefinition method,
        Instruction cast)
        => method.CilMethodBody!.LocalVariables[caller.Locals.IndexOf(((ReferenceCast)cast.Operands[1]).Value)]
            .VariableType?.FullName;

    [Test]
    public void SsaSimplifierForwardsCastOperandToProducedVersion()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var target = app.SystemTypes.SystemExceptionType;
        var x8 = new Register(8, "x8");
        var produced = new LocalVariable("produced", x8.Copy(1))
            { Type = app.SystemTypes.SystemStringType };
        var intVersion = new LocalVariable("intVersion", x8.Copy(2))
            { Type = app.SystemTypes.SystemInt32Type };
        var staleCopy = new LocalVariable("staleCopy", x8.Copy(3))
            { Type = app.SystemTypes.SystemInt32Type };
        var baseLocal = new LocalVariable("base", new Register(null, "base"));
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = target };
        var sink = new LocalVariable("sink", new Register(null, "sink"))
            { Type = app.SystemTypes.SystemInt32Type };
        var module = new ModuleDefinition("CastForward.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemStringType, target,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemInt32Type);
        var castInstruction = new Instruction(3, OpCode.Move, result,
            new ReferenceCast(staleCopy, target, true));
        var (caller, method) = ForeignCaller(app, module, [
            new Instruction(0, OpCode.Move, produced, new MemoryOperand(baseLocal, addend: 0, accessSize: 8)),
            new Instruction(1, OpCode.Move, intVersion, new Immediate(0x2A)),
            new Instruction(2, OpCode.Move, staleCopy, produced),
            castInstruction,
            new Instruction(4, OpCode.Move, sink, intVersion),
            new Instruction(5, OpCode.Return)],
            [produced, intVersion, staleCopy, baseLocal, result, sink]);

        SsaSimplifier.Run(caller.ControlFlowGraph!, [result]);
        CopyCoalescer.Run(caller.ControlFlowGraph!);
        IlGenerator.GenerateIl(caller, method);

        Assert.Multiple(() =>
        {
            Assert.That(((ReferenceCast)castInstruction.Operands[1]).Value, Is.SameAs(produced),
                "the cast operand must forward through the copy to the produced version");
            Assert.That(CastOperandLocalType(caller, method, castInstruction), Is.EqualTo("System.String"),
                "the emitted local must carry the producer's proven type");
        });
    }

    [Test]
    public void CopyCoalescerRebindsCastOperandToProducerRepresentative()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var target = app.SystemTypes.SystemExceptionType;
        var x8 = new Register(8, "x8");
        var produced = new LocalVariable("produced", x8.Copy(1))
            { Type = app.SystemTypes.SystemStringType };
        var slot = new LocalVariable("slot", x8.Copy(2));
        var baseLocal = new LocalVariable("base", new Register(null, "base"));
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = target };
        var module = new ModuleDefinition("CastCoalesce.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemStringType, target,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var castInstruction = new Instruction(2, OpCode.Move, result,
            new ReferenceCast(slot, target, true));
        var (caller, method) = ForeignCaller(app, module, [
            new Instruction(0, OpCode.Move, produced, new MemoryOperand(baseLocal, addend: 0, accessSize: 8)),
            new Instruction(1, OpCode.Move, slot, produced),
            castInstruction,
            new Instruction(3, OpCode.Return)],
            [produced, slot, baseLocal, result]);

        CopyCoalescer.Run(caller.ControlFlowGraph!);
        IlGenerator.GenerateIl(caller, method);

        Assert.Multiple(() =>
        {
            Assert.That(((ReferenceCast)castInstruction.Operands[1]).Value, Is.SameAs(produced),
                "the cast operand must rebind to the coalesced representative");
            Assert.That(CastOperandLocalType(caller, method, castInstruction), Is.EqualTo("System.String"),
                "the emitted local must carry the producer's proven type");
        });
    }

    [Test]
    public void CastUseKeepsOperandVersionLiveAcrossConflictingDefinition()
    {
        // The `param as T` shape: the slot's produced version and a value-typed
        // version of the same register are concurrently live. Without the cast
        // counted as a use, the produced version looks dead past the int version's
        // definition, no interference edge is recorded, and the two merge into the
        // int-typed representative - orphaning the operand (previously object,
        // now binding straight to the int version).
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var target = app.SystemTypes.SystemExceptionType;
        var x8 = new Register(8, "x8");
        var produced = new LocalVariable("produced", x8.Copy(1));
        var slot = new LocalVariable("slot", x8.Copy(2));
        var intVersion = new LocalVariable("intVersion", x8.Copy(3))
            { Type = app.SystemTypes.SystemInt32Type };
        var baseLocal = new LocalVariable("base", new Register(null, "base"));
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = target };
        var sink = new LocalVariable("sink", new Register(null, "sink"));
        var useInt = new LocalVariable("useInt", new Register(null, "useInt"));
        var module = new ModuleDefinition("CastInterfere.dll");
        SeedCorLibTypes(app, module, target, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemInt32Type);
        var castInstruction = new Instruction(3, OpCode.Move, result,
            new ReferenceCast(slot, target, true));
        var (caller, method) = ForeignCaller(app, module, [
            new Instruction(0, OpCode.Move, produced, new MemoryOperand(baseLocal, addend: 0, accessSize: 8)),
            new Instruction(1, OpCode.Move, slot, produced),
            new Instruction(2, OpCode.Move, intVersion, new Immediate(0x2A)),
            castInstruction,
            new Instruction(4, OpCode.Move, slot, intVersion),
            new Instruction(5, OpCode.Move, sink, slot),
            new Instruction(6, OpCode.Move, useInt, intVersion),
            new Instruction(7, OpCode.Return)],
            [produced, slot, intVersion, baseLocal, result, sink, useInt]);

        CopyCoalescer.Run(caller.ControlFlowGraph!);
        IlGenerator.GenerateIl(caller, method);

        var castOperand = ((ReferenceCast)castInstruction.Operands[1]).Value;
        Assert.Multiple(() =>
        {
            Assert.That(castOperand, Is.Not.SameAs(intVersion),
                "the operand must not bind to the concurrently-typed int version");
            Assert.That(caller.ControlFlowGraph!.Instructions
                    .Any(i => ReferenceEquals(i.Destination, castOperand)), Is.True,
                "the operand's version must keep a producer after coalescing");
            Assert.That(CastOperandLocalType(caller, method, castInstruction), Is.EqualTo("System.Object"),
                "the merged slot carries no proven type, so the slot contract owns the type");
        });
    }
}
