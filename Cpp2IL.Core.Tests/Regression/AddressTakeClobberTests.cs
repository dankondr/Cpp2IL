using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: address-takes that never leave the frame (castle-recovery#108).
// A finalizer spills `this` into a slot, publishes &slot into the exception-handling
// record stored at another frame offset, then reloads the slot for the base call.
// The pointer is only ever read back inside the same frame - nothing can write
// through it - so the reload must still bind `this`. Marking every address-take as
// a clobber used to leave the reload on an unproduced version, which emitted an
// unassigned `object` receiver and decompiled to a C#-illegal `local.Finalize()`.
public class AddressTakeClobberTests
{
    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    // A Derived.Run instance caller plus a virtual Base.Cleanup callee standing in
    // for the base call; the AsmResolver members the emitted IL has to name.
    private static (InjectedMethodAnalysisContext caller, MethodDefinition method,
            InjectedMethodAnalysisContext callee)
        NewFixture(ApplicationAnalysisContext app)
    {
        var baseType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Base",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var callee = baseType.InjectMethodContext("Cleanup", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Virtual, []);
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Derived",
            baseType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = owner.InjectMethodContext("Run", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public, []);

        var module = new ModuleDefinition("FrameRecord.dll");
        var baseDefinition = new TypeDefinition("Tests", "Base",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(baseDefinition);
        baseType.PutExtraData("AsmResolverType", baseDefinition);
        var calleeDefinition = new MethodDefinition("Cleanup",
            MethodAttributes.Public | MethodAttributes.Virtual,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        baseDefinition.Methods.Add(calleeDefinition);
        callee.PutExtraData("AsmResolverMethod", calleeDefinition);

        var ownerDefinition = new TypeDefinition("Tests", "Derived",
            TypeAttributes.Public | TypeAttributes.Class, baseDefinition);
        module.TopLevelTypes.Add(ownerDefinition);
        owner.PutExtraData("AsmResolverType", ownerDefinition);
        var method = new MethodDefinition("Run", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        ownerDefinition.Methods.Add(method);

        return (caller, method, callee);
    }

    [Test]
    public void FrameRecordAddressTakeKeepsThisReceiver()
    {
        var app = App;
        var thisRegister = new Register(null, "X0");
        var slot = new Register(null, "slot");
        var (caller, method, callee) = NewFixture(app);

        // The EH idiom: spill this, publish &slot into a frame record, read the record
        // back and load through it, then reload the slot for the base call.
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, slot, thisRegister),
            new Instruction(1, OpCode.Move, new Register(null, "X8"), new AddressOf(slot)),
            new Instruction(2, OpCode.Move, new Register(null, "record"), new Register(null, "X8")),
            new Instruction(3, OpCode.Move, new Register(null, "scratch"), new Register(null, "record")),
            new Instruction(4, OpCode.Move, new Register(null, "X1"),
                new MemoryOperand(new Register(null, "scratch"))),
            new Instruction(5, OpCode.Move, thisRegister, slot),
            new Instruction(6, OpCode.CallVoid, callee, thisRegister),
            new Instruction(7, OpCode.Return),
        ]);
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph);
        caller.ParameterOperands = [thisRegister];
        caller.AnalysisWarnings = [];

        SsaForm.Build(caller);

        // The reload must read the spilled version - the take creates no orphaned version.
        var reload = caller.ControlFlowGraph.Instructions.Single(i =>
            i.OpCode == OpCode.Move && i.Destination is Register { Name: "X0" });
        var spill = caller.ControlFlowGraph.Instructions.Single(i =>
            i.OpCode == OpCode.Move && i.Destination is Register { Name: "slot" });
        Assert.That(((Register)reload.Operands[1]).Version,
            Is.EqualTo(((Register)spill.Operands[0]).Version));

        LocalVariables.CreateAll(caller);
        LocalVariables.ResolveTypesAndFields(caller);
        SsaSimplifier.Run(caller);
        SsaForm.Remove(caller);
        CopyCoalescer.Run(caller);
        LocalVariables.ResolveLateGeneratedTypes(caller);

        IlGenerator.GenerateIl(caller, method);

        // The receiver is `this`, which emits as ldarg.0. Checked on the call
        // itself: the load through the record is an unmanaged-load stub that
        // throws, so the base call after it is unreachable and never emitted.
        var cleanup = caller.ControlFlowGraph.Instructions.Single(i => i.OpCode == OpCode.CallVoid);
        Assert.That(cleanup.Operands[1] is LocalVariable { IsThis: true }, Is.True,
            () => string.Join("\n", caller.ControlFlowGraph.Instructions));
    }

    [Test]
    public void CarrierReassignedBeforeUseDoesNotClobber()
    {
        // The pointer's register is free for reuse once reassigned: a fresh load kills
        // the carrier, so passing the reused register to a call cannot publish &slot.
        var app = App;
        var thisRegister = new Register(null, "X0");
        var slot = new Register(null, "slot");
        var pointer = new Register(null, "X8");
        var carrierCopy = new Register(null, "X2");
        var callerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests",
            "Derived", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = callerType.InjectMethodContext("Run", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, slot, thisRegister),
            new Instruction(1, OpCode.Move, pointer, new AddressOf(slot)),
            new Instruction(2, OpCode.Move, pointer,
                new MemoryOperand(thisRegister, null, 8)),
            new Instruction(3, OpCode.Move, carrierCopy, pointer),
            new Instruction(4, OpCode.CallVoid, caller, carrierCopy),
            new Instruction(5, OpCode.Move, thisRegister, slot),
            new Instruction(6, OpCode.Return),
        ]);
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph);
        caller.ParameterOperands = [thisRegister];
        caller.AnalysisWarnings = [];

        SsaForm.Build(caller);

        var reload = caller.ControlFlowGraph.Instructions.Last(i =>
            i.OpCode == OpCode.Move && i.Destination is Register { Name: "X0" });
        var spill = caller.ControlFlowGraph.Instructions.Single(i =>
            i.OpCode == OpCode.Move && i.Destination is Register { Name: "slot" });
        Assert.That(((Register)reload.Operands[1]).Version,
            Is.EqualTo(((Register)spill.Operands[0]).Version),
            "a reassigned carrier cannot publish the pointer, so the reload keeps the spill's version");
    }

    [Test]
    public void StoreThroughAddressTakenSlotStillClobbers()
    {
        // The clobber still has to fire where the pointer can actually write: a store
        // through &slot means the reload can no longer see the spilled value.
        var app = App;
        var thisRegister = new Register(null, "X0");
        var slot = new Register(null, "slot");
        var pointer = new Register(null, "X8");
        var callerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests",
            "Derived", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = callerType.InjectMethodContext("Run", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, slot, thisRegister),
            new Instruction(1, OpCode.Move, pointer, new AddressOf(slot)),
            new Instruction(2, OpCode.Move, new MemoryOperand(pointer), thisRegister),
            new Instruction(3, OpCode.Move, thisRegister, slot),
            new Instruction(4, OpCode.Return),
        ]);
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph);
        caller.ParameterOperands = [thisRegister];
        caller.AnalysisWarnings = [];

        SsaForm.Build(caller);

        var reload = caller.ControlFlowGraph.Instructions.Last(i =>
            i.OpCode == OpCode.Move && i.Destination is Register { Name: "X0" });
        var spill = caller.ControlFlowGraph.Instructions.Single(i =>
            i.OpCode == OpCode.Move && i.Destination is Register { Name: "slot" });
        Assert.That(((Register)reload.Operands[1]).Version,
            Is.GreaterThan(((Register)spill.Operands[0]).Version),
            "a write through the published pointer must still clobber the slot");
    }
}
