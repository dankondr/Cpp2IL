using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Analysis;

public class StackProtectorRecoveryTests
{
    private ApplicationAnalysisContext _app = null!;
    private TypeAnalysisContext _int64 = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
        _int64 = _app.SystemTypes.SystemInt64Type;
        _app.InstructionSet = new NewArmV8InstructionSet();
    }

    private static LocalVariable Reg(string registerName, TypeAnalysisContext? type = null, int version = -1) =>
        new($"v_{registerName}_{version}", new Register(null, registerName, version), type);

    private MethodAnalysisContext Caller()
    {
        var caller = new InjectedMethodAnalysisContext(
            _app.SystemTypes.SystemObjectType, "F",
            _app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, [])
        {
            ParameterLocals = [],
            AnalysisWarnings = [],
        };
        return caller;
    }

    // A TwoWay guard whose compare reads the TLS cell [SYSREG+0x28] on one side,
    // branching to a block that calls __stack_chk_fail. failTargetName drives
    // the fail block's call target; canary=false swaps the compare for a plain
    // value comparison.
    private (MethodAnalysisContext caller, Instruction branch, Instruction failCall)
        CanaryGuard(string failTargetName, bool canary = true)
    {
        var caller = Caller();
        var sysLocal = new LocalVariable("v_sys", new Register(null, "SYSREG"), _int64);
        var tls = Reg("X23", _int64, 1);
        var spilled = Reg("X8", _int64, 38);
        var frame = Reg("X29", _int64, 1);
        var cond = Reg("TEMPCOND", _app.SystemTypes.SystemBooleanType, 20);

        var failCallInsn = new Instruction(5, OpCode.Call, new StringLiteral(failTargetName),
            Reg("X0", version: 2));
        var failReturn = new Instruction(6, OpCode.Return);
        var mergeReturn = new Instruction(4, OpCode.Return, Reg("X0", version: 3));
        var branch = new Instruction(3, OpCode.ConditionalJump, failCallInsn, cond);

        var check = canary
            ? new Instruction(2, OpCode.CheckNotEqual, cond,
                new MemoryOperand(spilled, null, 0x28),
                new MemoryOperand(tls, null, 0x28))
            : new Instruction(2, OpCode.CheckNotEqual, cond,
                Reg("X8", _int64, 40), Reg("X9", _int64, 41));

        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, tls, sysLocal),
            new Instruction(1, OpCode.Move, spilled, new MemoryOperand(frame, null, -60)),
            check,
            branch,
            mergeReturn,
            failCallInsn,
            failReturn,
        ]);
        caller.Locals = [sysLocal, tls, spilled, frame, cond];
        return (caller, branch, failCallInsn);
    }

    [Test]
    public void CanaryGuardFoldsToMergeAndExcisesFailBlock()
    {
        var (caller, branch, failCall) = CanaryGuard("__stack_chk_fail");

        StackProtectorRecovery.Run(caller);

        var cfg = caller.ControlFlowGraph!;
        Assert.That(branch.OpCode, Is.EqualTo(OpCode.Jump));
        Assert.That(failCall.OpCode, Is.EqualTo(OpCode.Nop));
        Assert.That(cfg.Blocks.Any(b => b.Instructions.Contains(failCall)), Is.False,
            "the dedicated fail block must become unreachable and be removed");
    }

    // The other real compare shape: the stored canary as a plain local operand
    // against the TLS cell.
    [Test]
    public void CanaryGuardWithLocalStoredCanaryFolds()
    {
        var (caller, branch, failCall) = CanaryGuard("__stack_chk_fail");
        var stored = Reg("X9", _int64, 50);
        caller.Locals!.Add(stored);
        var check = caller.ControlFlowGraph!.Blocks
            .SelectMany(b => b.Instructions)
            .First(i => i.OpCode == OpCode.CheckNotEqual);
        // Replace the spilled-TLS side with a plain local: [TLS+28] vs local.
        check.SetOperand(1, stored);

        StackProtectorRecovery.Run(caller);

        Assert.That(branch.OpCode, Is.EqualTo(OpCode.Jump));
        Assert.That(failCall.OpCode, Is.EqualTo(OpCode.Nop));
    }

    // When several guards share one failure block - the common real shape -
    // every one of them must fold; nopping the call must not stop later guards
    // from recognising the failure.
    [Test]
    public void SharedFailBlockFoldsEveryGuard()
    {
        var caller = Caller();
        var sysLocal = new LocalVariable("v_sys", new Register(null, "SYSREG"), _int64);
        var tls = Reg("X23", _int64, 1);
        var condA = Reg("TEMPCOND", _app.SystemTypes.SystemBooleanType, 1);
        var condB = Reg("TEMPCOND", _app.SystemTypes.SystemBooleanType, 2);

        var failCall = new Instruction(6, OpCode.Call, new StringLiteral("__stack_chk_fail"),
            Reg("X0", version: 2));
        var failReturn = new Instruction(7, OpCode.Return);
        var mergeReturn = new Instruction(5, OpCode.Return, Reg("X0", version: 3));
        var branchA = new Instruction(2, OpCode.ConditionalJump, failCall, condA);
        var branchB = new Instruction(4, OpCode.ConditionalJump, failCall, condB);

        var othersA = Reg("X8", _int64, 60);
        var othersB = Reg("X8", _int64, 61);

        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, tls, sysLocal),
            new Instruction(1, OpCode.CheckNotEqual, condA,
                new MemoryOperand(tls, null, 0x28), othersA),
            branchA,
            new Instruction(3, OpCode.CheckNotEqual, condB,
                new MemoryOperand(tls, null, 0x28), othersB),
            branchB,
            mergeReturn,
            failCall,
            failReturn,
        ]);
        caller.Locals = [sysLocal, tls, condA, condB, othersA, othersB];

        StackProtectorRecovery.Run(caller);

        Assert.That(branchA.OpCode, Is.EqualTo(OpCode.Jump), "first guard must fold");
        Assert.That(branchB.OpCode, Is.EqualTo(OpCode.Jump), "second guard must fold");
        Assert.That(failCall.OpCode, Is.EqualTo(OpCode.Nop));
        Assert.That(caller.ControlFlowGraph!.Blocks.Any(b => b.Instructions.Contains(failCall)),
            Is.False);
    }

    // The dominant real shape: the prologue stores the canary into a frame
    // slot (`Move [frame-8], [SYSREG+0x28]`) and the epilogue compares the
    // fresh TLS read against that slot.
    [Test]
    public void StoredCanaryFrameSlotFolds()
    {
        var caller = Caller();
        var sysLocal = new LocalVariable("v_sys", new Register(null, "SYSREG"), _int64);
        var tls = Reg("X23", _int64, 1);
        var frame = Reg("X29", _int64, 1);
        var cond = Reg("TEMPCOND", _app.SystemTypes.SystemBooleanType, 20);

        var failCall = new Instruction(5, OpCode.Call, new StringLiteral("__stack_chk_fail"),
            Reg("X0", version: 2));
        var failReturn = new Instruction(6, OpCode.Return);
        var mergeReturn = new Instruction(4, OpCode.Return, Reg("X0", version: 3));
        var branch = new Instruction(3, OpCode.ConditionalJump, failCall, cond);

        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, tls, sysLocal),
            new Instruction(1, OpCode.Move, new MemoryOperand(frame, null, -8),
                new MemoryOperand(tls, null, 0x28)),
            new Instruction(2, OpCode.CheckNotEqual, cond,
                new MemoryOperand(tls, null, 0x28), new MemoryOperand(frame, null, -8)),
            branch,
            mergeReturn,
            failCall,
            failReturn,
        ]);
        caller.Locals = [sysLocal, tls, frame, cond];

        StackProtectorRecovery.Run(caller);

        Assert.That(branch.OpCode, Is.EqualTo(OpCode.Jump));
        Assert.That(failCall.OpCode, Is.EqualTo(OpCode.Nop));
    }

    // The widest real compare shape: the fresh side reads the canary through
    // a spilled thread pointer - `[ptr + 0x28]` where `ptr` was loaded from a
    // frame cell that only ever holds SYSREG - against the stored-canary
    // frame slot. The dead edge's `__stack_chk_fail` is the co-proof, and the
    // sweep then nops the whole machinery: the compare, the reload chain, the
    // canary store, the thread-pointer store and the SYSREG move.
    [Test]
    public void SpilledTlsPointerCompareFoldsAndSweepsMachinery()
    {
        var caller = Caller();
        var sysLocal = new LocalVariable("v_sys", new Register(null, "SYSREG"), _int64);
        var tls = Reg("X23", _int64, 1);
        var ptr = Reg("X8", _int64, 59);
        var frame = Reg("X29", _int64, 1);
        var cond = Reg("TEMPCOND", _app.SystemTypes.SystemBooleanType, 20);

        var moveTls = new Instruction(0, OpCode.Move, tls, sysLocal);
        var storeCanary = new Instruction(1, OpCode.Move, new MemoryOperand(frame, null, -8),
            new MemoryOperand(tls, null, 0x28));
        var loadPtr = new Instruction(2, OpCode.Move, ptr, new MemoryOperand(frame, null, -40));
        var storePtr = new Instruction(3, OpCode.Move, new MemoryOperand(frame, null, -40), tls);
        var check = new Instruction(4, OpCode.CheckNotEqual, cond,
            new MemoryOperand(ptr, null, 0x28), new MemoryOperand(frame, null, -8));
        var failCall = new Instruction(6, OpCode.Call, new StringLiteral("__stack_chk_fail"),
            Reg("X0", version: 2));
        var branch = new Instruction(5, OpCode.ConditionalJump, failCall, cond);
        var mergeReturn = new Instruction(7, OpCode.Return, Reg("X0", version: 3));
        var failReturn = new Instruction(8, OpCode.Return);

        caller.ControlFlowGraph = new ISILControlFlowGraph([
            moveTls, storeCanary, loadPtr, storePtr, check, branch, mergeReturn, failCall,
            failReturn,
        ]);
        caller.Locals = [sysLocal, tls, ptr, frame, cond];

        StackProtectorRecovery.Run(caller);

        Assert.That(branch.OpCode, Is.EqualTo(OpCode.Jump));
        Assert.That(failCall.OpCode, Is.EqualTo(OpCode.Nop));
        foreach (var machinery in new[] { moveTls, storeCanary, loadPtr, storePtr, check })
            Assert.That(machinery.OpCode, Is.EqualTo(OpCode.Nop),
                $"protector machinery instruction {machinery.Index} must be swept");
    }

    // When the cell feeding the compare's `[x + 0x28]` side also carries real
    // data the guard still folds - the stored-canary side and the reachable
    // __stack_chk_fail prove the protector - but the unproven store is real
    // frame traffic and survives the sweep.
    [Test]
    public void UnprovenPointerCellStoreSurvivesTheSweep()
    {
        var caller = Caller();
        var sysLocal = new LocalVariable("v_sys", new Register(null, "SYSREG"), _int64);
        var tls = Reg("X23", _int64, 1);
        var ptr = Reg("X8", _int64, 59);
        var frame = Reg("X29", _int64, 1);
        var other = Reg("X10", _int64, 70);
        var cond = Reg("TEMPCOND", _app.SystemTypes.SystemBooleanType, 20);

        var moveTls = new Instruction(0, OpCode.Move, tls, sysLocal);
        var storeCanary = new Instruction(1, OpCode.Move, new MemoryOperand(frame, null, -8),
            new MemoryOperand(tls, null, 0x28));
        var loadPtr = new Instruction(2, OpCode.Move, ptr, new MemoryOperand(frame, null, -40));
        var realStore = new Instruction(3, OpCode.Move, new MemoryOperand(frame, null, -40), other);
        var check = new Instruction(4, OpCode.CheckNotEqual, cond,
            new MemoryOperand(ptr, null, 0x28), new MemoryOperand(frame, null, -8));
        var failCall = new Instruction(6, OpCode.Call, new StringLiteral("__stack_chk_fail"),
            Reg("X0", version: 2));
        var branch = new Instruction(5, OpCode.ConditionalJump, failCall, cond);
        var mergeReturn = new Instruction(7, OpCode.Return, Reg("X0", version: 3));
        var failReturn = new Instruction(8, OpCode.Return);

        caller.ControlFlowGraph = new ISILControlFlowGraph([
            moveTls, storeCanary, loadPtr, realStore, check, branch, mergeReturn, failCall,
            failReturn,
        ]);
        caller.Locals = [sysLocal, tls, ptr, frame, other, cond];

        StackProtectorRecovery.Run(caller);

        Assert.That(branch.OpCode, Is.EqualTo(OpCode.Jump));
        Assert.That(failCall.OpCode, Is.EqualTo(OpCode.Nop));
        Assert.That(check.OpCode, Is.EqualTo(OpCode.Nop));
        Assert.That(storeCanary.OpCode, Is.EqualTo(OpCode.Nop));
        Assert.That(realStore.OpCode, Is.EqualTo(OpCode.Move),
            "a store carrying real data is not protector machinery");
    }

    // A frame slot whose writes are not all canary stores is not proven: the
    // compare stays real code even beside a `__stack_chk_fail` call.
    [Test]
    public void UnprovenFrameSlotIsNotExcised()
    {
        var caller = Caller();
        var sysLocal = new LocalVariable("v_sys", new Register(null, "SYSREG"), _int64);
        var tls = Reg("X23", _int64, 1);
        var frame = Reg("X29", _int64, 1);
        var other = Reg("X9", _int64, 7);
        var cond = Reg("TEMPCOND", _app.SystemTypes.SystemBooleanType, 20);

        var failCall = new Instruction(6, OpCode.Call, new StringLiteral("__stack_chk_fail"),
            Reg("X0", version: 2));
        var failReturn = new Instruction(7, OpCode.Return);
        var mergeReturn = new Instruction(5, OpCode.Return, Reg("X0", version: 3));
        var branch = new Instruction(4, OpCode.ConditionalJump, failCall, cond);

        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, tls, sysLocal),
            new Instruction(1, OpCode.Move, new MemoryOperand(frame, null, -8),
                new MemoryOperand(tls, null, 0x28)),
            new Instruction(2, OpCode.Move, new MemoryOperand(frame, null, -8), other),
            new Instruction(3, OpCode.CheckNotEqual, cond,
                new MemoryOperand(tls, null, 0x28), new MemoryOperand(frame, null, -8)),
            branch,
            mergeReturn,
            failCall,
            failReturn,
        ]);
        caller.Locals = [sysLocal, tls, frame, other, cond];

        StackProtectorRecovery.Run(caller);

        Assert.That(branch.OpCode, Is.EqualTo(OpCode.ConditionalJump));
        Assert.That(failCall.OpCode, Is.EqualTo(OpCode.Call));
    }

    [Test]
    public void AnImmediateFailTargetIsMatchedThroughTheResolver()
    {
        var (caller, branch, failCall) = CanaryGuard("unused");
        failCall.SetOperand(0, new Immediate(0x7CD54D0));

        StackProtectorRecovery.Run(caller,
            address => address == 0x7CD54D0 ? "__stack_chk_fail" : null);

        Assert.That(branch.OpCode, Is.EqualTo(OpCode.Jump));
        Assert.That(failCall.OpCode, Is.EqualTo(OpCode.Nop));
    }

    // A non-canary compare branching to a __stack_chk_fail call: the compare is
    // real code, so the guard stays.
    [Test]
    public void NonCanaryCompareIsNotExcised()
    {
        var (caller, branch, failCall) = CanaryGuard("__stack_chk_fail", canary: false);

        StackProtectorRecovery.Run(caller);

        Assert.That(branch.OpCode, Is.EqualTo(OpCode.ConditionalJump));
        Assert.That(failCall.OpCode, Is.EqualTo(OpCode.Call));
    }

    // A canary compare whose failure block calls anything else: without the
    // __stack_chk_fail call present, nothing is excised.
    [Test]
    public void MissingFailCallIsNotExcised()
    {
        var (caller, branch, failCall) = CanaryGuard("puts");

        StackProtectorRecovery.Run(caller);

        Assert.That(branch.OpCode, Is.EqualTo(OpCode.ConditionalJump));
        Assert.That(failCall.OpCode, Is.EqualTo(OpCode.Call));
    }

    // When the failure call is already gone (excised for another guard on the
    // shared tail, or never linked) the compare may survive folded to a single
    // constant check: `CheckNotEqual x, x` is provably false, so the guard
    // reduces to its fall-through edge.
    [Test]
    public void SelfCompareCanaryFoldsToFallThroughWithoutFailCall()
    {
        var caller = Caller();
        var x9 = Reg("X9", _int64, 7);
        var tls = Reg("X23", _int64, 1);
        var cond = Reg("TEMPCOND", _app.SystemTypes.SystemBooleanType, 20);
        var realCall = new Instruction(5, OpCode.Call, new StringLiteral("puts"),
            Reg("X0", version: 2));
        var fallThroughReturn = new Instruction(4, OpCode.Return, Reg("X0", version: 3));
        var branch = new Instruction(3, OpCode.ConditionalJump, realCall, cond);

        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, x9,
                new LocalVariable("v_sys", new Register(null, "SYSREG"), _int64)),
            new Instruction(1, OpCode.Move, tls, x9),
            new Instruction(2, OpCode.CheckNotEqual, cond,
                new MemoryOperand(tls, null, 0x28), new MemoryOperand(tls, null, 0x28)),
            branch,
            fallThroughReturn,
            realCall,
            new Instruction(6, OpCode.Return),
        ]);
        caller.Locals = [tls, cond];

        StackProtectorRecovery.Run(caller);

        Assert.That(branch.OpCode, Is.EqualTo(OpCode.Jump), "a provably-false canary check folds");
        Assert.That(realCall.OpCode, Is.EqualTo(OpCode.Call), "the real call on the dead edge stays");
    }

    // `CheckEqual x, x` is provably true: the taken edge is the live one.
    [Test]
    public void SelfCompareCanaryEqualFoldsToTakenEdge()
    {
        var caller = Caller();
        var sysLocal = new LocalVariable("v_sys", new Register(null, "SYSREG"), _int64);
        var tls = Reg("X23", _int64, 1);
        var cond = Reg("TEMPCOND", _app.SystemTypes.SystemBooleanType, 20);
        var realCall = new Instruction(5, OpCode.Call, new StringLiteral("puts"),
            Reg("X0", version: 2));
        var deadReturn = new Instruction(4, OpCode.Return, Reg("X0", version: 3));
        var branch = new Instruction(3, OpCode.ConditionalJump, realCall, cond);

        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, tls, sysLocal),
            new Instruction(1, OpCode.CheckEqual, cond,
                new MemoryOperand(tls, null, 0x28), new MemoryOperand(tls, null, 0x28)),
            branch,
            deadReturn,
            realCall,
            new Instruction(6, OpCode.Return),
        ]);
        caller.Locals = [sysLocal, tls, cond];

        StackProtectorRecovery.Run(caller);

        Assert.That(branch.OpCode, Is.EqualTo(OpCode.Jump));
        Assert.That(branch.Operands[0], Is.InstanceOf<Block>()
            .And.Matches<Block>(b => b.Instructions.Contains(realCall)),
            "CheckEqual x,x is always true so the taken edge is live");
    }

    // A canary check whose two sides differ and no failure call anywhere:
    // nothing proves the guard constant or excises the failure, so it stays.
    [Test]
    public void DifferingCanarySidesWithoutFailCallStay()
    {
        var caller = Caller();
        var sysLocal = new LocalVariable("v_sys", new Register(null, "SYSREG"), _int64);
        var tls = Reg("X23", _int64, 1);
        var spilled = Reg("X8", _int64, 38);
        var cond = Reg("TEMPCOND", _app.SystemTypes.SystemBooleanType, 20);
        var realCall = new Instruction(5, OpCode.Call, new StringLiteral("puts"),
            Reg("X0", version: 2));
        var fallThroughReturn = new Instruction(4, OpCode.Return, Reg("X0", version: 3));
        var branch = new Instruction(3, OpCode.ConditionalJump, realCall, cond);

        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, tls, sysLocal),
            new Instruction(1, OpCode.Move, spilled, tls),
            new Instruction(2, OpCode.CheckNotEqual, cond,
                new MemoryOperand(spilled, null, 0x28), new MemoryOperand(tls, null, 0x28)),
            branch,
            fallThroughReturn,
            realCall,
            new Instruction(6, OpCode.Return),
        ]);
        caller.Locals = [sysLocal, tls, spilled, cond];

        StackProtectorRecovery.Run(caller);

        Assert.That(branch.OpCode, Is.EqualTo(OpCode.ConditionalJump));
    }

    // The large-frame shape: the compare reads the canary's frame slot through
    // a pointer materialized as `Move ptr, &stackslot`, and no store to that
    // cell was lifted. The proven [SYSREG+0x28] side and the reachable
    // __stack_chk_fail still prove the protector, so the guard folds.
    [Test]
    public void AddressOfFrameCellCompareFolds()
    {
        var caller = Caller();
        var sysLocal = new LocalVariable("v_sys", new Register(null, "SYSREG"), _int64);
        var tls = Reg("X23", _int64, 1);
        var frameSlot = new LocalVariable("v48", new Register(null, "stack_-80A0"), _int64);
        var ptr = Reg("X9", _int64, 147);
        var cond = Reg("TEMPCOND", _app.SystemTypes.SystemBooleanType, 20);

        var failCall = new Instruction(5, OpCode.Call, new StringLiteral("__stack_chk_fail"),
            Reg("X0", version: 2));
        var failReturn = new Instruction(6, OpCode.Return);
        var mergeReturn = new Instruction(4, OpCode.Return, Reg("X0", version: 3));
        var branch = new Instruction(3, OpCode.ConditionalJump, failCall, cond);

        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, tls, sysLocal),
            new Instruction(1, OpCode.Move, ptr, new AddressOf(frameSlot)),
            new Instruction(2, OpCode.CheckNotEqual, cond,
                new MemoryOperand(tls, null, 0x28), new MemoryOperand(ptr, null, 0x7FF8)),
            branch,
            mergeReturn,
            failCall,
            failReturn,
        ]);
        caller.Locals = [sysLocal, tls, frameSlot, ptr, cond];

        StackProtectorRecovery.Run(caller);

        Assert.That(branch.OpCode, Is.EqualTo(OpCode.Jump));
        Assert.That(failCall.OpCode, Is.EqualTo(OpCode.Nop));
    }

    // The same frame-cell compare with no failure call anywhere: without the
    // co-proof the frame slot is not proven the canary and the guard stays.
    [Test]
    public void AddressOfFrameCellWithoutFailCallStays()
    {
        var caller = Caller();
        var sysLocal = new LocalVariable("v_sys", new Register(null, "SYSREG"), _int64);
        var tls = Reg("X23", _int64, 1);
        var frameSlot = new LocalVariable("v48", new Register(null, "stack_-80A0"), _int64);
        var ptr = Reg("X9", _int64, 147);
        var cond = Reg("TEMPCOND", _app.SystemTypes.SystemBooleanType, 20);

        var realCall = new Instruction(5, OpCode.Call, new StringLiteral("puts"),
            Reg("X0", version: 2));
        var mergeReturn = new Instruction(4, OpCode.Return, Reg("X0", version: 3));
        var branch = new Instruction(3, OpCode.ConditionalJump, realCall, cond);

        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, tls, sysLocal),
            new Instruction(1, OpCode.Move, ptr, new AddressOf(frameSlot)),
            new Instruction(2, OpCode.CheckNotEqual, cond,
                new MemoryOperand(tls, null, 0x28), new MemoryOperand(ptr, null, 0x7FF8)),
            branch,
            mergeReturn,
            realCall,
            new Instruction(6, OpCode.Return),
        ]);
        caller.Locals = [sysLocal, tls, frameSlot, ptr, cond];

        StackProtectorRecovery.Run(caller);

        Assert.That(branch.OpCode, Is.EqualTo(OpCode.ConditionalJump));
    }

    // A canary-looking compare whose +0x28 bases are not TLS-provenanced is not
    // the stack-guard read: the guard stays.
    [Test]
    public void NonTlsCompareIsNotExcised()
    {
        var (caller, branch, failCall) = CanaryGuard("__stack_chk_fail");
        var other = Reg("X10", _int64, 70);
        caller.Locals!.Add(other);
        var check = caller.ControlFlowGraph!.Blocks
            .SelectMany(b => b.Instructions)
            .First(i => i.OpCode == OpCode.CheckNotEqual);
        check.SetOperand(1, new MemoryOperand(other, null, 0x28));
        check.SetOperand(2, new MemoryOperand(other, null, 0x28));

        StackProtectorRecovery.Run(caller);

        Assert.That(branch.OpCode, Is.EqualTo(OpCode.ConditionalJump));
        Assert.That(failCall.OpCode, Is.EqualTo(OpCode.Call));
    }
}
