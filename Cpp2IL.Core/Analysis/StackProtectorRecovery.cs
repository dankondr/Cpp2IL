using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Excises the ARM64 stack protector. The compiler reads the TLS stack-guard
/// slot - `mrs xN, tpidr_el0` (lifted as `Move xN, SYSREG`) then
/// `[xN + 0x28]` - stores the canary in the prologue, and in the epilogue
/// compares the stored canary against a fresh `[SYSREG + 0x28]` load, branching
/// to `__stack_chk_fail` on mismatch. None of it has program meaning.
///
/// A guard is folded only when all three elements are present: a canary check
/// (`CheckEqual`/`CheckNotEqual` where one side provably is the canary - the
/// TLS cell `[SYSREG + 0x28]`, a local or cell every def of which carries it -
/// and both sides are shapes it can take), the conditional branch it feeds,
/// and a `__stack_chk_fail` call - a call whose target names that import,
/// either lifted with a "name" literal or resolved through its
/// PLT/GOT-veneer relocation. When any element is missing nothing is touched
/// and the call keeps its diagnostic - unless the compare's two sides are the
/// same operand, in which case the check is a constant and the guard folds to
/// its live edge on that proof alone (the failure call has already gone for
/// these).
///
/// Folding replaces the guard's `ConditionalJump` with a `Jump` to the other
/// successor and nops the `__stack_chk_fail` call. Blocks made unreachable by
/// the fold are removed; the now-dead compare, SYSREG moves and spilled-TLS
/// reloads die in the DeadCodeEliminator that runs immediately after this pass.
/// </summary>
public static class StackProtectorRecovery
{
    private const long TlsStackGuardOffset = 0x28;

    public static void Run(MethodAnalysisContext method) => Run(method, null);

    internal static void Run(MethodAnalysisContext method, Func<ulong, string?>? importNameResolver)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet)
            return;

        var binary = method.AppContext.Binary;
        string? ResolveName(ulong address) => importNameResolver != null
            ? importNameResolver(address)
            : BlockMemoryImportRecovery.ResolveImportName(binary, address);

        var cfg = method.ControlFlowGraph!;
        var orphaned = new Queue<Block>();
        var failCalls = new List<Instruction>();

        foreach (var block in cfg.Blocks.ToList())
            TryExciseGuard(cfg, block, ResolveName, orphaned, failCalls);

        RemoveOrphanedBlocks(cfg, orphaned);

        // Nop'd only after every guard folded: several canary guards commonly
        // share one failure block, and a nopped call would stop matching
        // IsStackCheckFailCall for the guards still to visit.
        foreach (var call in failCalls)
        {
            call.OpCode = OpCode.Nop;
            call.SetOperands();
        }

        SweepDeadCanary(cfg);
    }

    // Once the guards fold, the protector's machinery is dead: the compare, the
    // reloads feeding it, the prologue stores to the canary cell and the cell
    // holding the spilled thread pointer. Left in place they emit unmanaged
    // TLS reads and undefined-SYSREG diagnostics for values that have no
    // program meaning, so they are nopped here: a pure def (Move/Not/compare)
    // whose result no instruction reads, and a store to a cell proven to hold
    // only protector values once nothing reads it back. Stores to cells that
    // carry real data are never touched.
    private static void SweepDeadCanary(ISILControlFlowGraph cfg)
    {
        // Cells are proven before the sweep: the proofs read the stores, and a
        // nopped store must not flip a cell's proof mid-fixpoint.
        var deadCells = new HashSet<MemoryOperand>();
        foreach (var instruction in cfg.Instructions)
        {
            if (instruction.OpCode == OpCode.Move
                && instruction.Operands.Count > 1
                && instruction.Operands[0] is MemoryOperand cell
                && (IsStoredCanaryCell(cell, cfg) || IsTlsPointerCell(cell, cfg)))
                deadCells.Add(cell);
        }

        var deadLocals = new HashSet<LocalVariable>();
        for (var round = 0; round < 16; round++)
        {
            var usedLocals = new HashSet<LocalVariable>();
            var readCells = new HashSet<MemoryOperand>();
            var instructions = cfg.Instructions;
            foreach (var instruction in instructions)
            {
                if (instruction.OpCode == OpCode.Nop)
                    continue;
                foreach (var source in instruction.Sources)
                    CollectSourceUse(source, usedLocals, readCells);
                if (instruction.Destination is MemoryOperand destinationCell)
                    CollectLocalUse(destinationCell, usedLocals);
            }

            var changed = false;
            foreach (var instruction in instructions)
            {
                if (instruction.OpCode is not (OpCode.Move or OpCode.CheckEqual
                        or OpCode.CheckNotEqual or OpCode.Not)
                    || instruction.Destination is not { } destination
                    || !TouchesProtector(instruction, deadCells, deadLocals, cfg))
                    continue;
                var dead = destination switch
                {
                    LocalVariable local => !usedLocals.Contains(local),
                    MemoryOperand cell => deadCells.Contains(cell) && !readCells.Contains(cell),
                    _ => false,
                };
                if (!dead)
                    continue;
                if (destination is LocalVariable deadLocal)
                    deadLocals.Add(deadLocal);
                instruction.OpCode = OpCode.Nop;
                instruction.SetOperands();
                changed = true;
            }
            if (!changed)
                return;
        }
    }

    // Only instructions on the protector's def-chain may be swept: an operand
    // naming a proven protector cell, a TLS canary read, a SYSREG root, or a
    // local already swept. Anything else - a dead load of real data, a store
    // to a mixed-use cell - keeps its instructions and its diagnostics.
    private static bool TouchesProtector(Instruction instruction, HashSet<MemoryOperand> deadCells,
        HashSet<LocalVariable> deadLocals, ISILControlFlowGraph cfg)
    {
        foreach (var operand in instruction.Operands)
        {
            switch (operand)
            {
                case MemoryOperand { Index: null, Addend: TlsStackGuardOffset,
                        Base: LocalVariable canaryBase }
                    when deadLocals.Contains(canaryBase) || IsSysregProvenanced(canaryBase, cfg):
                case MemoryOperand cell when deadCells.Contains(cell):
                case Register { Name: "SYSREG" }:
                    return true;
                case MemoryOperand mem
                    when (mem.Base is LocalVariable b && deadLocals.Contains(b))
                        || (mem.Index is LocalVariable i && deadLocals.Contains(i)):
                    return true;
                case LocalVariable local
                    when deadLocals.Contains(local) || IsSysregProvenanced(local, cfg):
                    return true;
            }
        }
        return false;
    }

    private static void CollectSourceUse(IOperand operand, HashSet<LocalVariable> locals,
        HashSet<MemoryOperand> cells)
    {
        if (operand is MemoryOperand cell)
            cells.Add(cell);
        CollectLocalUse(operand, locals);
    }

    private static void CollectLocalUse(IOperand operand, HashSet<LocalVariable> locals)
    {
        switch (operand)
        {
            case LocalVariable local:
                locals.Add(local);
                break;
            case MemoryOperand { Base: LocalVariable baseLocal }:
                locals.Add(baseLocal);
                break;
        }
        if (operand is MemoryOperand { Index: LocalVariable indexLocal })
            locals.Add(indexLocal);
    }

    // A TwoWay block whose branch condition is the canary check and one of whose
    // successors leads to __stack_chk_fail is the protector's epilogue guard:
    // fold it to the other successor. Any other shape is left alone.
    private static void TryExciseGuard(ISILControlFlowGraph cfg, Block guard,
        Func<ulong, string?> resolve, Queue<Block> orphaned, List<Instruction> failCalls)
    {
        if (guard.Successors.Count != 2 || guard.Instructions.Count == 0)
            return;
        var branch = guard.Instructions[^1];
        if (branch.OpCode != OpCode.ConditionalJump
            || branch.Operands.Count < 2
            || branch.Operands[1] is not LocalVariable condition
            || !IsCanaryCondition(condition, cfg))
            return;

        foreach (var successor in guard.Successors.ToList())
        {
            if (CollectFailCalls(successor, resolve) is not { } calls)
                continue;
            var merge = guard.Successors[0] == successor
                ? guard.Successors[1]
                : guard.Successors[0];
            if (merge == successor || CollectFailCalls(merge, resolve) != null)
                return; // both edges reach the failure - not a canary guard

            branch.OpCode = OpCode.Jump;
            branch.SetOperands(merge);
            guard.CalculateBlockType();

            RemoveEdge(cfg, guard, successor, orphaned);
            failCalls.AddRange(calls);
            return;
        }

        // The failure may already be gone - excised for another guard sharing
        // this tail, or never linked - while the compare survived. When the
        // compare's two sides are the same operand its value is constant, so
        // the guard reduces to its one live edge and dies with it. The dead
        // edge's failure call is collected and nopped the same way: when the
        // block it shares with real code (the exception-scaffold tail) stays
        // reachable, the other instructions keep their own diagnostics.
        if (!IsConstantCanaryCondition(condition, cfg, out var constant))
            return;
        var live = guard.Successors[constant ? 1 : 0];
        var dead = guard.Successors[constant ? 0 : 1];
        branch.OpCode = OpCode.Jump;
        branch.SetOperands(live);
        guard.CalculateBlockType();
        RemoveEdge(cfg, guard, dead, orphaned);
        if (CollectFailCalls(dead, resolve) is { } deadCalls)
            failCalls.AddRange(deadCalls);
    }

    // Walks empty connector blocks (all-Nop, or a single Jump) until a block
    // holding a resolved __stack_chk_fail call. Returns that call, or null when
    // the path carries real content or never reaches the failure. Any other
    // instructions alongside the call stay put - they belong to other
    // mechanisms (the exception-scaffold tail) and keep their own diagnostics.
    private static List<Instruction>? CollectFailCalls(Block start, Func<ulong, string?> resolve)
    {
        var visited = new HashSet<Block>();
        var queue = new Queue<Block>();
        queue.Enqueue(start);
        while (queue.Count > 0)
        {
            var block = queue.Dequeue();
            if (!visited.Add(block))
                continue;
            if (visited.Count > 64)
                return null;

            var calls = block.Instructions
                .Where(instruction => IsStackCheckFailCall(instruction, resolve))
                .ToList();
            if (calls.Count > 0)
                return calls;

            var meaningful = block.Instructions
                .Where(instruction => instruction.OpCode != OpCode.Nop).ToList();
            if (meaningful.Count == 0
                || (meaningful.Count == 1 && meaningful[0].OpCode == OpCode.Jump))
            {
                foreach (var successor in block.Successors)
                    queue.Enqueue(successor);
            }
            else
                return null;
        }
        return null;
    }

    private static bool IsStackCheckFailCall(Instruction instruction, Func<ulong, string?> resolve) =>
        instruction.IsCall && instruction.Operands.Count > 0 && instruction.Operands[0] switch
        {
            StringLiteral { Value: "__stack_chk_fail" } => true,
            Immediate target => resolve(target.UnsignedValue) == "__stack_chk_fail",
            _ => false,
        };

    // The condition feeding the guard: every producer chain must end at a canary
    // check - a CheckEqual/CheckNotEqual comparing the TLS stack-guard cell
    // [SYSREG + 0x28] against the stored canary (a local, or the same cell read
    // through a spilled TLS base). Anything else means the branch is real code.
    private static bool IsCanaryCondition(LocalVariable condition, ISILControlFlowGraph cfg)
    {
        var visited = new HashSet<LocalVariable>();
        var stack = new Stack<LocalVariable>();
        stack.Push(condition);
        var sawCheck = false;
        while (stack.Count > 0)
        {
            var local = stack.Pop();
            if (!visited.Add(local))
                continue;
            var sawDef = false;
            foreach (var def in cfg.Instructions
                         .Where(i => ReferenceEquals(i.Destination, local)))
            {
                sawDef = true;
                switch (def.OpCode)
                {
                    case OpCode.Move or OpCode.Not:
                        if (def.Sources.Count != 1 || def.Sources[0] is not LocalVariable source)
                            return false;
                        stack.Push(source);
                        break;
                    case OpCode.CheckEqual or OpCode.CheckNotEqual:
                        if (!IsCanaryCheck(def, cfg))
                            return false;
                        sawCheck = true;
                        break;
                    default:
                        return false;
                }
            }
            if (!sawDef)
                return false;
        }
        return sawCheck;
    }

    // The same walk as IsCanaryCondition, but also proves the condition's truth
    // value: a canary check comparing an operand against itself is constant
    // (`CheckNotEqual x, x` is always false, `CheckEqual x, x` always true),
    // with each `Not` hop flipping it. Returns false when any terminal check
    // compares differing operands or the paths disagree on the value - the
    // guard may then still be excised only via a reachable failure call.
    private static bool IsConstantCanaryCondition(LocalVariable condition, ISILControlFlowGraph cfg,
        out bool constant)
    {
        var visited = new HashSet<(LocalVariable, int)>();
        var stack = new Stack<(LocalVariable local, int parity)>();
        stack.Push((condition, 0));
        var value = -1;
        while (stack.Count > 0)
        {
            var (local, parity) = stack.Pop();
            if (!visited.Add((local, parity)))
                continue;
            var sawDef = false;
            foreach (var def in cfg.Instructions
                         .Where(i => ReferenceEquals(i.Destination, local)))
            {
                sawDef = true;
                switch (def.OpCode)
                {
                    case OpCode.Move:
                        if (def.Sources.Count != 1 || def.Sources[0] is not LocalVariable source)
                        {
                            constant = false;
                            return false;
                        }
                        stack.Push((source, parity));
                        break;
                    case OpCode.Not:
                        if (def.Sources.Count != 1 || def.Sources[0] is not LocalVariable negated)
                        {
                            constant = false;
                            return false;
                        }
                        stack.Push((negated, parity ^ 1));
                        break;
                    case OpCode.CheckEqual or OpCode.CheckNotEqual:
                        if (!IsCanaryCheck(def, cfg)
                            || def.Operands.Count < 3
                            || !def.Operands[1].Equals(def.Operands[2]))
                        {
                            constant = false;
                            return false;
                        }
                        var check = (def.OpCode == OpCode.CheckNotEqual) != (parity == 1) ? 0 : 1;
                        if (value == -1)
                            value = check;
                        else if (value != check)
                        {
                            constant = false;
                            return false;
                        }
                        break;
                    default:
                        constant = false;
                        return false;
                }
            }
            if (!sawDef)
            {
                constant = false;
                return false;
            }
        }
        if (value == -1)
        {
            constant = false;
            return false;
        }
        constant = value == 1;
        return true;
    }

    private static bool IsCanaryCheck(Instruction check, ISILControlFlowGraph cfg)
    {
        if (check.Operands.Count < 3)
            return false;
        var left = check.Operands[1];
        var right = check.Operands[2];
        return (IsCanaryProven(left, cfg) || IsCanaryProven(right, cfg))
            && IsCanaryOperand(left, cfg)
            && IsCanaryOperand(right, cfg);
    }

    // A side provably part of the protector: the fresh TLS read, a local whose
    // every def carries it, or a cell whose every store writes it. When one
    // side proves the canary and the other is a shape it could take, the
    // compare feeding a reachable __stack_chk_fail is the protector - nothing
    // else ever calls it.
    private static bool IsCanaryProven(IOperand operand, ISILControlFlowGraph cfg) =>
        operand switch
        {
            LocalVariable local => IsCanaryValue(local, cfg),
            MemoryOperand mem => IsTlsCanaryRead(mem, cfg) || IsStoredCanaryCell(mem, cfg),
            _ => false,
        };

    // One side of a canary check: the fresh TLS read, a plain local (the fail
    // call's presence is what proves it the stored canary), a `+0x28` read
    // through any (possibly spilled) TLS base, a memory cell proven to hold
    // the stored canary - the frame slot the prologue wrote with
    // `Move [frame+off], [SYSREG+0x28]` - or a frame cell read through a
    // materialized address-of pointer whose store the lift did not emit.
    private static bool IsCanaryOperand(IOperand operand, ISILControlFlowGraph cfg) =>
        operand switch
        {
            LocalVariable => true,
            MemoryOperand { Index: null, Addend: TlsStackGuardOffset } => true,
            MemoryOperand mem => IsStoredCanaryCell(mem, cfg) || IsFrameCanaryCell(mem, cfg),
            _ => false,
        };

    // A `[ptr + off]` load through a pointer materialized as `Move ptr,
    // &stackslot` - or directly through `&stackslot` - reads a frame cell even
    // when the canary store itself is absent: large frames re-materialize the
    // frame base per use and the lifter may not have emitted the prologue
    // store. The compiler only ever compares the TLS canary against its own
    // stored copy, so next to a proven canary side the frame cell is that copy.
    private static bool IsFrameCanaryCell(MemoryOperand cell, ISILControlFlowGraph cfg)
    {
        if (cell.Index != null)
            return false;
        if (cell.Base is AddressOf addressOf)
            return IsStackSlot(addressOf.Target);
        if (cell.Base is not LocalVariable pointer)
            return false;
        var saw = false;
        foreach (var def in cfg.Instructions.Where(i => ReferenceEquals(i.Destination, pointer)))
        {
            if (def.OpCode != OpCode.Move || def.Operands.Count < 2
                || def.Operands[1] is not AddressOf source
                || !IsStackSlot(source.Target))
                return false;
            saw = true;
        }
        return saw;
    }

    private static bool IsStackSlot(IOperand operand) =>
        operand is LocalVariable { Register.Name: { } name } && name.StartsWith("stack_");

    // A memory cell is the stored canary when every write to it carries the
    // TLS canary value - the prologue's `Move [cell], [SYSREG+0x28]`, possibly
    // through a spilled local whose own defs all read the same cell.
    private static bool IsStoredCanaryCell(MemoryOperand cell, ISILControlFlowGraph cfg)
    {
        if (cell.Index != null)
            return false;
        var saw = false;
        foreach (var def in cfg.Instructions.Where(i => i.OpCode == OpCode.Move
                     && i.Operands.Count > 1
                     && i.Operands[0] is MemoryOperand dest
                     && dest.Equals(cell)))
        {
            if (!IsCanaryValue(def.Operands[1], cfg))
                return false;
            saw = true;
        }
        return saw;
    }

    // A cell holding the spilled thread pointer: every write carries a
    // SYSREG-provenanced value - the `mrs xN, tpidr_el0` result, possibly
    // through spilled locals - so reads `[cell] + 0x28` are TLS canary reads
    // one level removed.
    private static bool IsTlsPointerCell(MemoryOperand cell, ISILControlFlowGraph cfg)
    {
        if (cell.Index != null)
            return false;
        var saw = false;
        foreach (var def in cfg.Instructions.Where(i => i.OpCode == OpCode.Move
                     && i.Operands.Count > 1
                     && i.Operands[0] is MemoryOperand dest
                     && dest.Equals(cell)))
        {
            var proven = def.Operands[1] switch
            {
                Register { Name: "SYSREG" } => true,
                LocalVariable source => IsSysregProvenanced(source, cfg),
                _ => false,
            };
            if (!proven)
                return false;
            saw = true;
        }
        return saw;
    }

    private static bool IsCanaryValue(IOperand operand, ISILControlFlowGraph cfg)
    {
        if (IsTlsCanaryRead(operand, cfg))
            return true;
        if (operand is not LocalVariable local)
            return false;
        var saw = false;
        foreach (var def in cfg.Instructions.Where(i => ReferenceEquals(i.Destination, local)))
        {
            if (def.OpCode != OpCode.Move || def.Operands.Count < 2
                || !IsTlsCanaryRead(def.Operands[1], cfg))
                return false;
            saw = true;
        }
        return saw;
    }

    // [base + 0x28] where base's producers root at SYSREG - the thread-pointer
    // register (`mrs xN, tpidr_el0`) whose +0x28 slot holds the stack guard.
    private static bool IsTlsCanaryRead(IOperand operand, ISILControlFlowGraph cfg) =>
        operand is MemoryOperand
            { Index: null, Addend: TlsStackGuardOffset, Base: LocalVariable baseLocal }
        && IsSysregProvenanced(baseLocal, cfg);

    // True when some producer chain roots the local at the TLS base register.
    // A coalesced local may carry other provenance on paths that cannot reach
    // the check; any chain suffices as evidence the TLS cell is the one read.
    private static bool IsSysregProvenanced(LocalVariable local, ISILControlFlowGraph cfg)
    {
        var visited = new HashSet<LocalVariable>();
        var stack = new Stack<LocalVariable>();
        stack.Push(local);
        while (stack.Count > 0)
        {
            var current = stack.Pop();
            if (!visited.Add(current))
                continue;
            if (current.Register.Name == "SYSREG")
                return true;
            foreach (var def in cfg.Instructions
                         .Where(i => ReferenceEquals(i.Destination, current)))
            {
                if (def.OpCode != OpCode.Move)
                    continue;
                foreach (var source in def.Sources)
                {
                    if (source is Register { Name: "SYSREG" })
                        return true;
                    if (source is LocalVariable sourceLocal)
                        stack.Push(sourceLocal);
                }
            }
        }
        return false;
    }

    // Removes `from` -> `to`, dropping `from`'s phi operands on `to` (phi operand
    // i+1 pairs with predecessor i) and queueing `to` for orphan cleanup.
    private static void RemoveEdge(ISILControlFlowGraph cfg, Block from, Block to, Queue<Block> orphaned)
    {
        var index = to.Predecessors.IndexOf(from);
        if (index >= 0)
        {
            foreach (var instruction in to.Instructions)
                if (instruction.OpCode == OpCode.Phi && 1 + index < instruction.Operands.Count)
                    instruction.RemoveOperandAt(1 + index);
            to.Predecessors.RemoveAt(index);
        }
        from.Successors.Remove(to);
        orphaned.Enqueue(to);
    }

    // Deletes blocks that lost every predecessor through folding, cascading
    // through their successors the same way.
    private static void RemoveOrphanedBlocks(ISILControlFlowGraph cfg, Queue<Block> seeds)
    {
        while (seeds.Count > 0)
        {
            var block = seeds.Dequeue();
            if (block == cfg.EntryBlock || !cfg.Blocks.Contains(block) || block.Predecessors.Count > 0)
                continue;
            foreach (var successor in block.Successors.ToList())
                RemoveEdge(cfg, block, successor, seeds);
            block.Successors.Clear();
            cfg.Blocks.Remove(block);
        }
    }
}
