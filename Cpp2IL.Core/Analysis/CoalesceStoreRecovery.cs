using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Canonicalizes the compiled `x ?? (x = value)` cache-store shape. The lifter
/// renders it as a flag-checked conditional whose guarded block stores a fresh
/// value into the tested slot, and phi-removal copies the merged result of the
/// two paths into a shared local on each edge:
///
///     flag = (slot == 0)
///     flag2 = !flag
///     merged = slot          // skip-path copy
///     if (flag2) goto join
/// init:
///     ...construct t...
///     slot = t
///     merged = t             // init-path copy
/// join:
///     use(merged)
///
/// A C# compiler instead emits `merged` from a single read of `slot` after the
/// join (`dup` covers the just-stored path), which is the shape ILSpy's
/// cached-`??` transforms (e.g. CachedDelegateInitialization) match. Rewrite
/// each paired merge to one `merged = slot` at the join head: after the store,
/// `slot` holds `t`, so the read is identical on both paths.
/// </summary>
public static class CoalesceStoreRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var emptiedAny = false;
        foreach (var block in cfg.Blocks)
        {
            if (block.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump } jump
                || jump.Operands.Count < 2)
                continue;

            if (jump.Operands[0] is not Block join || jump.Operands[1] is not LocalVariable condition)
                continue;

            // Resolve the storage the branch condition null-checks.
            if (!TryGetNullCheckedStorage(block, jump, condition, out var storage, out var chain,
                    out var jumpOnNonNull))
                continue;

            // The guarded path is the other successor; it must rejoin at `join`
            // through a chain of single-entry single-exit blocks (the compiler's
            // store block plus any empty edge trampolines).
            var init = block.Successors.FirstOrDefault(successor => successor != join);
            var edge = new List<Block>();
            var current = init;
            while (current != null && current != join)
            {
                if (current == block
                    || current.Predecessors.Any(predecessor => predecessor != (edge.LastOrDefault() ?? block))
                    || current.Successors.Count != 1
                    || edge.Contains(current))
                    break;
                edge.Add(current);
                current = current.Successors[0];
            }
            if (init == null || edge.Count == 0 || current != join)
                continue;

            // The false edge can run through its own trampoline before the
            // block holding the edge copies: chase `Jump` tails past them.
            join = ResolveJoinCopiesBlock(join);

            // Every `Move slot', t` in the guarded path stores back into the slot
            // the condition checked. Trailing `Move merged, t` copies pair with
            // `Move merged, slot` copies in this block; rewrite each pair.
            var collapsedAny = false;
            foreach (var edgeBlock in edge)
            foreach (var store in edgeBlock.Instructions.Where(instruction =>
                         instruction.OpCode == OpCode.Move && instruction.Operands.Count == 2
                         && SameStorage(instruction.Operands[0], storage)).ToList())
            {
                if (store.Operands[1] is not LocalVariable storedValue)
                    continue;

                // The init-edge copy either trails the store in its own block, sits
                // in a dedicated copy trampoline later on the edge, or, when the
                // copy block was folded into the join, sits at the join head.
                var storeIndex = edgeBlock.Instructions.IndexOf(store);
                var mergeSpace = edge.SkipWhile(candidate => candidate != edgeBlock)
                    .SelectMany(candidate => candidate == edgeBlock
                        ? candidate.Instructions.Skip(storeIndex + 1)
                        : candidate.Instructions)
                    .Concat(join.Instructions.TakeWhile(instruction => instruction.Index == -1))
                    .Where(instruction => instruction.OpCode == OpCode.Move
                        && instruction.Operands.Count == 2
                        && instruction.Operands[0] is LocalVariable
                        && instruction.Operands[1] == storedValue);
                foreach (var initMerge in mergeSpace.ToList())
                {
                    if (initMerge.Operands[0] is not LocalVariable merged)
                        break;

                    var preMerge = block.Instructions.LastOrDefault(instruction =>
                        instruction != jump && instruction.OpCode == OpCode.Move
                        && instruction.Operands.Count == 2
                        && ReferenceEquals(instruction.Operands[0], merged)
                        && SameStorage(instruction.Operands[1], storage));
                    if (preMerge == null)
                        continue;
                    if (!MergeIsReducible(cfg, block, edge, merged, preMerge, initMerge)
                        || IsJumpTarget(cfg, preMerge) || IsJumpTarget(cfg, initMerge))
                        continue;

                    block.Instructions.Remove(preMerge);
                    foreach (var mergeBlock in edge.Append(join))
                    {
                        mergeBlock.Instructions.Remove(initMerge);
                        emptiedAny |= mergeBlock.Instructions.Count == 0;
                    }
                    join.Instructions.Insert(0,
                        new Instruction(-1, OpCode.Move, merged, store.Operands[0]));
                    collapsedAny = true;
                }

                TryRetargetAllocationStore(cfg, edgeBlock, store, storedValue);
                emptiedAny |= edgeBlock.Instructions.Count == 0;
            }

            // The collapse left a `brtrue storage` shape: when the flag chain was
            // `(slot != null)` feeding only this jump, retarget the condition onto
            // the slot and drop the now-dead flag stores so emission inlines the
            // slot read into the branch.
            if (collapsedAny && jumpOnNonNull && ChainIsSingleUse(cfg, jump, chain))
            {
                jump.SetOperand(1, storage);
                foreach (var instruction in chain)
                    block.Instructions.Remove(instruction);
            }
        }

        // Removing a merge copy can leave a dedicated copy-trampoline block
        // empty; retarget the jumps into it and drop it so no branch operand
        // keeps pointing at a block that holds nothing.
        if (emptiedAny)
            cfg.RemoveEmptyBlocks();
    }

    // A `Newobj v` result used only as the stored value can write the slot
    // itself: `newobj; stsfld` keeps the guarded path to the single store the
    // decompiler's cached-initialization pattern expects. The paired .ctor
    // call is still found by identity and nopped at emission, so retarget both
    // operands to the same slot.
    private static void TryRetargetAllocationStore(ISILControlFlowGraph cfg, Block edgeBlock,
        Instruction store, LocalVariable storedValue)
    {
        if (!edgeBlock.Instructions.Contains(store))
            return;

        var allocation = cfg.Instructions.SingleOrDefault(instruction =>
            instruction.OpCode == OpCode.Newobj && ReferenceEquals(instruction.Destination, storedValue));
        if (allocation == null || IsJumpTarget(cfg, allocation) || IsJumpTarget(cfg, store))
            return;

        var ctorCall = cfg.Instructions.SingleOrDefault(instruction =>
            instruction.OpCode is OpCode.Call or OpCode.CallVoid
            && instruction.Operands is [MethodAnalysisContext { Name: ".ctor" } constructor, ..]
            && constructor.DeclaringType?.FullName != "System.Object"
            && instruction.Operands.Count > CtorReceiverIndex(instruction)
            && ReferenceEquals(instruction.Operands[CtorReceiverIndex(instruction)], storedValue));
        if (ctorCall == null)
            return;
        var receiverIndex = CtorReceiverIndex(ctorCall);

        foreach (var user in cfg.Instructions)
        {
            if (user != store && user != ctorCall && user != allocation
                && user.Operands.Any(operand => OperandReferencesLocal(operand, storedValue)))
                return;
        }

        allocation.SetOperand(0, store.Operands[0]);
        ctorCall.SetOperand(receiverIndex, store.Operands[0]);
        edgeBlock.Instructions.Remove(store);
    }

    private static int CtorReceiverIndex(Instruction ctorCall) => ctorCall.OpCode == OpCode.CallVoid ? 1 : 2;

    // A join reachable only through bare `Jump` trampolines has its edge copies
    // one block deeper; follow until the block that carries real instructions.
    private static Block ResolveJoinCopiesBlock(Block join)
    {
        while (join.Instructions.LastOrDefault() is { OpCode: OpCode.Jump } trampoline
               && join.Instructions.All(instruction =>
                   instruction.Index == -1 || instruction == trampoline)
               && trampoline.Operands[0] is Block next
               && next != join)
            join = next;
        return join;
    }

    // `merged` may only be defined by the two merges being removed and may not
    // be read inside the two blocks, so the rewrite never leaves a stale or a
    // clobbered value.
    private static bool MergeIsReducible(ISILControlFlowGraph cfg, Block block, List<Block> edge,
        LocalVariable merged, Instruction preMerge, Instruction initMerge)
    {
        foreach (var instruction in cfg.Instructions)
        {
            if (ReferenceEquals(instruction.Destination, merged)
                && instruction != preMerge && instruction != initMerge)
                return false;
        }
        foreach (var instruction in block.Instructions.Concat(edge.SelectMany(edgeBlock => edgeBlock.Instructions)))
        {
            if (instruction == preMerge || instruction == initMerge)
                continue;
            if (instruction.Operands.Any(operand => OperandReferencesLocal(operand, merged)))
                return false;
        }
        return true;
    }

    private static bool IsJumpTarget(ISILControlFlowGraph cfg, Instruction instruction) =>
        cfg.Instructions.Any(other => other.OpCode is OpCode.Jump or OpCode.ConditionalJump
            or OpCode.IndirectJump && ReferenceEquals(other.Operands[0], instruction));

    private static bool OperandReferencesLocal(IOperand operand, LocalVariable local) => operand switch
    {
        LocalVariable value => ReferenceEquals(value, local),
        ReferenceCast cast => ReferenceEquals(cast.Value, local),
        MemoryOperand memory => OperandReferencesLocal(memory.Base, local)
            || OperandReferencesLocal(memory.Index, local),
        AddressOf address => OperandReferencesLocal(address.Target, local),
        FieldReference field => ReferenceEquals(field.Local, local),
        ArrayAccess access => ReferenceEquals(access.Array, local)
            || OperandReferencesLocal(access.Index, local),
        ArrayElementFieldReference elementField => ReferenceEquals(elementField.Array, local)
            || OperandReferencesLocal(elementField.Index, local),
        ArrayLength length => ReferenceEquals(length.Array, local),
        _ => false,
    };

    // The operand the branch's condition tests against zero: a `Check*Equal`
    // over a storage operand, optionally behind Not/Move flag locals defined
    // in the same block. Returns the consumed flag instructions and whether
    // the branch fires while the slot is non-null.
    private static bool TryGetNullCheckedStorage(Block block, Instruction jump,
        LocalVariable condition, out IOperand storage, out List<Instruction> chain,
        out bool jumpOnNonNull)
    {
        storage = null!;
        chain = [];
        jumpOnNonNull = false;
        var current = condition;
        var flips = 0;
        for (var depth = 0; depth < 4; depth++)
        {
            var definition = block.Instructions
                .TakeWhile(instruction => instruction != jump)
                .LastOrDefault(instruction => ReferenceEquals(instruction.Destination, current));
            if (definition == null)
                return false;

            if (definition.OpCode is OpCode.Not or OpCode.Move
                && definition.Operands.Count == 2
                && definition.Operands[1] is LocalVariable next)
            {
                if (definition.OpCode == OpCode.Not)
                    flips++;
                chain.Add(definition);
                current = next;
                continue;
            }

            if (definition.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual
                && definition.Operands.Count == 3)
            {
                if (IsZeroConstant(definition.Operands[2]))
                    storage = definition.Operands[1];
                else if (IsZeroConstant(definition.Operands[1]))
                    storage = definition.Operands[2];
                if (storage is not (FieldReference or LocalVariable))
                    return false;
                chain.Add(definition);
                jumpOnNonNull = (definition.OpCode == OpCode.CheckNotEqual) != (flips % 2 == 1);
                return true;
            }

            return false;
        }
        return false;
    }

    // Every flag local in the resolved chain must be read exactly once - by the
    // next link or by the jump - before its definition can be removed.
    private static bool ChainIsSingleUse(ISILControlFlowGraph cfg, Instruction jump, List<Instruction> chain)
    {
        foreach (var instruction in chain)
        {
            if (instruction.Destination is not LocalVariable local)
                return false;
            Instruction? reader = null;
            var uses = 0;
            foreach (var candidate in cfg.Instructions)
            {
                if (candidate != instruction
                    && candidate.Operands.Any(operand => OperandReferencesLocal(operand, local)))
                {
                    uses++;
                    reader = candidate;
                }
            }
            if (uses != 1 || (reader != jump && !chain.Contains(reader)))
                return false;
        }
        return true;
    }

    private static bool SameStorage(IOperand a, IOperand b) => (a, b) switch
    {
        (LocalVariable x, LocalVariable y) => ReferenceEquals(x, y),
        (FieldReference field, FieldReference other) => field.Field == other.Field
            && field.Offset == other.Offset
            && (field.Field.IsStatic || ReferenceEquals(field.Local, other.Local)),
        _ => false,
    };

    private static bool IsZeroConstant(IOperand operand) => operand is Immediate { Value: 0 };
}
