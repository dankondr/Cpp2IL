using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Removes the IL2CPP runtime-metadata initialization guards the compiler emits near the top of
/// (almost) every method, plus il2cpp_runtime_class_init blocks.
/// </summary>
public static class MetadataInitGuardRemover
{
    private const string InitializeRuntimeMetadata = "il2cpp_codegen_initialize_runtime_metadata";
    private const string InitializeMethod = "il2cpp_codegen_initialize_method";
    private const string ClassInitExport = "il2cpp_runtime_class_init_export";
    private const string ClassInitActual = "il2cpp_runtime_class_init_actual";
    private const string ClassInitCodegen = "il2cpp_codegen_runtime_class_init";

    // Byte holding Il2CppClass's bitfield, of which bit 0 is initialized_and_no_error.
    // TODO this is almost certainly not correct on every version... but which?
    private const long InitialisedFlagOffset64 = 0x135;
    private const long InitialisedFlagOffset32 = 0xBD;

    // Offset of MethodInfo::rgctx_data
    private const long MethodRgctxOffset64 = 0x38;
    private const long MethodRgctxOffset32 = 0x1C;

    public static void Run(MethodAnalysisContext method)
        => Run(method.ControlFlowGraph!, method.AppContext.Binary.is32Bit ? InitialisedFlagOffset32 : InitialisedFlagOffset64);

    // Rewrite any metadata init calls we didn't remove into movs.
    public static void RewriteUnguardedInits(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Call || instruction.Operands is not [StringLiteral { Value: InitializeRuntimeMetadata or InitializeMethod }, var result, var handle, ..])
                continue;

            instruction.OpCode = OpCode.Move;
            instruction.SetOperands(result, handle);
        }
    }
    
    // Removes the lazy-init guards protecting a generic method's inlined RGCTX metadata lookups.
    public static void RunRgctx(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var rgctxOffset = method.AppContext.Binary.is32Bit ? MethodRgctxOffset32 : MethodRgctxOffset64;

        var removedAny = false;

        foreach (var guard in cfg.Blocks.ToList())
            removedAny |= TryRemoveRgctxGuard(method, guard, rgctxOffset);

        if (removedAny)
            DeadCodeEliminator.Run(cfg);
    }

    private static bool TryRemoveRgctxGuard(MethodAnalysisContext method, Block guard, long rgctxOffset)
    {
        var cfg = method.ControlFlowGraph!;
        if (guard.BlockType != BlockType.TwoWay || guard.Successors.Count != 2
            || guard.Instructions.Count == 0 || guard.Instructions[^1].OpCode != OpCode.ConditionalJump)
            return false;

        if (!TryMatchRgctxGuard(method, guard, rgctxOffset, out var contextRequirement))
            return false;

        var first = guard.Successors[0];
        var second = guard.Successors[1];

        // treat region calls as init boilerplate, exactly as the class-init flag test does
        return TryExcise(cfg, guard, first, second, true, contextRequirement: contextRequirement)
            || TryExcise(cfg, guard, second, first, true, contextRequirement: contextRequirement);
    }

    // What an unresolved call inside an rgctx-init arm must receive as an argument to count as the
    // lazy initializer rather than arbitrary code: either the context local itself (the unmodelled
    // extra generic-context argument) or a MethodInfo* for the method whose rgctx table is loaded.
    private sealed class ContextArgumentRequirement(
        LocalVariable? contextLocal, MethodAnalysisContext? contextOwner, int? contextRegisterNumber = null)
    {
        public bool SatisfiedBy(ISILControlFlowGraph cfg, Instruction instruction)
        {
            var firstArg = instruction.OpCode == OpCode.CallVoid ? 1 : 2;
            return instruction.Operands.Skip(firstArg).OfType<LocalVariable>().Any(local => IsContextValue(cfg, local, 0));
        }

        // The context reaches the call through plain register copies (MOV), whose destination
        // locals carry no type of their own; follow the copy chain back to the original local,
        // and accept any version of the context register itself - SSA renames it at every copy.
        private bool IsContextValue(ISILControlFlowGraph cfg, LocalVariable local, int depth)
        {
            if (contextLocal != null && ReferenceEquals(local, contextLocal))
                return true;

            if (contextOwner != null
                && local.Type is RuntimeMethodInfoAnalysisContext { RepresentedMethod: var represented }
                && ReferenceEquals(represented, contextOwner))
                return true;

            if (local.Register.Number == contextRegisterNumber)
                return true;

            if (depth >= 4)
                return false;

            var copies = cfg.Instructions
                .Where(i => i.OpCode == OpCode.Move && ReferenceEquals(i.Destination, local))
                .Select(i => i.Operands[1])
                .ToList();
            return copies is [LocalVariable source] && IsContextValue(cfg, source, depth + 1);
        }
    }

    // Matches the guard's compare: a MethodInfo::rgctx_data slot tested against zero. The compared
    // value can appear three ways:
    //  - the raw [methodInfo + 0x38] load on a typed MethodInfo* local (or a Move of that load);
    //  - a local already rewritten by RgctxResolver into the method's rgctx table object
    //    (MethodRgctxTableTypeAnalysisContext) - the null-check is on the table itself;
    //  - the same field loaded off a second, unmodelled generic-context pointer: an untyped local
    //    bound to a parameter register beyond what the declared signature consumes.
    private static bool TryMatchRgctxGuard(MethodAnalysisContext method, Block guard, long rgctxOffset,
        out ContextArgumentRequirement? requirement)
    {
        requirement = null;

        foreach (var comparison in guard.Instructions.Where(i => i.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual))
        {
            for (var i = 1; i <= 2; i++)
            {
                var operand = comparison.Operands[i];
                if (!IsZero(comparison.Operands[3 - i]))
                    continue;

                if (IsRgctxLoad(operand, rgctxOffset))
                    return true;

                if (operand is LocalVariable { Type: MethodRgctxTableTypeAnalysisContext table }
                    && IsCurrentMethod(table.OwnerMethod, method))
                {
                    // the helper call receives the method's own MethodInfo* - the last calling-
                    // convention parameter - but SSA renames and type resets can detach the arg
                    // local from it, so bind by the parameter's register as well.
                    int? methodInfoRegister = method.ParameterOperands.LastOrDefault() is Register register ? register.Number : null;
                    requirement = new ContextArgumentRequirement(null, table.OwnerMethod, methodInfoRegister);
                    return true;
                }

                if (TryGetUntypedContextBase(operand, rgctxOffset, out var direct)
                    && IsExtraContextLocal(method, direct))
                {
                    requirement = new ContextArgumentRequirement(direct, null);
                    return true;
                }

                if (GetLoadedMemory(guard, operand) is { } loaded)
                {
                    if (IsRgctxLoad(loaded, rgctxOffset))
                        return true;

                    if (TryGetUntypedContextBase(loaded, rgctxOffset, out var indirect)
                        && IsExtraContextLocal(method, indirect))
                    {
                        requirement = new ContextArgumentRequirement(indirect, null);
                        return true;
                    }
                }
            }
        }

        return false;
    }

    // The rgctx table must belong to this method (or a method it is the generic definition of) -
    // otherwise the guard protects a different context and excising it would drop a real init.
    private static bool IsCurrentMethod(MethodAnalysisContext owner, MethodAnalysisContext method) =>
        ReferenceEquals(owner, method)
        || (owner as ConcreteGenericMethodAnalysisContext)?.BaseMethodContext == method;

    private static bool IsRgctxLoad(IOperand operand, long rgctxOffset) =>
        operand is MemoryOperand { Index: null, Scale: 0, Base: LocalVariable { Type: RuntimeMethodInfoAnalysisContext } } memory
        && memory.Addend == rgctxOffset;

    private static bool TryGetUntypedContextBase(IOperand operand, long rgctxOffset,
        [NotNullWhen(true)] out LocalVariable? local)
    {
        local = operand is MemoryOperand { Index: null, Scale: 0, Addend: var addend, Base: LocalVariable { Type: null } baseLocal }
            && addend == rgctxOffset ? baseLocal : null;
        return local != null;
    }

    // The extra generic-context argument arrives in a register beyond the operands the declared
    // signature accounts for; anything else (this, real parameters) would be a user lazily-init'd
    // field, which we must not excise.
    private static bool IsExtraContextLocal(MethodAnalysisContext method, LocalVariable local) =>
        method.ParameterOperands.Count > 0
        && method.ParameterOperands.All(operand => operand is not Register register || register.Number != local.Register.Number);

    private static bool IsZero(IOperand operand) => operand is Immediate { Value: 0 };

    public static void Run(ISILControlFlowGraph cfg, long initialisedFlagOffset)
    {
        var removedAny = false;

        // Nested metadata guards are common in constructors. Removing an inner guard can make its
        // outer guard a pure init region, so keep scanning until a pass no longer changes the CFG.
        bool removedInPass;
        do
        {
            removedInPass = false;
            foreach (var guard in cfg.Blocks.ToList())
            {
                if (!cfg.Blocks.Contains(guard))
                    continue;
                removedInPass |= TryRemoveGuard(cfg, guard, initialisedFlagOffset);
            }

            removedAny |= removedInPass;
        } while (removedInPass);

        removedAny |= FoldKnownMetadataFlags(cfg);
        removedAny |= RemoveBareClassInitCalls(cfg);

        if (removedAny)
            DeadCodeEliminator.Run(cfg);
    }

    private static bool FoldKnownMetadataFlags(ISILControlFlowGraph cfg)
    {
        if (!cfg.Instructions.Any(instruction => instruction.IsCall
                && instruction.Operands is [StringLiteral { Value: InitializeRuntimeMetadata or InitializeMethod }, ..]))
            return false;

        var comparedAddresses = cfg.Instructions
            .Where(instruction => instruction.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual)
            .SelectMany(instruction => new[]
            {
                IsZero(instruction.Operands[2]) ? GetLoadedMemory(cfg, instruction.Operands[1]) : null,
                IsZero(instruction.Operands[1]) ? GetLoadedMemory(cfg, instruction.Operands[2]) : null,
            })
            .Where(memory => memory is { IsConstant: true })
            .Select(memory => ConstantMemoryAddress(cfg, memory!.Value))
            .OfType<long>()
            .ToHashSet();
        var flags = cfg.Instructions
            .Where(instruction => instruction.OpCode == OpCode.Move
                && instruction.Operands is [MemoryOperand destination, var value]
                && IsKnownOne(cfg, value))
            .Select(instruction => ConstantMemoryAddress(cfg, (MemoryOperand)instruction.Operands[0]))
            .OfType<long>()
            .Where(comparedAddresses.Contains)
            .ToHashSet();
        if (flags.Count == 0)
            return false;

        var changed = false;
        foreach (var instruction in cfg.Instructions)
        {
            if (instruction.OpCode == OpCode.Move
                && instruction.Operands is [MemoryOperand destination, var value]
                && ConstantMemoryAddress(cfg, destination) is { } storedAddress
                && flags.Contains(storedAddress) && IsKnownOne(cfg, value))
            {
                instruction.OpCode = OpCode.Nop;
                instruction.SetOperands();
                changed = true;
                continue;
            }

            for (var i = 1; i < instruction.Operands.Count; i++)
                if (instruction.Operands[i] is MemoryOperand memory
                    && ConstantMemoryAddress(cfg, memory) is { } loadedAddress
                    && flags.Contains(loadedAddress))
                {
                    instruction.SetOperand(i, new Immediate(1));
                    changed = true;
                }
        }

        return changed;
    }

    // wasm keeps the initialized-flag check inside the class-init function, so callers make bare unguarded
    // calls with no region to excise (just drop the call)
    private static bool RemoveBareClassInitCalls(ISILControlFlowGraph cfg)
    {
        var removedAny = false;

        foreach (var block in cfg.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                if (!instruction.IsCall
                    || instruction.Operands[0] is not StringLiteral { Value: ClassInitExport or ClassInitActual or ClassInitCodegen })
                    continue;

                instruction.OpCode = OpCode.Nop;
                instruction.SetOperands();
                removedAny = true;
            }
        }

        return removedAny;
    }

    private static bool TryRemoveGuard(ISILControlFlowGraph cfg, Block guard, long initialisedFlagOffset)
    {
        if (guard.BlockType != BlockType.TwoWay || guard.Successors.Count != 2
            || guard.Instructions.Count == 0 || guard.Instructions[^1].OpCode != OpCode.ConditionalJump)
            return false;

        // see if we're checking Il2CppClass::initialized_and_no_error
        // that means this is runtime_init boilerplate and we can drop the block
        var initialisedFlagTest = guard.Instructions.Any(i =>
            IsInitialisedFlagTest(cfg, i, initialisedFlagOffset));

        // Either successor could be the init entry; the other is then the merge.
        var first = guard.Successors[0];
        var second = guard.Successors[1];
        var metadataFlag = GetComparedMemory(guard);

        return TryExcise(cfg, guard, first, second, initialisedFlagTest, metadataFlag)
            || TryExcise(cfg, guard, second, first, initialisedFlagTest, metadataFlag)
            || TryExciseThroughSibling(cfg, guard, first, second, initialisedFlagTest, metadataFlag)
            || TryExciseThroughSibling(cfg, guard, second, first, initialisedFlagTest, metadataFlag)
            || TryFoldMetadataFlag(cfg, guard, metadataFlag);
    }

    // Some value-producing guards repeat a real field assignment in both arms, so excising the init
    // arm is deliberately rejected above. In recovered managed code metadata is already materialized;
    // fold only absolute one-byte flags that this method also sets after a metadata-init call.
    private static bool TryFoldMetadataFlag(ISILControlFlowGraph cfg, Block guard, MemoryOperand? metadataFlag)
    {
        if (metadataFlag is not { IsConstant: true } flag
            || ConstantMemoryAddress(cfg, flag) is not { } flagAddress
            || !cfg.Instructions.Any(i => i.IsCall
                && i.Operands is [StringLiteral { Value: InitializeRuntimeMetadata or InitializeMethod }, ..])
            || !cfg.Instructions.Any(i => i.OpCode == OpCode.Move
                && i.Operands is [MemoryOperand destination, var value]
                && ConstantMemoryAddress(cfg, destination) == flagAddress && IsKnownOne(cfg, value)))
            return false;

        var changed = false;
        // The load feeding the guard is often in its predecessor after block splitting. Rewrite the
        // matching flag everywhere before deleting its initializing store, otherwise a later pass
        // is left with a read of unmanaged process memory and no proof that it is metadata state.
        foreach (var instruction in cfg.Instructions)
        {
            for (var i = 1; i < instruction.Operands.Count; i++)
            {
                if (instruction.Operands[i] is not MemoryOperand memory
                    || ConstantMemoryAddress(cfg, memory) != flagAddress)
                    continue;
                instruction.SetOperand(i, new Immediate(1));
                changed = true;
                }
        }

        if (!changed)
            return false;

        foreach (var store in cfg.Instructions.Where(i => i.OpCode == OpCode.Move
                     && i.Operands is [MemoryOperand destination, var value]
                     && ConstantMemoryAddress(cfg, destination) == flagAddress && IsKnownOne(cfg, value)))
        {
            store.OpCode = OpCode.Nop;
            store.SetOperands();
        }

        return changed;
    }

    private static long? ConstantMemoryAddress(ISILControlFlowGraph cfg, MemoryOperand memory)
    {
        if (memory.Index != null || memory.Scale != 0)
            return null;
        if (memory.Base == null)
            return memory.Addend;
        if (memory.Base is not LocalVariable local)
            return null;

        var definitions = cfg.Instructions.Where(instruction => ReferenceEquals(instruction.Destination, local))
            .Select(instruction => instruction.Operands is [_, Immediate immediate] ? (long?)immediate.Value : null)
            .Distinct()
            .ToArray();
        return definitions is [long baseAddress] ? baseAddress + memory.Addend : null;
    }

    private static bool IsKnownOne(ISILControlFlowGraph cfg, IOperand operand) =>
        IsOne(operand) || operand is LocalVariable local && cfg.Instructions.Any(i =>
            i.OpCode == OpCode.Move && ReferenceEquals(i.Destination, local)
                                     && i.Operands is [_, Immediate { Value: 1 }]);

    private static bool TryExciseThroughSibling(ISILControlFlowGraph cfg, Block guard, Block initEntry,
        Block retainedEntry, bool initialisedFlagTest, MemoryOperand? metadataFlag)
    {
        if (retainedEntry.Successors.Count != 1)
            return false;

        var merge = retainedEntry.Successors[0];
        if (merge == cfg.EntryBlock || merge == cfg.ExitBlock
            || !TryCollectRegion(cfg, guard, initEntry, merge, initialisedFlagTest, out var region, metadataFlag))
            return false;

        Excise(cfg, guard, initEntry, merge, region, retainedEntry);
        return true;
    }

    private static MemoryOperand? GetComparedMemory(Block guard)
    {
        foreach (var comparison in guard.Instructions.Where(i => i.OpCode is OpCode.CheckEqual or OpCode.CheckNotEqual))
        {
            for (var i = 1; i <= 2; i++)
            {
                if (!IsZero(comparison.Operands[3 - i]))
                    continue;
                if (GetLoadedMemory(guard, comparison.Operands[i]) is { } memory)
                    return memory;
            }
        }

        foreach (var mask in guard.Instructions.Where(i => i.OpCode == OpCode.And))
        {
            if (mask.Operands is [_, var value, Immediate { Value: 1 }]
                && GetLoadedMemory(guard, value) is { } memory)
                return memory;
            if (mask.Operands is [_, Immediate { Value: 1 }, var reversedValue]
                && GetLoadedMemory(guard, reversedValue) is { } reversedMemory)
                return reversedMemory;
        }

        return null;
    }

    private static MemoryOperand? GetLoadedMemory(Block guard, IOperand operand)
    {
        if (operand is MemoryOperand memory)
            return memory;
        if (operand is not LocalVariable local)
            return null;

        var load = guard.Instructions.LastOrDefault(candidate =>
            candidate.OpCode == OpCode.Move && ReferenceEquals(candidate.Destination, local));
        return load?.Operands[1] is MemoryOperand loadedMemory ? loadedMemory : null;
    }

    private static MemoryOperand? GetLoadedMemory(ISILControlFlowGraph cfg, IOperand operand)
    {
        if (operand is MemoryOperand memory)
            return memory;
        if (operand is not LocalVariable local)
            return null;

        return cfg.Instructions.LastOrDefault(candidate => candidate.OpCode == OpCode.Move
            && ReferenceEquals(candidate.Destination, local))?.Operands[1] is MemoryOperand loaded ? loaded : null;
    }

    private static bool IsOne(IOperand operand) => operand is Immediate { Value: 1 };

    internal static bool IsInitialisedFlagTest(ISILControlFlowGraph cfg, Instruction instruction,
        long initialisedFlagOffset)
    {
        if (instruction.OpCode != OpCode.And || instruction.Operands is not [_, var flag, var mask]
            || !IsOne(mask))
            return false;

        if (flag is MemoryOperand { Index: null, Scale: 0, Base: LocalVariable directAddress } direct)
            return direct.Addend == initialisedFlagOffset
                || direct.Addend == 0 && IsClassFlagAddress(cfg, directAddress, initialisedFlagOffset);

        if (flag is not LocalVariable flagLocal)
            return false;
        var load = cfg.Instructions.FirstOrDefault(candidate =>
            candidate.OpCode == OpCode.Move
            && ReferenceEquals(candidate.Destination, flagLocal)
            && candidate.Operands is [_, MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable }]);
        if (load?.Operands[1] is not MemoryOperand { Base: LocalVariable address })
            return false;

        return IsClassFlagAddress(cfg, address, initialisedFlagOffset);
    }

    private static bool IsClassFlagAddress(ISILControlFlowGraph cfg, LocalVariable address,
        long initialisedFlagOffset) =>
        cfg.Instructions.Any(candidate =>
            candidate.OpCode == OpCode.Add
            && ReferenceEquals(candidate.Destination, address)
            && candidate.Operands.Skip(1).Any(operand => operand is Immediate { Value: var value }
                && value == initialisedFlagOffset));

    private static bool TryExcise(ISILControlFlowGraph cfg, Block guard, Block initEntry, Block merge,
        bool initialisedFlagTest, MemoryOperand? metadataFlag = null, ContextArgumentRequirement? contextRequirement = null)
    {
        if (merge == cfg.EntryBlock || merge == cfg.ExitBlock)
            return false;

        if (!TryCollectRegion(cfg, guard, initEntry, merge, initialisedFlagTest, out var region, metadataFlag, contextRequirement))
            return false;

        Excise(cfg, guard, initEntry, merge, region);
        return true;
    }

    private static bool TryCollectRegion(ISILControlFlowGraph cfg, Block guard, Block initEntry, Block merge,
        bool initialisedFlagTest, out HashSet<Block> region, MemoryOperand? metadataFlag = null,
        ContextArgumentRequirement? contextRequirement = null)
    {
        region = [];

        if (initEntry == merge || initEntry == guard)
            return false;

        var sawMetadataInit = false;
        var sawClassInit = false;
        var sawFlagStore = false;
        var sawContextInit = false;
        var reconverges = false;

        var queue = new Queue<Block>();
        queue.Enqueue(initEntry);

        while (queue.Count > 0)
        {
            var block = queue.Dequeue();

            if (block == merge)
            {
                reconverges = true;
                continue;
            }

            // The region must not run into the method boundary or loop back through the guard.
            if (block == cfg.EntryBlock || block == cfg.ExitBlock || block == guard)
                return false;

            if (!region.Add(block))
                continue;

            if (!ClassifyBlock(cfg, block, initialisedFlagTest, metadataFlag, contextRequirement,
                    ref sawMetadataInit, ref sawClassInit, ref sawFlagStore, ref sawContextInit))
                return false;

            foreach (var successor in block.Successors)
                queue.Enqueue(successor);
        }

        var sawInit = contextRequirement == null
            ? sawClassInit || (sawMetadataInit && sawFlagStore)
            : sawContextInit;
        if (!reconverges || !sawInit)
            return false;

        var collected = region;
        foreach (var block in collected)
        {
            if (block.Predecessors.Any(predecessor => predecessor != guard && !collected.Contains(predecessor)))
                return false;
            if (block.Successors.Any(successor => successor != merge && !collected.Contains(successor)))
                return false;
        }

        return true;
    }

    // A region block is acceptable only if every instruction is intra-region control flow, an init
    // call, the flag store, or otherwise side-effect-free (writes a local, not memory). A managed call
    // or any other store would have an effect we cannot silently drop, so it disqualifies the region.
    private static bool ClassifyBlock(ISILControlFlowGraph cfg, Block block, bool initialisedFlagTest, MemoryOperand? metadataFlag,
        ContextArgumentRequirement? contextRequirement,
        ref bool sawMetadataInit, ref bool sawClassInit, ref bool sawFlagStore, ref bool sawContextInit)
    {
        foreach (var instruction in block.Instructions)
        {
            switch (instruction.OpCode)
            {
                case OpCode.Jump:
                    break;

                // Structurally-proven lazy-context guard: only unresolved helpers count, and every
                // one must take the context (the unmodelled extra generic-context argument, or a
                // MethodInfo* for the owning method) - the proof that each call is "init X" rather
                // than an arbitrary region call with its own effects.
                case OpCode.Call or OpCode.CallVoid when contextRequirement is { } requirement:
                    if (instruction.Operands[0] is Immediate)
                    {
                        if (!requirement.SatisfiedBy(cfg, instruction))
                            return false;
                        sawContextInit = true;
                        break;
                    }

                    // Already-identified init boilerplate nested inside the arm is still boilerplate.
                    if (instruction.Operands is [StringLiteral { Value: InitializeRuntimeMetadata or InitializeMethod }, ..])
                    {
                        sawMetadataInit = true;
                        break;
                    }
                    return false;

                // Behind an initialized_and_no_error test the callee is the class initializer, even if we didn't resolve it.
                // If we didn't, that's fine, just skip.
                case OpCode.Call or OpCode.CallVoid when initialisedFlagTest:
                    sawClassInit = true;
                    break;

                case OpCode.Call or OpCode.CallVoid:
                    if (instruction.Operands is not [StringLiteral { Value: var name }, ..])
                        return false;

                    if (name is InitializeRuntimeMetadata or InitializeMethod)
                        sawMetadataInit = true;
                    else if (name is ClassInitExport or ClassInitActual or ClassInitCodegen)
                        sawClassInit = true;
                    else
                        return false;

                    break;

                case OpCode.Move when instruction.Operands is [MemoryOperand destination, _]
                                          && metadataFlag is { } flag && destination.Equals(flag):
                    sawFlagStore = true;
                    break;

                default:
                    if (!IsSideEffectFree(instruction))
                        return false;
                    break;
            }
        }

        return true;
    }

    // True for instructions that only compute a value into a local (or do nothing). A store - any
    // instruction whose destination operand is a memory or field reference rather than a local - is
    // excluded, as is anything that transfers control or merges values (phi/return/indirect).
    private static bool IsSideEffectFree(Instruction instruction) =>
        instruction.OpCode switch
        {
            OpCode.Nop => true,
            OpCode.Move or OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Modulo
                or OpCode.ShiftLeft or OpCode.ShiftRight or OpCode.And or OpCode.Or or OpCode.Xor
                or OpCode.Not or OpCode.Negate
                or (>= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual)
                => instruction.Operands is [LocalVariable, ..],
            _ => false,
        };

    internal static void Excise(ISILControlFlowGraph cfg, Block guard, Block initEntry, Block merge,
        HashSet<Block> region, Block? retainedEntry = null)
    {
        // 1. Repair the merge's phis: drop the inputs from the region's back-edges.
        for (var i = merge.Predecessors.Count - 1; i >= 0; i--)
        {
            if (!region.Contains(merge.Predecessors[i]))
                continue;

            foreach (var phi in merge.Instructions)
                if (phi.OpCode == OpCode.Phi && 1 + i < phi.Operands.Count)
                    phi.RemoveOperandAt(1 + i);

            merge.Predecessors.RemoveAt(i);
        }

        // 2. Fold the guard so it goes straight to the merge.
        guard.Successors.Remove(initEntry);
        initEntry.Predecessors.Remove(guard);

        var terminator = guard.Instructions[^1];
        terminator.OpCode = OpCode.Jump;
        terminator.SetOperands(retainedEntry ?? merge);
        guard.CalculateBlockType();

        // 3. Delete the region. 
        foreach (var block in region)
        {
            foreach (var successor in block.Successors)
                successor.Predecessors.Remove(block);
            foreach (var predecessor in block.Predecessors)
                predecessor.Successors.Remove(block);

            block.Successors.Clear();
            block.Predecessors.Clear();
            cfg.Blocks.Remove(block);
        }
    }
}
