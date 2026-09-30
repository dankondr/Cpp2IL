using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Post-SSA copy/constant cleanup. The bulk of copy and constant propagation is done earlier, in SSA,
/// by <see cref="SsaSimplifier"/>; this pass mops up the copies that <em>destroying</em> SSA leaves
/// behind - each phi is lowered to a <c>Move</c> on every incoming edge, so the phi's result becomes a
/// single local with one definition per predecessor.
///
/// Those multiple definitions mean a value is no longer single-assignment: at the join the definitions
/// merge, and which one reaches a use is path-dependent. So unlike <see cref="SsaSimplifier"/>, this
/// pass cannot blindly forward a definition - it walks the CFG and refuses to carry a multiply-defined
/// local's value across the join its other definitions merge at (where the phi used to be).
/// </summary>
public static class Simplifier
{
    public static void Simplify(MethodAnalysisContext method)
    {
        new SimplifierContext(method).Process();
    }

    private readonly ref struct SimplifierContext(MethodAnalysisContext method)
    {
        private readonly Dictionary<Block, Dictionary<Instruction, OperandList>> _sourceCache = [];
        private readonly MethodAnalysisContext _method = method;
        private readonly ISILControlFlowGraph _graph = method.ControlFlowGraph!;

        public void Process()
        {
            PopulateSourceCache();

            InlineLocals();

            // Repeat until no change
            while (InlineConstantsSinglePass()) ;

            // More locals can now be inlined
            InlineLocals();

            _graph.RemoveNops();
            _graph.RemoveEmptyBlocks();
        }

        private void PopulateSourceCache()
        {
            #if NET5_0_OR_GREATER
            _sourceCache.EnsureCapacity(_graph.Blocks.Count);
            #endif

            foreach (var block in _graph.Blocks)
            {
                var sourceCache = new Dictionary<Instruction, OperandList>(block.Instructions.Count);
                foreach (var instruction in block.Instructions)
                {
                    sourceCache[instruction] = instruction.Sources;
                }

                _sourceCache[block] = sourceCache;
            }
        }

        private void UpdateSourceCache(Block block, Instruction instruction)
        {
            _sourceCache[block][instruction] = instruction.Operands;
        }

        private bool InlineConstantsSinglePass()
        {
            var changed = false;
            var definitionCounts = CountDefinitions();

            var visited = new HashSet<Block>();
            var queue = new Queue<Block>(_graph.Blocks.Count);

#if NET5_0_OR_GREATER
            visited.EnsureCapacity(_graph.Blocks.Count);
#endif

            queue.Enqueue(_graph.EntryBlock);
            visited.Add(_graph.EntryBlock);

            while (queue.Count > 0)
            {
                var block = queue.Dequeue();

                for (var i = 0; i < block.Instructions.Count; i++)
                {
                    var instruction = block.Instructions[i];

                    // If it's move and it moves something to local, replace and remove it
                    if (instruction.OpCode == OpCode.Move && instruction.Operands[0] is LocalVariable local)
                    {
                        // A group of field loads from one receiver before a value-returning call is a
                        // native snapshot. Forwarding the loads would turn it into post-call reloads.
                        if (instruction.Operands[1] is FieldReference field
                            && MustPreserveFieldSnapshot(block, i + 1, local, field.Local))
                            continue;
                        if (instruction.Operands[1] is SelectedFieldReference selected)
                        {
                            var preserve = false;
                            foreach (var choice in selected.Choices)
                                preserve |= MustPreserveFieldSnapshot(block, i + 1, local, choice.Field.Local);
                            if (preserve)
                                continue;
                        }

                        // A copy between locals that cannot hold each other's value - a slot
                        // merging unrelated references across paths - has no legal managed
                        // store, so the source cannot be forwarded into the destination's
                        // typed positions. The move itself stays: the emitter fills the slot
                        // with a noted synthetic default (a decompiler-issue call naming both
                        // types), so the stored value is measured rather than silently
                        // dropped. Copies between managed pointers (T& or T* on both sides)
                        // are exempt - the value is the address itself.
                        if (instruction.Operands[1] is LocalVariable incompatibleSource
                            && LocalVariables.NoLegalManagedCopy(local, incompatibleSource, allowByRefReinterpret: true))
                            continue;

                        if (IsLocalUsedAfterInstruction(block, i + 1, local, out var usedByMemory))
                        {
                            // This can't be inlined into memory operand
                            if (usedByMemory) continue;

                            // A local with several definitions is not in SSA form, so its value at a join
                            // depends on the path taken; don't carry this definition across that join.
                            var stopAtJoins = definitionCounts.TryGetValue(local, out var defs) && defs > 1;

                            // Replace local
                            ReplaceLocalsUntilReassignment(block, i + 1, local, instruction.Operands[1], stopAtJoins);

                            // Only drop the defining move once the local has no remaining uses; if the
                            // replacement stopped at a join, the local is still live past it so the move stays.
                            if (IsLocalUsedAfterInstruction(block, i + 1, local, out _))
                                continue;

                            // Change that move to nop
                            instruction.OpCode = OpCode.Nop;
                            instruction.SetOperands();
                            UpdateSourceCache(block, instruction);

                            changed = true;
                        }
                    }
                }

                foreach (var successor in block.Successors)
                {
                    if (visited.Add(successor))
                        queue.Enqueue(successor);
                }
            }

            return changed;
        }

        private bool MustPreserveFieldSnapshot(Block block, int startIndex, LocalVariable value,
            LocalVariable? receiver)
        {
            if (receiver == null)
                return false;

            for (var callIndex = startIndex; callIndex < block.Instructions.Count; callIndex++)
            {
                var instruction = block.Instructions[callIndex];
                if (instruction.Destination == value)
                    return false;

                if (instruction.OpCode != OpCode.Call)
                    continue;

                if (!IsLocalUsedAfterInstruction(block, callIndex + 1, value, out _))
                    return false;

                for (var i = 0; i < callIndex; i++)
                {
                    var candidateInstruction = block.Instructions[i];
                    if (candidateInstruction.OpCode != OpCode.Move
                        || candidateInstruction.Destination is not LocalVariable candidate
                        || candidate == value
                        || candidateInstruction.Operands[1] is not FieldReference field
                        || field.Local != receiver)
                        continue;

                    var reassigned = false;
                    for (var j = i + 1; j < callIndex; j++)
                        reassigned |= block.Instructions[j].Destination == candidate;

                    if (!reassigned && IsLocalUsedAfterInstruction(block, callIndex + 1, candidate, out _))
                        return true;
                }

                return false;
            }

            return false;
        }

        private void InlineLocals()
        {
            var definitionCounts = CountDefinitions();

            var visited = new HashSet<Block>();
            var queue = new Queue<Block>(_method.ControlFlowGraph!.Blocks.Count);

#if NET5_0_OR_GREATER
            visited.EnsureCapacity(_graph.Blocks.Count);
#endif

            queue.Enqueue(_graph.EntryBlock);
            visited.Add(_graph.EntryBlock);

            while (queue.Count > 0)
            {
                var block = queue.Dequeue();

                for (var i = 0; i < block.Instructions.Count; i++)
                {
                    var instruction = block.Instructions[i];

                    // If it's move and it moves local to local, replace and remove it
                    if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable local, LocalVariable source] })
                    {
                        // A copy between locals that cannot hold each other's value has no legal
                        // managed store, so the source is never forwarded into the destination's
                        // typed positions. The move stays for the emitter, which fills the slot
                        // with a noted synthetic default instead of dropping the store silently.
                        // Copies between managed pointers (T& or T* on both sides) are exempt -
                        // the value is the address itself.
                        if (LocalVariables.NoLegalManagedCopy(local, source, allowByRefReinterpret: true))
                            continue;

                        // A local with several definitions is not in SSA form, so its value at a join
                        // depends on the path taken; don't carry this definition across that join.
                        var stopAtJoins = definitionCounts.TryGetValue(local, out var defs) && defs > 1;

                        // Replace local with source
                        ReplaceLocalsUntilReassignment(block, i + 1, local, source, stopAtJoins);

                        // If the replacement stopped at a join merging another definition, the local is
                        // still live there - keep its defining move rather than dropping the value on this path.
                        if (IsLocalUsedAfterInstruction(block, i + 1, local, out _))
                            continue;

                        if (!_method.ParameterLocals.Contains(local))
                            _method.Locals.Remove(local);

                        // Change that move to nop
                        instruction.OpCode = OpCode.Nop;
                        instruction.SetOperands();
                        UpdateSourceCache(block, instruction);
                    }
                }

                foreach (var successor in block.Successors)
                {
                    if (visited.Add(successor))
                        queue.Enqueue(successor);
                }
            }
        }

        // Counts how many instructions define each local. A local with more than one definition is not in
        // SSA form: at a control-flow join its value depends on which predecessor was taken, so none of its
        // definitions may be propagated across that join - a phi would be needed there instead.
        private Dictionary<LocalVariable, int> CountDefinitions()
        {
            var counts = new Dictionary<LocalVariable, int>();

            foreach (var instruction in _graph.Blocks.SelectMany(block => block.Instructions))
            {
                if (instruction.Destination is LocalVariable local)
                    counts[local] = counts.TryGetValue(local, out var count) ? count + 1 : 1;
            }

            return counts;
        }

        private void ReplaceLocalsUntilReassignment(Block startBlock, int startIndex, LocalVariable local,
            IOperand replacement, bool stopAtJoins)
        {
            var visited = new HashSet<Block>();
            var remaining = new Stack<(Block, int)>(_graph.Blocks.Count);

#if NET5_0_OR_GREATER
            visited.EnsureCapacity(_graph.Blocks.Count);
#endif

            visited.Add(startBlock);
            remaining.Push((startBlock, startIndex));

            while (remaining.Count > 0)
            {
                var (currentBlock, index) = remaining.Pop();

                // Process instructions starting at the given index
                for (var i = index; i < currentBlock.Instructions.Count; i++)
                {
                    var instruction = currentBlock.Instructions[i];

                    // Stop on this branch when reassigned
                    if (instruction.Destination is LocalVariable destLocal && destLocal == local)
                        return;

                    // Replace operands
                    for (var j = 0; j < instruction.Operands.Count; j++)
                    {
                        var operand = instruction.Operands[j];

                        if (operand is LocalVariable usedLocal && usedLocal == local
                            && (replacement is not LocalVariable localReplacement
                                || !LocalVariables.CallOperandProvenMismatched(instruction, j,
                                    localReplacement, _method)))
                        {
                            instruction.SetOperand(j, replacement);
                            UpdateSourceCache(currentBlock, instruction);
                        }

                        // A memory operand's base/index holds an address, so only a local replacement may
                        // be substituted there (copy propagation). A constant/value replacement is left in
                        // place - the caller sees the local is still used and keeps its defining move.
                        else if (operand is MemoryOperand memory && replacement is LocalVariable)
                        {
                            if (memory.Base is LocalVariable baseLocal && baseLocal == local)
                                memory.Base = replacement;

                            if (memory.Index is LocalVariable indexLocal && indexLocal == local)
                                memory.Index = replacement;

                            instruction.SetOperand(j, memory);
                            UpdateSourceCache(currentBlock, instruction);
                        }

                        // The object a field is accessed on is an address just like a memory base,
                        // and its type must be able to serve as the receiver - a mismatched local
                        // would produce an invalid ldfld. The receiver slot is what the
                        // ldfld/stfld type contract reads: the replacement's emitted slot type
                        // must supply the field's declaring type (`&Vector2` cannot feed
                        // `ldfld Vector3::x`) - a value-type mismatch NoLegalManagedCopy cannot see.
                        else if (operand is FieldReference field && replacement is LocalVariable fieldReplacement &&
                                 field.Local == local && !LocalVariables.NoLegalManagedCopy(local, fieldReplacement) &&
                                 !LocalVariables.ReceiverProvenMismatched(
                                     LocalVariables.EmittedSlotLocalType(fieldReplacement, _method),
                                     LocalVariables.ReceiverHost(field)))
                        {
                            field.Local = fieldReplacement;
                        }
                        else if (operand is SelectedFieldReference selected && replacement is LocalVariable selectedReplacement)
                        {
                            if (selected.Selector == local)
                                selected.Selector = selectedReplacement;
                            foreach (var choice in selected.Choices)
                                if (choice.Field.Local == local && !LocalVariables.NoLegalManagedCopy(local, selectedReplacement)
                                    && !LocalVariables.ReceiverProvenMismatched(
                                        LocalVariables.EmittedSlotLocalType(selectedReplacement, _method),
                                        LocalVariables.ReceiverHost(choice.Field)))
                                    choice.Field.Local = selectedReplacement;
                        }


                        // An address-take's compound target (&receiver.field, &array[i].field,
                        // &mem[base+index]) reads the locals inside it like any other operand.
                        else if (operand is AddressOf address && replacement is LocalVariable addressReplacement)
                        {
                            SubstituteInAddressTarget(address, local, addressReplacement, _method);
                        }

                        // A reference cast's operand is a managed-reference slot just like a memory
                        // base: only a local replacement may be substituted there, so a constant
                        // stays put and keeps its defining move alive. The local must itself carry
                        // a managed reference - a value-typed, generic-parameter, pointer or
                        // native-handle replacement would emit an isinst/castclass on a
                        // non-reference stack kind, which ILVerify rejects.
                        else if (operand is ReferenceCast cast && cast.Value == local &&
                                 replacement is LocalVariable castReplacement &&
                                 IsManagedReferenceLocal(castReplacement))
                        {
                            instruction.SetOperand(j, new ReferenceCast(castReplacement, cast.Type, cast.NullOnFailure));
                            UpdateSourceCache(currentBlock, instruction);
                        }
                    }
                }

                // Process successors
                foreach (var successor in currentBlock.Successors)
                {
                    // A join merges this local's other definitions, so for a non-SSA (multiply-defined)
                    // local the replacement must not flow past it - the value there is path-dependent.
                    if (stopAtJoins && successor.Predecessors.Count > 1)
                        continue;

                    if (visited.Add(successor))
                        remaining.Push((successor, 0));
                }
            }
        }

        // Substitution inside an address-take's target mirrors the operand-level rules: compound
        // positions (the object or memory cell a field/element is addressed through) take a local
        // replacement exactly like their top-level counterparts. A bare local target (&v) is the
        // cell's own identity rather than a value inside it, so it is never rewritten.
        private static void SubstituteInAddressTarget(AddressOf address, LocalVariable local,
            LocalVariable replacement, MethodAnalysisContext method)
        {
            switch (address.Target)
            {
                case MemoryOperand memory:
                    if (memory.Base is LocalVariable memoryBase && memoryBase == local)
                        memory.Base = replacement;
                    if (memory.Index is LocalVariable memoryIndex && memoryIndex == local)
                        memory.Index = replacement;
                    address.Target = memory; // MemoryOperand is a struct, write the copy back
                    break;
                case FieldReference field when field.Local == local && !LocalVariables.NoLegalManagedCopy(local, replacement)
                    && !LocalVariables.ReceiverProvenMismatched(
                        LocalVariables.EmittedSlotLocalType(replacement, method),
                        LocalVariables.ReceiverHost(field)):
                    field.Local = replacement;
                    break;
                case SelectedFieldReference selected:
                    if (selected.Selector == local)
                        selected.Selector = replacement;
                    foreach (var choice in selected.Choices)
                        if (choice.Field.Local == local && !LocalVariables.NoLegalManagedCopy(local, replacement)
                            && !LocalVariables.ReceiverProvenMismatched(
                                LocalVariables.EmittedSlotLocalType(replacement, method),
                                LocalVariables.ReceiverHost(choice.Field)))
                            choice.Field.Local = replacement;
                    break;
                case ArrayAccess access:
                    if (access.Array == local)
                        access.Array = replacement;
                    if (access.Index is LocalVariable arrayIndex && arrayIndex == local)
                        access.Index = replacement;
                    break;
                case ArrayElementFieldReference elementField:
                    if (elementField.Array == local)
                        elementField.Array = replacement;
                    if (elementField.Index is LocalVariable elementIndex && elementIndex == local)
                        elementField.Index = replacement;
                    break;
                case ArrayLength length when length.Array == local:
                    length.Array = replacement;
                    break;
                case ReferenceCast cast when cast.Value == local && IsManagedReferenceLocal(replacement):
                    address.Target = new ReferenceCast(replacement, cast.Type, cast.NullOnFailure);
                    break;
                case AddressOf nested:
                    SubstituteInAddressTarget(nested, local, replacement, method);
                    break;
            }
        }

        // Whether the local's emitted type can fill an isinst/castclass operand slot, which holds a
        // managed object reference. The slot accepts exactly the signature kinds that land as object
        // references - classes, strings, object, arrays, non-value generic instances and boxed
        // values. Everything else is a non-reference stack kind there: primitives and other value
        // types load as values, IL2CPP_TYPE_VAR/MVAR load as generic-parameter values, and
        // pointer, byref, native-int, pinned, sentinel and other exotic kinds all emit signatures
        // ILVerify rejects in the operand position.
        private static bool IsManagedReferenceLocal(LocalVariable local) =>
            local.Type is { IsValueType: false } type
                && type.Type is Il2CppTypeEnum.IL2CPP_TYPE_CLASS
                    or Il2CppTypeEnum.IL2CPP_TYPE_STRING
                    or Il2CppTypeEnum.IL2CPP_TYPE_OBJECT
                    or Il2CppTypeEnum.IL2CPP_TYPE_SZARRAY
                    or Il2CppTypeEnum.IL2CPP_TYPE_ARRAY
                    or Il2CppTypeEnum.IL2CPP_TYPE_GENERICINST
                    or Il2CppTypeEnum.IL2CPP_TYPE_BOXED;

        private bool IsLocalUsedAfterInstruction(Block startBlock, int startIndex, LocalVariable local, out bool usedByMemory)
        {
            var visited = new HashSet<Block>();
            var remaining = new Stack<(Block, int)>(_graph.Blocks.Count);

#if NET5_0_OR_GREATER
            visited.EnsureCapacity(_graph.Blocks.Count);
#endif

            // The start block is not marked visited: a loop back into it reaches the reads before
            // `startIndex` too. A copy at the end of a loop body is read at the top of the next
            // iteration (`p = p + 4` feeding the load of `[p]`), and dropping it freezes the loop.
            remaining.Push((startBlock, startIndex));

            usedByMemory = false;

            while (remaining.Count > 0)
            {
                var (currentBlock, index) = remaining.Pop();

                var blockSources = _sourceCache[currentBlock];

                // Process instructions
                for (var i = index; i < currentBlock.Instructions.Count; i++)
                {
                    var instruction = currentBlock.Instructions[i];
                    var sources = blockSources[instruction];

                    // Direct usage check
                    if (sources.Contains(local))
                        return true;

                    // A field access reads the object it is on, whether the field is being read or written,
                    // so the destination has to be considered too - a store is not in Sources.
                    foreach (var operand in instruction.Operands)
                    {
                        if (operand is FieldReference field && field.Local == local)
                        {
                            usedByMemory = true;
                            return true;
                        }

                        if (operand is SelectedFieldReference selected
                            && (selected.Selector == local || selected.Choices.Any(c => c.Field.Local == local)))
                        {
                            usedByMemory = true;
                            return true;
                        }

                        // Likewise, an array element or length reads the array, and taking a slot's address reads it
                        // however the callee uses it - none of which are in Sources when they sit in a destination position.
                        if (operand is ArrayAccess array && (array.Array == local || array.Index == local as IOperand))
                        {
                            usedByMemory = true;
                            return true;
                        }

                        if (operand is ArrayLength length && length.Array == local)
                        {
                            usedByMemory = true;
                            return true;
                        }

                        if (operand is AddressOf address && LocalVariables.ContainsLocal(address.Target, local))
                        {
                            usedByMemory = true;
                            return true;
                        }

                        // The operand of a reference cast is a managed-reference slot typed
                        // LocalVariable: reading it is a use, but a constant could never be
                        // substituted into it, same as a memory base or field receiver. The use
                        // only counts when the operand local can itself carry a managed reference:
                        // for a value-typed, generic-parameter, pointer or untyped operand the
                        // producer must stay droppable, because keeping it would type the operand
                        // as a non-reference stack kind - isinst/castclass rejects those - while a
                        // producerless operand falls back to emitting System.Object, which verifies.
                        if (operand is ReferenceCast cast && cast.Value == local &&
                            IsManagedReferenceLocal(local))
                        {
                            usedByMemory = true;
                            return true;
                        }
                    }

                    // Used in memory operand
                    foreach (var source in sources)
                    {
                        if (source is MemoryOperand memory)
                        {
                            if (memory.Base is LocalVariable memLocal && memLocal == local)
                            {
                                usedByMemory = true;
                                return true;
                            }

                            if (memory.Index is LocalVariable memLocal2 && memLocal2 == local)
                            {
                                usedByMemory = true;
                                return true;
                            }
                        }
                    }
                }

                // Process successors
                foreach (var successor in currentBlock.Successors)
                {
                    if (visited.Add(successor))
                        remaining.Push((successor, 0));
                }
            }

            return false;
        }
    }
}
