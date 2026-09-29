using System.Collections.Generic;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Copy and constant propagation, performed while the graph is still in SSA form.
/// </summary>
public static class SsaSimplifier
{
    public static void Run(MethodAnalysisContext method) =>
        Run(method.ControlFlowGraph!, method.ParameterLocals, method);

    public static void Run(ISILControlFlowGraph cfg, List<LocalVariable> parameterLocals) =>
        Run(cfg, parameterLocals, null);

    private static void Run(ISILControlFlowGraph cfg, List<LocalVariable> parameterLocals,
        MethodAnalysisContext? method)
    {
        // dest -> value for every forwardable copy/constant. SSA's single-assignment property means a
        // local is defined at most once, so there is never a conflicting entry for the same key.
        var forwarded = new Dictionary<LocalVariable, IOperand>();

        foreach (var block in cfg.Blocks)
            foreach (var instruction in block.Instructions)
                if (instruction.OpCode == OpCode.Move
                    && instruction.Operands[0] is LocalVariable dest
                    && !parameterLocals.Contains(dest))
                {
                    // A copy between locals that cannot hold each other's value - a slot merging
                    // unrelated references across paths - has no legal managed store, so the
                    // source is never forwarded into the destination's typed positions (an
                    // address-of field receiver would emit an invalid ldflda). The move itself
                    // stays: the emitter fills the slot with a noted synthetic default (a
                    // decompiler-issue call naming both types), so the stored value is measured
                    // rather than silently dropped. Copies between managed pointers (T& or T*
                    // on both sides) are exempt - the value is the address itself.
                    if (instruction.Operands[1] is LocalVariable copySource
                        && LocalVariables.NoLegalManagedCopy(dest, copySource, allowByRefReinterpret: true))
                        continue;

                    if (IsForwardable(instruction.Operands[1]))
                        forwarded[dest] = instruction.Operands[1];
                }

        if (forwarded.Count == 0)
            return;

        // Collapse copy chains (t1 := a; t2 := t1; ...) so each local maps straight to its final value.
        var resolved = new Dictionary<LocalVariable, IOperand>();
        foreach (var dest in forwarded.Keys)
            resolved[dest] = Resolve(dest, forwarded);

        // One global substitution of every use.
        foreach (var block in cfg.Blocks)
            foreach (var instruction in block.Instructions)
                ReplaceUses(instruction, resolved, method);

        // A forwarded local is dead now - unless a use could not take its value (a constant cannot be
        // a memory base/index, so such a use keeps the original local). Drop the defining Move only
        // once the local truly has no reads left; the leftover nops are cleared by SsaForm.Remove.
        var reads = CollectReadLocals(cfg);
        foreach (var block in cfg.Blocks)
            foreach (var instruction in block.Instructions)
                if (instruction.OpCode == OpCode.Move
                    && instruction.Operands[0] is LocalVariable dest
                    && forwarded.ContainsKey(dest)
                    && !reads.Contains(dest))
                {
                    instruction.OpCode = OpCode.Nop;
                    instruction.SetOperands();
                }
    }

    // Follows local-to-local copies to the end of the chain. The visited set guards against a cycle a
    // malformed graph could present; a well-formed SSA graph (definitions dominate uses) has none.
    private static IOperand Resolve(LocalVariable dest, Dictionary<LocalVariable, IOperand> forwarded)
    {
        var value = forwarded[dest];
        var visited = new HashSet<LocalVariable> { dest };

        while (value is LocalVariable next && forwarded.TryGetValue(next, out var nextValue) && visited.Add(next))
            value = nextValue;

        return value;
    }

    private static void ReplaceUses(Instruction instruction, Dictionary<LocalVariable, IOperand> resolved,
        MethodAnalysisContext? method)
    {
        // The single definition position (a Move/Call destination local) must not be rewritten - only
        // reads are forwarded. In SSA the local being eliminated never appears as a use of itself, so
        // skipping just its own definition operand is sufficient.
        var destination = instruction.Destination;

        for (var i = 0; i < instruction.Operands.Count; i++)
        {
            switch (instruction.Operands[i])
            {
                case LocalVariable local when !ReferenceEquals(local, destination) && resolved.TryGetValue(local, out var value)
                    && (value is not LocalVariable localReplacement
                        || !LocalVariables.CallOperandProvenMismatched(instruction, i,
                            localReplacement, method)):
                    instruction.SetOperand(i, value);
                    break;

                // A memory base/index must stay an address-holding local, so only a local replacement
                // is substituted there; a constant is left in place (which keeps the source Move alive).
                case MemoryOperand memory:
                    if (memory.Base is LocalVariable baseLocal && resolved.TryGetValue(baseLocal, out var baseValue) && baseValue is LocalVariable baseReplacement)
                        memory.Base = baseReplacement;
                    if (memory.Index is LocalVariable indexLocal && resolved.TryGetValue(indexLocal, out var indexValue) && indexValue is LocalVariable indexReplacement)
                        memory.Index = indexReplacement;
                    instruction.SetOperand(i, memory); // MemoryOperand is a struct, write the copy back
                    break;

                // Same as a memory base: the object a field is read from must stay a local, and
                // its type must be able to serve as the receiver - a mismatched local would
                // produce an invalid ldfld.
                case FieldReference { Local: { } fieldLocal } field when resolved.TryGetValue(fieldLocal, out var fieldValue) && fieldValue is LocalVariable fieldReplacement && !LocalVariables.NoLegalManagedCopy(fieldLocal, fieldReplacement)
                    && (method == null || !LocalVariables.ReceiverProvenMismatched(
                        LocalVariables.EmittedSlotLocalType(fieldReplacement, method),
                        LocalVariables.ReceiverHost(field))):
                    field.Local = fieldReplacement;
                    break;
                case SelectedFieldReference selected:
                    if (resolved.TryGetValue(selected.Selector, out var selectorValue) && selectorValue is LocalVariable selectorReplacement)
                        selected.Selector = selectorReplacement;
                    foreach (var choice in selected.Choices)
                        if (resolved.TryGetValue(choice.Field.Local, out var receiverValue) && receiverValue is LocalVariable receiverReplacement && !LocalVariables.NoLegalManagedCopy(choice.Field.Local, receiverReplacement)
                            && (method == null || !LocalVariables.ReceiverProvenMismatched(
                                LocalVariables.EmittedSlotLocalType(receiverReplacement, method),
                                LocalVariables.ReceiverHost(choice.Field))))
                            choice.Field.Local = receiverReplacement;
                    break;

                // Same as a memory base: the operand of a reference cast is a managed-reference
                // slot typed LocalVariable, so only a local replacement is substituted there; a
                // constant stays put, which keeps the source Move alive.
                case ReferenceCast cast
                    when resolved.TryGetValue(cast.Value, out var castValue) && castValue is LocalVariable castReplacement:
                    instruction.SetOperand(i, new ReferenceCast(castReplacement, cast.Type, cast.NullOnFailure));
                    break;

                // An address-take's target can itself be a compound expression (&receiver.field,
                // &array[i].field, &mem[base+index]): the locals inside it are reads like any
                // other, so a forwarded copy substitutes there too. Without this the target still
                // names the old local after its definition is dropped, leaving a use of an
                // unassigned local in the emitted IL.
                case AddressOf address:
                    SubstituteAddressTarget(address, resolved, method);
                    break;
            }
        }
    }

    // Substitution inside an address-take's target. Compound positions - the object or memory
    // cell a field/element is addressed through - take local replacements exactly like their
    // top-level counterparts. A bare local target (&v) is the cell's own identity rather than a
    // value inside it, so forwarding must not rewrite it.
    private static void SubstituteAddressTarget(AddressOf address, Dictionary<LocalVariable, IOperand> resolved,
        MethodAnalysisContext? method)
    {
        switch (address.Target)
        {
            case MemoryOperand memory:
                if (memory.Base is LocalVariable baseLocal && resolved.TryGetValue(baseLocal, out var baseValue) && baseValue is LocalVariable baseReplacement)
                    memory.Base = baseReplacement;
                if (memory.Index is LocalVariable indexLocal && resolved.TryGetValue(indexLocal, out var indexValue) && indexValue is LocalVariable indexReplacement)
                    memory.Index = indexReplacement;
                address.Target = memory; // MemoryOperand is a struct, write the copy back
                break;
            case FieldReference { Local: { } fieldLocal } field
                when resolved.TryGetValue(fieldLocal, out var fieldValue) && fieldValue is LocalVariable fieldReplacement && !LocalVariables.NoLegalManagedCopy(fieldLocal, fieldReplacement)
                     && (method == null || !LocalVariables.ReceiverProvenMismatched(
                         LocalVariables.EmittedSlotLocalType(fieldReplacement, method),
                         LocalVariables.ReceiverHost(field))):
                field.Local = fieldReplacement;
                break;
            case SelectedFieldReference selected:
                if (resolved.TryGetValue(selected.Selector, out var selectorValue) && selectorValue is LocalVariable selectorReplacement)
                    selected.Selector = selectorReplacement;
                foreach (var choice in selected.Choices)
                    if (resolved.TryGetValue(choice.Field.Local, out var receiverValue) && receiverValue is LocalVariable receiverReplacement && !LocalVariables.NoLegalManagedCopy(choice.Field.Local, receiverReplacement)
                        && (method == null || !LocalVariables.ReceiverProvenMismatched(
                            LocalVariables.EmittedSlotLocalType(receiverReplacement, method),
                            LocalVariables.ReceiverHost(choice.Field))))
                        choice.Field.Local = receiverReplacement;
                break;
            case ArrayAccess access:
                if (resolved.TryGetValue(access.Array, out var arrayValue) && arrayValue is LocalVariable arrayReplacement)
                    access.Array = arrayReplacement;
                if (access.Index is LocalVariable elementIndex && resolved.TryGetValue(elementIndex, out var elementValue) && elementValue is LocalVariable elementReplacement)
                    access.Index = elementReplacement;
                break;
            case ArrayElementFieldReference elementField:
                if (resolved.TryGetValue(elementField.Array, out var elementArrayValue) && elementArrayValue is LocalVariable elementArrayReplacement)
                    elementField.Array = elementArrayReplacement;
                if (elementField.Index is LocalVariable elementFieldIndex && resolved.TryGetValue(elementFieldIndex, out var elementIndexValue) && elementIndexValue is LocalVariable elementIndexReplacement)
                    elementField.Index = elementIndexReplacement;
                break;
            case ArrayLength length
                when resolved.TryGetValue(length.Array, out var lengthValue) && lengthValue is LocalVariable lengthReplacement:
                length.Array = lengthReplacement;
                break;
            case ReferenceCast cast
                when resolved.TryGetValue(cast.Value, out var castValue) && castValue is LocalVariable castReplacement:
                address.Target = new ReferenceCast(castReplacement, cast.Type, cast.NullOnFailure);
                break;
            case AddressOf nested:
                SubstituteAddressTarget(nested, resolved, method);
                break;
        }
    }

    // Every local read by some instruction. The single write position (a plain local destination) is
    // excluded; memory and field operands always contribute their address/object locals as reads, as
    // do locals nested inside an address-take's compound target (&receiver.field reads receiver).
    private static HashSet<LocalVariable> CollectReadLocals(ISILControlFlowGraph cfg)
    {
        var reads = new HashSet<LocalVariable>();

        foreach (var block in cfg.Blocks)
            foreach (var instruction in block.Instructions)
            {
                var destination = instruction.Destination;

                foreach (var operand in instruction.Operands)
                {
                    if (operand is LocalVariable destinationLocal && ReferenceEquals(destinationLocal, destination))
                        continue;

                    foreach (var used in LocalVariables.OperandLocals(operand))
                        if (used != null)
                            reads.Add(used);
                }
            }

        return reads;
    }

    // Pure values that are safe to duplicate across uses: other locals (copies) and constants. Memory
    // and field loads are excluded so a load is never re-executed; they are handled post-SSA instead.
    private static bool IsForwardable(IOperand value) =>
        value switch
        {
            LocalVariable => true,
            MemoryOperand => false,
            FieldReference => false,
            SelectedFieldReference => false,
            _ => true
        };
}
