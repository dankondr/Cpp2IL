using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Removes pure instructions whose result is never used. This eliminates, among other things, the
/// dead flag/temporary computations the x86 lifter emits eagerly for every comparison - a single
/// <c>cmp</c>/<c>test</c> produces all of CF/OF/SF/ZF/PF plus scratch temporaries, but the branch
/// that follows only consumes one of them.
///
/// Liveness is marked from the instructions with an effect, per local, so it holds in and out of
/// SSA form: a local with several definitions stays whole while any reader needs it. Instructions
/// are turned into nops rather than spliced out; the structural cleanup happens later, out of SSA,
/// where it is safe for phi nodes.
/// </summary>
public static class DeadCodeEliminator
{
    public static void Run(MethodAnalysisContext method) => Run(method.ControlFlowGraph!);

    public static void Run(ISILControlFlowGraph cfg)
    {
        // A local is live when an instruction with an effect (a call, store, branch, return)
        // reads it, or a pure definition of a live local does. Marking from the effects, rather
        // than counting uses, also removes copies that only feed each other around a loop
        // (`a = b; b = a`), which a use count keeps alive forever.
        var instructions = cfg.Blocks.SelectMany(block => block.Instructions).ToList();
        var live = new HashSet<LocalVariable>();
        var work = new Stack<LocalVariable>();
        var definitions = new Dictionary<LocalVariable, List<Instruction>>();
        foreach (var instruction in instructions)
        {
            if (Pure(instruction) is { } destination)
            {
                (definitions.TryGetValue(destination, out var list) ? list : definitions[destination] = []).Add(instruction);
                continue;
            }
            foreach (var used in UsedLocals(instruction))
                if (live.Add(used))
                    work.Push(used);
        }

        while (work.Count > 0)
            if (definitions.TryGetValue(work.Pop(), out var defs))
                foreach (var definition in defs)
                    foreach (var used in UsedLocals(definition))
                        if (live.Add(used))
                            work.Push(used);

        foreach (var instruction in instructions)
            if (Pure(instruction) is { } destination && !live.Contains(destination))
            {
                instruction.OpCode = OpCode.Nop;
                instruction.SetOperands();
            }
    }

    // The local a pure instruction defines. Stores have a memory or field destination
    // (Destination is not a local) and are never dead.
    private static LocalVariable? Pure(Instruction instruction)
        => IsRemovable(instruction.OpCode) && instruction.Destination is LocalVariable destination ? destination : null;

    /// <summary>
    /// Every local read by the instruction. The single write position - a plain local destination -
    /// is excluded. Memory and field operands always contribute their address/object locals as
    /// reads, even when they are the destination of a store.
    /// </summary>
    internal static IEnumerable<LocalVariable> UsedLocals(Instruction instruction)
    {
        var destination = instruction.Destination as LocalVariable;

        foreach (var operand in instruction.Operands)
        {
            switch (operand)
            {
                case LocalVariable local when !ReferenceEquals(local, destination):
                    yield return local;
                    break;
                case MemoryOperand memory:
                    if (memory.Base is LocalVariable baseLocal)
                        yield return baseLocal;
                    if (memory.Index is LocalVariable indexLocal)
                        yield return indexLocal;
                    break;
                // A static field access doesn't read the storage pointer it was resolved from, so that
                // pointer (and the class load feeding it) is free to die.
                case FieldReference { Field.IsStatic: false, Local: { } fieldLocal }:
                    yield return fieldLocal;
                    break;
                // Handing out a slot's address is a read of it as far as we can tell, whatever the callee then does with it.
                case AddressOf { Target: LocalVariable addressed }:
                    yield return addressed;
                    break;
                case AddressOf { Target: FieldReference { Field.IsStatic: false } addressedField }:
                    yield return addressedField.Local;
                    break;
                case ReferenceCast referenceCast:
                    yield return referenceCast.Value;
                    break;
                // The selector's value is read to pick a field, and each choice is
                // a field access rooted in its own receiver local.
                case SelectedFieldReference selected:
                    yield return selected.Selector;
                    foreach (var receiver in selected.Choices.Select(c => c.Field.Local))
                        if (receiver != null)
                            yield return receiver;
                    break;
                case AddressOf { Target: ArrayAccess addressedElement }:
                    foreach (var used in ArrayAccessLocals(addressedElement))
                        yield return used;
                    break;
                case AddressOf { Target: ArrayElementFieldReference addressedField }:
                    foreach (var used in ArrayElementFieldLocals(addressedField))
                        yield return used;
                    break;
                case ArrayAccess access:
                    foreach (var used in ArrayAccessLocals(access))
                        yield return used;
                    break;
                case ArrayElementFieldReference elementField:
                    foreach (var used in ArrayElementFieldLocals(elementField))
                        yield return used;
                    break;
                case ArrayLength { Array: { } lengthArray }:
                    yield return lengthArray;
                    break;
            }
        }
    }

    private static IEnumerable<LocalVariable> ArrayAccessLocals(ArrayAccess access)
    {
        yield return access.Array;

        if (access.Index is LocalVariable index)
            yield return index;
    }

    private static IEnumerable<LocalVariable> ArrayElementFieldLocals(ArrayElementFieldReference field)
    {
        yield return field.Array;
        if (field.Index is LocalVariable index)
            yield return index;
    }

    /// <summary>
    /// Opcodes with no side effects, so removing a never-read result is safe. Calls, stores,
    /// returns and branches are intentionally excluded.
    /// </summary>
    private static bool IsRemovable(OpCode opCode) =>
        opCode switch
        {
            OpCode.Move or OpCode.Phi
                or OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Modulo
                or OpCode.ShiftLeft or OpCode.ShiftRight
                or OpCode.And or OpCode.Or or OpCode.Xor
                or OpCode.Not or OpCode.Negate or OpCode.SignExtend32 => true,
            >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual => true,
            _ => false
        };
}
