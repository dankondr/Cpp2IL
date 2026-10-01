using System;
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
    public static void Run(MethodAnalysisContext method) => Run(method.ControlFlowGraph!, method);

    /// <summary>
    /// The lifter ends a method that falls off its last call with a Return; once that call is
    /// known never to return and became a Throw, nothing reaches the Return after it, and
    /// emitting it only spells a value that never existed. It is spliced out, not turned into a
    /// nop, so the body still ends in the throw instead of falling off its end.
    /// </summary>
    public static void RemoveReturnsAfterThrow(ISILControlFlowGraph cfg)
    {
        foreach (var block in cfg.Blocks.ToList())
        {
            var thrown = block.Instructions.FindIndex(i => i.OpCode == OpCode.Throw);
            if (thrown >= 0 && LoneReturn(block.Instructions.Skip(thrown + 1)))
                block.Instructions.RemoveRange(thrown + 1, block.Instructions.Count - thrown - 1);
            // The Return can also sit in a block of its own that only throwing blocks fall into.
            else if (block != cfg.EntryBlock && block != cfg.ExitBlock && block.Predecessors.Count > 0
                     && LoneReturn(block.Instructions)
                     && block.Predecessors.All(p => p.Instructions.LastOrDefault(i => i.OpCode != OpCode.Nop) is { OpCode: OpCode.Throw }))
            {
                foreach (var successor in block.Successors)
                    successor.Predecessors.Remove(block);
                foreach (var predecessor in block.Predecessors)
                    predecessor.Successors.Remove(block);
                cfg.Blocks.Remove(block);
            }
        }

        static bool LoneReturn(IEnumerable<Instruction> instructions)
            => instructions.Where(i => i.OpCode != OpCode.Nop).ToList() is [{ OpCode: OpCode.Return }];
    }

    /// <summary>
    /// `new T[w, h]` writes its lengths into a stack buffer and passes only `&amp;lengths[0]` to the
    /// array stub (<see cref="ArrayRecovery.IsArrayNewWithoutBounds"/>), so the stores of the later
    /// lengths name cells nothing reads directly. They stay until the stub becomes a NewArr that
    /// takes them as operands. A store of a register's entry value there is a callee-saved spill
    /// that happens to sit next to the buffer, not a length.
    /// </summary>
    internal static Func<Instruction, bool> StoresArrayNewLengths(MethodAnalysisContext? method, IList<Instruction> instructions)
    {
        // ponytail: passes that run DCE on a bare graph reach the app through the global context.
        if ((method?.AppContext ?? Cpp2IlApi.CurrentAppContext) is not { } app)
            return _ => false;
        var buffers = new List<long>();
        foreach (var call in instructions)
        {
            if (call is not { OpCode: OpCode.Call, Operands: [Immediate target, _, _, var lengths, ..] }
                || !ArrayRecovery.IsArrayNewWithoutBounds(app, target.UnsignedValue))
                continue;
            var buffer = lengths as AddressOf ?? (lengths is LocalVariable pointer
                ? instructions.FirstOrDefault(i => ReferenceEquals(i.Destination, pointer))?.Operands[1] as AddressOf
                : null);
            if (buffer is { Target: LocalVariable first } && FrameStructFieldReads.FrameOffset(first) is { } offset)
                buffers.Add(offset);
        }
        // ponytail: lengths of rank <= 4, so three cells past the first.
        return buffers.Count == 0
            ? _ => false
            : store => store is { OpCode: OpCode.Move, Operands: [LocalVariable cell, var value] }
                       && value is not LocalVariable { Register.Version: < 1 }
                       && FrameStructFieldReads.FrameOffset(cell) is { } at
                       && buffers.Any(start => start < at && at - start <= 24);
    }

    public static void Run(ISILControlFlowGraph cfg, MethodAnalysisContext? method = null)
    {
        // A local is live when an instruction with an effect (a call, store, branch, return)
        // reads it, or a pure definition of a live local does. Marking from the effects, rather
        // than counting uses, also removes copies that only feed each other around a loop
        // (`a = b; b = a`), which a use count keeps alive forever.
        var instructions = cfg.Blocks.SelectMany(block => block.Instructions).ToList();
        var live = new HashSet<LocalVariable>();
        var work = new Stack<LocalVariable>();
        var definitions = new Dictionary<LocalVariable, List<Instruction>>();
        var lengths = StoresArrayNewLengths(method, instructions);
        LocalVariable? Removable(Instruction instruction)
            => Pure(instruction) is { } destination && !lengths(instruction) ? destination : null;
        foreach (var instruction in instructions)
        {
            if (Removable(instruction) is { } destination)
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
            if (Removable(instruction) is { } destination && !live.Contains(destination))
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
