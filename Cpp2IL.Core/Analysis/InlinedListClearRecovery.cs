using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>Collapses IL2CPP's inlined List&lt;T&gt;.Clear body back to the public Clear call.</summary>
internal static class InlinedListClearRecovery
{
    internal static int Run(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph;
        if (cfg == null)
            return 0;

        var recovered = 0;
        while (TryRecoverOne(cfg))
        {
            recovered++;
            cfg.RemoveUnreachableBlocks();
        }
        return recovered;
    }

    private static bool TryRecoverOne(ISILControlFlowGraph cfg)
    {
        foreach (var block in cfg.Blocks.ToArray())
        foreach (var anchor in block.Instructions.Where(instruction => instruction is
                 {
                     OpCode: OpCode.Move,
                     Operands: [FieldReference { Field.Name: "_size", Containers.Count: 0 } size, Immediate { Value: 0 }]
                 } && IsList(size.Field.DeclaringType)).ToArray())
        {
            var sizeField = (FieldReference)anchor.Operands[0];
            if (ClearBody(block, anchor, sizeField.Local) is not var (body, clearBlock))
                continue;

            var listType = sizeField.Field.DeclaringType;
            var listDefinition = listType is GenericInstanceTypeAnalysisContext instanceType
                ? instanceType.GenericType
                : listType;
            var clear = listDefinition.Methods.FirstOrDefault(candidate => candidate.Name == "Clear"
                && !candidate.IsStatic && candidate.Parameters.Count == 0
                && (candidate.Attributes & MethodAttributes.MemberAccessMask) == MethodAttributes.Public);
            if (clear == null)
                continue;

            var anchorIndex = block.Instructions.IndexOf(anchor);
            var evidence = ReceiverType(block.Instructions.Take(anchorIndex), sizeField.Local)
                ?? sizeField.Local.Type;
            var target = evidence is GenericInstanceTypeAnalysisContext instance
                ? new ConcreteGenericMethodAnalysisContext(clear, instance.GenericArguments, [])
                : clear;

            // Only the proven body goes; whatever the block does around it stays in place.
            var at = block.Instructions.FindIndex(body.Contains);
            block.Instructions.RemoveAll(body.Contains);
            block.Instructions.Insert(at, new Instruction(anchor.Index, OpCode.CallVoid, target, sizeField.Local));
            if (clearBlock != null)
            {
                block.Successors.Remove(clearBlock);
                clearBlock.Predecessors.Remove(block);
            }
            block.CalculateBlockType();
            return true;
        }
        return false;
    }

    // The inlined body of List<T>.Clear around `_size = 0` in `block`:
    //   _version++                      Add t, (_version | t0), 1 [after Move t0, _version]; Move _version, t
    //   size = _size                    optional Move s, _size (or s = get_Count())
    //   _size = 0
    //   Array.Clear(_items, 0, size)    inline, or in `clearBlock` behind `if (size < 1) goto merge`
    // Its temps must not reach a read outside it. A shape that cannot be matched leaves the body alone.
    private static (HashSet<Instruction> Body, Block? ClearBlock)? ClearBody(Block block, Instruction anchor,
        LocalVariable list)
    {
        var instructions = block.Instructions;
        var body = new HashSet<Instruction> { anchor };
        var temps = new HashSet<LocalVariable>();

        var versionStores = instructions.Where(instruction => instruction is
            { OpCode: OpCode.Move, Operands: [FieldReference { Field.Name: "_version", Containers.Count: 0 } v, LocalVariable] }
            && ReferenceEquals(v.Local, list)).ToList();
        if (versionStores is not [var versionStore])
            return null;
        var incremented = (LocalVariable)versionStore.Operands[1];
        if (DefinitionBefore(instructions, versionStore, incremented) is not
            { OpCode: OpCode.Add, Operands: [_, var counter, Immediate { Value: 1 }] } increment)
            return null;
        body.Add(versionStore);
        body.Add(increment);
        temps.Add(incremented);
        if (counter is LocalVariable loaded)
        {
            if (DefinitionBefore(instructions, increment, loaded) is not
                { OpCode: OpCode.Move, Operands: [_, FieldReference { Field.Name: "_version", Containers.Count: 0 } read] } load
                || !ReferenceEquals(read.Local, list))
                return null;
            body.Add(load);
            temps.Add(loaded);
        }
        else if (!IsListField(counter, list, "_version"))
            return null;

        var anchorIndex = instructions.IndexOf(anchor);
        var saved = instructions.Take(anchorIndex).Where(instruction => SizeRead(instruction, list) != null).ToList();
        if (saved.Count > 1)
            return null;
        var savedSize = saved.Count == 1 ? SizeRead(saved[0], list) : null;
        if (saved.Count == 1)
            body.Add(saved[0]);
        bool IsSize(IOperand operand) => IsListField(operand, list, "_size")
            || savedSize != null && ReferenceEquals(operand, savedSize);
        bool ClearsItems(Instruction instruction) => instruction is
            {
                OpCode: OpCode.CallVoid,
                Operands: [MethodAnalysisContext { Name: "Clear", DeclaringType.FullName: "System.Array" }, var items, ..]
            } && IsListField(items, list, "_items");
        bool IsArrayClear(Instruction instruction) => ClearsItems(instruction)
            && instruction.Operands is [_, _, Immediate { Value: 0 }, var length] && IsSize(length);

        Block? clearBlock = null;
        if (instructions.LastOrDefault() is { OpCode: OpCode.ConditionalJump, Operands: [Block merge, LocalVariable condition] } jump
            && DefinitionBefore(instructions, jump, condition) is
                { OpCode: OpCode.CheckLess, Operands: [_, var checkedSize, Immediate { Value: 1 }] } check
            && IsSize(checkedSize))
        {
            // `if (size < 1) goto merge;` with Array.Clear on the fall-through path,
            // which rejoins merge or returns exactly as merge does. Besides the call, that
            // path may only write registers: Clear has no result, so a register live into
            // merge holds the same source value on both paths, and the clear path's writes
            // (restores after the clobbering call) are redundant with the skip path.
            if (block.Successors.Count != 2 || !block.Successors.Contains(merge))
                return null;
            clearBlock = block.Successors.First(successor => !ReferenceEquals(successor, merge));
            var last = clearBlock.Instructions.LastOrDefault();
            if (clearBlock.Predecessors.Count != 1
                || clearBlock.Instructions.Count(IsArrayClear) != 1
                || !clearBlock.Instructions.All(instruction => IsArrayClear(instruction)
                    || instruction is { OpCode: OpCode.Move, Operands: [LocalVariable, not MemoryOperand] }
                    || ReferenceEquals(instruction, last) && instruction.OpCode is OpCode.Return or OpCode.Jump)
                || !(clearBlock.Successors.Count == 1 && ReferenceEquals(clearBlock.Successors[0], merge)
                     || SameReturn(clearBlock, merge)))
                return null;
            body.Add(check);
            body.Add(jump);
            temps.Add(condition);
        }
        else
        {
            // An Array.Clear behind a size check this shape does not match, or over a length
            // it does not recognize as the size, is not a delimited body.
            if (block.Successors.Any(successor => successor.Instructions.Any(ClearsItems)))
                return null;
            var inline = instructions.Skip(anchorIndex + 1).Where(ClearsItems).ToList();
            if (inline.Count > 1 || !inline.All(IsArrayClear))
                return null;
            body.UnionWith(inline);
        }

        // A temp the body writes must not reach a read outside the body.
        var removed = clearBlock == null ? body : body.Concat(clearBlock.Instructions).ToHashSet();
        foreach (var temp in temps)
            if (ReadAfter(block, instructions.Last(instruction => body.Contains(instruction)
                    && ReferenceEquals(instruction.Destination, temp)), temp, removed))
                return null;
        // A saved size still read later is the caller's own read of the old size: it stays,
        // provided it runs before the Clear call takes the body's place.
        if (saved.Count == 1 && ReadAfter(block, saved[0], savedSize!, removed))
        {
            if (instructions.FindIndex(body.Contains) != instructions.IndexOf(saved[0]))
                return null;
            body.Remove(saved[0]);
        }
        // The skip edge's half of a register merge whose other half sits on the dropped
        // clear path is a no-op when nothing reads the merged register afterwards.
        if (clearBlock != null)
            foreach (var copy in instructions.Where(instruction => instruction is
                         { OpCode: OpCode.Move, Index: -1, Operands: [LocalVariable merged, _] }
                         && clearBlock.Instructions.Any(write => ReferenceEquals(write.Destination, merged))).ToList())
                if (!ReadAfter(block, copy, (LocalVariable)copy.Operands[0], removed))
                    body.Add(copy);
        return (body, clearBlock);
    }

    private static Instruction? DefinitionBefore(List<Instruction> instructions, Instruction user, LocalVariable local)
    {
        for (var i = instructions.IndexOf(user) - 1; i >= 0; i--)
            if (instructions[i].Operands.Count > 0 && ReferenceEquals(instructions[i].Operands[0], local))
                return instructions[i];
        return null;
    }

    // `s = _size`, or the `s = get_Count()` an earlier pass made of it where the getter is
    // provably the field's accessor.
    private static LocalVariable? SizeRead(Instruction instruction, LocalVariable list) => instruction switch
    {
        { OpCode: OpCode.Move, Operands: [LocalVariable size, var source] } when IsListField(source, list, "_size") => size,
        { OpCode: OpCode.Call, Operands: [MethodAnalysisContext { Name: "get_Count" } getter, LocalVariable size, var receiver] }
            when ReferenceEquals(receiver, list) && IsList(getter.DeclaringType) => size,
        _ => null,
    };

    private static bool IsListField(IOperand operand, LocalVariable list, string name) =>
        operand is FieldReference { Containers.Count: 0 } field
        && ReferenceEquals(field.Local, list) && field.Field.Name == name;

    // Clear at the end of a method: `Array.Clear; return` beside a bare `return`.
    private static bool SameReturn(Block clearBlock, Block merge) =>
        clearBlock.Instructions[^1] is { OpCode: OpCode.Return } clearReturn
        && merge.Instructions is [{ OpCode: OpCode.Return } mergeReturn]
        && clearReturn.Operands.Count == 0 && mergeReturn.Operands.Count == 0;

    // Locals are register webs: a later plain write of `temp` ends its live range, a read before
    // any such write (on any path, loops included) means the value is still needed.
    private static bool ReadAfter(Block block, Instruction definition, LocalVariable temp,
        HashSet<Instruction> removed)
    {
        var pending = new Stack<(Block Block, int Start)>();
        pending.Push((block, block.Instructions.IndexOf(definition) + 1));
        var visited = new HashSet<Block>();
        while (pending.Count > 0)
        {
            var (current, start) = pending.Pop();
            var killed = false;
            for (var i = start; i < current.Instructions.Count && !killed; i++)
            {
                var instruction = current.Instructions[i];
                if (removed.Contains(instruction))
                    continue;
                if (Reads(instruction, temp))
                    return true;
                killed = ReferenceEquals(instruction.Destination, temp);
            }
            if (!killed)
                foreach (var successor in current.Successors)
                    if (visited.Add(successor))
                        pending.Push((successor, 0));
        }
        return false;
    }

    // Every operand but the written slot itself: `Add t, t, 1` reads `t`, `Move t, x` does not.
    private static bool Reads(Instruction instruction, LocalVariable temp)
    {
        var written = ReferenceEquals(instruction.Destination, temp)
            ? instruction.OpCode switch
            {
                OpCode.Call or OpCode.IndirectCall => 1,
                OpCode.MemoryCopy or OpCode.MemorySet or OpCode.MemoryMove => 3,
                _ => 0,
            }
            : -1;
        return instruction.Operands.Where((_, index) => index != written).Any(operand => Uses(operand, temp));
    }

    private static bool Uses(IOperand? operand, LocalVariable local) => operand switch
    {
        LocalVariable variable => ReferenceEquals(variable, local),
        FieldReference field => ReferenceEquals(field.Local, local),
        MemoryOperand memory => Uses(memory.Base, local) || Uses(memory.Index, local),
        AddressOf address => Uses(address.Target, local),
        _ => false,
    };

    private static TypeAnalysisContext? ReceiverType(IEnumerable<Instruction> prefix, LocalVariable receiver)
    {
        foreach (var instruction in prefix.Reverse())
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable destination, FieldReference source] }
                && ReferenceEquals(destination, receiver) && IsList(source.Field.FieldType))
                return source.Field.FieldType;
        return null;
    }

    private static bool IsList(TypeAnalysisContext? type) =>
        type?.DefaultFullName.StartsWith("System.Collections.Generic.List`1") == true
        || type is GenericInstanceTypeAnalysisContext { GenericType.DefaultFullName: "System.Collections.Generic.List`1" };
}
