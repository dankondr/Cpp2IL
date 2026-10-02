using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>Collapses IL2CPP's inlined List&lt;T&gt;.Add fast path back to the public Add call.</summary>
internal static class InlinedListAddRecovery
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
        foreach (var slowBlock in cfg.Blocks.ToArray())
        foreach (var call in slowBlock.Instructions)
        {
            if (call is not { OpCode: OpCode.CallVoid, Operands: [MethodAnalysisContext { Name: "AddWithResize" } callee, var receiver, _, ..] }
                || !IsList(callee.DeclaringType)
                || ListLocal(slowBlock, receiver) is not { } list
                || AddBody(slowBlock, list) is not var (body, region, branch, fast, nullChecks))
                continue;

            // Only the proven body goes; the item's computation and whatever else the
            // blocks hold stay, and the slow path's AddWithResize stands for the Add.
            foreach (var block in region)
                block.Instructions.RemoveAll(body.Contains);
            branch.Instructions.Add(new Instruction(call.Index, OpCode.Jump, slowBlock));
            foreach (var (from, to) in nullChecks.Append((branch, fast)))
            {
                from.Successors.Remove(to);
                to.Predecessors.Remove(from);
                from.CalculateBlockType();
            }
            // A block the body filled entirely goes too: branches into it would have no
            // instruction to land on.
            foreach (var emptied in region.Where(block => block != branch && block.Instructions.Count == 0))
            {
                var next = emptied.Successors.Single();
                foreach (var predecessor in emptied.Predecessors)
                {
                    if (predecessor.Instructions.LastOrDefault() is { OpCode: OpCode.Jump or OpCode.ConditionalJump } jump
                        && ReferenceEquals(jump.Operands[0], emptied))
                        jump.SetOperand(0, next);
                    predecessor.Successors[predecessor.Successors.IndexOf(emptied)] = next;
                    if (!next.Predecessors.Contains(predecessor))
                        next.Predecessors.Add(predecessor);
                }
                cfg.RemovePredecessor(next, emptied);
                cfg.Blocks.Remove(emptied);
            }
            return true;
        }
        return false;
    }

    // The inlined body of List<T>.Add ahead of `slowBlock`'s AddWithResize:
    //   items = _items; _version++     Move a, _items; Add t, (_version | t0), 1 [after Move t0, _version]; Move _version, t
    //                                  optionally `if (_items == null) throw` on the way
    //   size = _size                   optional Move s, _size
    //   if (size >= items.Length)      CheckLess c, size, a.Length; Not c2, c | CheckGreaterOrEqual c2, size, a.Length
    //                                  | CheckEqual c2, a.Length, 0 (size known zero); ConditionalJump c2
    // The other successor is the fast path: it may only write registers, the list's own
    // fields and an element of its array, and must rejoin where the slow path does. A temp
    // the body writes must not reach a read outside it. Anything else leaves the Add alone.
    private static (HashSet<Instruction> Body, List<Block> Region, Block Branch, Block Fast,
        List<(Block, Block)> NullChecks)? AddBody(Block slowBlock, LocalVariable list)
    {
        // Inside List<T> itself the slow path is its own Add.
        if (list.IsThis
            || slowBlock.Predecessors is not [var branch] || branch.Successors.Count != 2
            || branch.Instructions.LastOrDefault() is not
                { OpCode: OpCode.ConditionalJump, Operands: [Block, LocalVariable condition] } jump)
            return null;
        var fast = branch.Successors.First(successor => !ReferenceEquals(successor, slowBlock));
        var body = new HashSet<Instruction> { jump };
        var temps = new HashSet<LocalVariable> { condition };

        // The run of blocks ending in the branch, earliest first: straight-line, or
        // leaving only through the array's own `if (_items == null) throw`.
        var region = new List<Block> { branch };
        var nullChecks = new List<(Block, Block)>();
        while (region.Count < 4 && region[0].Predecessors is [var previous]
               && !region[0].Instructions.Any(instruction => IsListField(instruction.Operands.ElementAtOrDefault(0), list, "_version")))
        {
            if (previous.Successors.Count == 2)
            {
                var thrower = previous.Successors.First(successor => !ReferenceEquals(successor, region[0]));
                if (previous.Instructions.LastOrDefault() is not
                        { OpCode: OpCode.ConditionalJump, Operands: [Block, LocalVariable isNull] } nullJump
                    || Definition(previous.Instructions, nullJump, isNull) is not
                        { OpCode: OpCode.CheckEqual, Operands: [_, var tested, Immediate { Value: 0 }] } nullTest
                    || !IsListField(tested, list, "_items")
                    || !thrower.Instructions.Any(instruction => instruction.OpCode == OpCode.Throw))
                    break;
                body.UnionWith([nullJump, nullTest]);
                temps.Add(isNull);
                nullChecks.Add((previous, thrower));
            }
            else if (previous.Successors.Count != 1)
                break;
            region.Insert(0, previous);
        }
        var sequence = region.SelectMany(block => block.Instructions).ToList();
        LocalVariable? items = null;
        IOperand? size = null;
        switch (Definition(sequence, jump, condition))
        {
            case { OpCode: OpCode.Not, Operands: [_, LocalVariable inner] } not
                when Definition(sequence, not, inner) is
                    { OpCode: OpCode.CheckLess, Operands: [_, var checkedSize, ArrayLength { Array: var array }] } check:
                body.UnionWith([not, check]);
                temps.Add(inner);
                (items, size) = (array, checkedSize);
                break;
            case { OpCode: OpCode.CheckGreaterOrEqual, Operands: [_, var checkedSize, ArrayLength { Array: var array }] } check:
                body.Add(check);
                (items, size) = (array, checkedSize);
                break;
            case { OpCode: OpCode.CheckEqual, Operands: [_, ArrayLength { Array: var array }, Immediate { Value: 0 }] } check:
                body.Add(check);
                items = array;
                break;
            default:
                return null;
        }

        if (Definition(sequence, jump, items) is not
                { OpCode: OpCode.Move, Operands: [_, var itemsSource] } itemsLoad
            || !IsListField(itemsSource, list, "_items"))
            return null;
        body.Add(itemsLoad);
        temps.Add(items);

        var versionStores = sequence.Where(instruction => instruction is
            { OpCode: OpCode.Move, Operands: [var destination, LocalVariable] } && IsListField(destination, list, "_version")).ToList();
        if (versionStores is not [var versionStore]
            || Definition(sequence, versionStore, (LocalVariable)versionStore.Operands[1]) is not
                { OpCode: OpCode.Add, Operands: [_, var counter, Immediate { Value: 1 }] } increment)
            return null;
        body.UnionWith([versionStore, increment]);
        temps.Add((LocalVariable)versionStore.Operands[1]);
        if (counter is LocalVariable loaded)
        {
            if (Definition(sequence, increment, loaded) is not { OpCode: OpCode.Move, Operands: [_, var read] } load
                || !IsListField(read, list, "_version"))
                return null;
            body.Add(load);
            temps.Add(loaded);
        }
        else if (!IsListField(counter, list, "_version"))
            return null;

        // Size reads after the prologue - the check's own, and the index the fast path stores
        // at - and the one the check compares, wherever in the run it was read.
        var prologue = sequence.FindIndex(body.Contains);
        foreach (var load in sequence.Skip(prologue).Where(instruction => IsSizeRead(instruction, list)))
        {
            body.Add(load);
            temps.Add((LocalVariable)load.Operands[load.OpCode == OpCode.Call ? 1 : 0]);
        }
        if (size is LocalVariable sizeLocal && !temps.Contains(sizeLocal))
        {
            if (Definition(sequence, jump, sizeLocal) is not { } sizeRead || !IsSizeRead(sizeRead, list))
                return null;
            body.Add(sizeRead);
            temps.Add(sizeLocal);
        }
        else if (size is not null and not LocalVariable && !IsListField(size, list, "_size"))
            return null;

        if (fast.Predecessors is not [_] || !FastPathRejoins(fast, slowBlock, list, items))
            return null;

        var removed = body.Concat(fast.Instructions).ToHashSet();
        foreach (var temp in temps)
        {
            var definition = sequence.Last(instruction => body.Contains(instruction)
                && ReferenceEquals(instruction.Destination, temp));
            if (ReadAfter(region.First(block => block.Instructions.Contains(definition)), definition, temp, removed))
                return null;
        }
        // A register the fast path writes and the code after the join reads must be written
        // on the slow path too, or dropping the fast path would leave the read undefined.
        foreach (var write in fast.Instructions.Where(instruction => instruction.Destination is LocalVariable))
            if (!slowBlock.Instructions.Any(instruction => ReferenceEquals(instruction.Destination, write.Destination))
                && fast.Instructions.Last(instruction => ReferenceEquals(instruction.Destination, write.Destination)) == write
                && ReadAfter(fast, write, (LocalVariable)write.Destination!, removed))
                return null;
        return (body, region, branch, fast, nullChecks);
    }

    // The list whose fields the body works on: the receiver itself, or - when the call
    // re-reads the receiver from its field - the same-typed local the check reads.
    private static LocalVariable? ListLocal(Block slowBlock, IOperand receiver)
    {
        if (receiver is LocalVariable local)
            return local;
        if (receiver is not FieldReference { Field.FieldType: { } listType } || slowBlock.Predecessors is not [var branch])
            return null;
        var checkedList = branch.Instructions.SelectMany(instruction => instruction.Operands).OfType<FieldReference>()
            .FirstOrDefault(field => field.Containers.Count == 0 && field.Field.Name is "_size" or "_items"
                && IsList(field.Field.DeclaringType))?.Local;
        return checkedList?.Type?.FullName == listType.FullName ? checkedList : null;
    }

    // The fast path stores the element and bumps `_size` - writing only registers, the
    // list's own fields and the element - and then does exactly what the slow path does
    // after AddWithResize: the same instructions (a tail the compiler duplicated) before
    // the same continuation, or the same plain return. The lifter's register copies
    // (index -1 moves) only carry registers across the join and are not compared.
    private static bool FastPathRejoins(Block fast, Block slowBlock, LocalVariable list, LocalVariable items)
    {
        var slowTail = WithoutJump(slowBlock.Instructions.SkipWhile(instruction => instruction.Operands.FirstOrDefault()
            is not MethodAnalysisContext { Name: "AddWithResize" }).Skip(1)).Where(instruction => !IsRegisterCopy(instruction)).ToList();
        var own = WithoutJump(fast.Instructions).Where(instruction => !IsRegisterCopy(instruction)).ToList();
        if (fast.Successors.ToHashSet().SetEquals(slowBlock.Successors))
        {
            if (own.Count >= slowTail.Count && own.Skip(own.Count - slowTail.Count).Zip(slowTail).All(pair => Same(pair.First, pair.Second)))
                own.RemoveRange(own.Count - slowTail.Count, slowTail.Count);
            else if (own.LastOrDefault() is { OpCode: OpCode.Return, Operands.Count: 0 }
                     && slowTail.LastOrDefault() is { OpCode: OpCode.Return, Operands.Count: 0 })
                own.RemoveAt(own.Count - 1);
        }
        else if (!(fast.Successors is [var next] && WithoutJump(next.Instructions).Where(instruction => !IsRegisterCopy(instruction)).ToList() is var rest
                   && (rest.Count == slowTail.Count && rest.Zip(slowTail).All(pair => Same(pair.First, pair.Second))
                       && next.Successors.ToHashSet().SetEquals(slowBlock.Successors)
                       || rest is [{ OpCode: OpCode.Return, Operands.Count: 0 }]
                       && slowTail is [{ OpCode: OpCode.Return, Operands.Count: 0 }])))
            return false;

        var element = new HashSet<LocalVariable> { items };
        bool FromElement(Instruction instruction) => instruction.Operands.Skip(1).Any(operand =>
            IsListField(operand, list, "_items") || element.Any(array => Uses(operand, array)));
        foreach (var instruction in own)
        {
            if (instruction.OpCode == OpCode.Nop)
                continue;
            if (instruction.IsCall && !IsSizeRead(instruction, list)
                || instruction.OpCode is OpCode.Jump or OpCode.ConditionalJump or OpCode.Return)
                return false;
            switch (instruction.Operands.FirstOrDefault())
            {
                case LocalVariable local:
                    // Addresses computed from the items array are where the element goes.
                    if (FromElement(instruction))
                        element.Add(local);
                    break;
                case AddressOf { Target: FieldReference { Local: var address } } when FromElement(instruction):
                    element.Add(address);
                    break;
                case FieldReference field when IsListField(field, list, "_size") || IsListField(field, list, "_version")
                                               || element.Contains(field.Local):
                    break;
                case ArrayAccess access when element.Contains(access.Array):
                    break;
                case MemoryOperand { Base: LocalVariable address } when element.Contains(address):
                    break;
                default:
                    return false;
            }
        }
        return true;
    }

    // `s = _size`, or the `s = get_Count()` an earlier pass made of it where the getter is
    // provably the field's accessor.
    private static bool IsSizeRead(Instruction instruction, LocalVariable list) => instruction switch
    {
        { OpCode: OpCode.Move, Operands: [LocalVariable, var source] } => IsListField(source, list, "_size"),
        { OpCode: OpCode.Call, Operands: [MethodAnalysisContext { Name: "get_Count" } getter, LocalVariable, var receiver] }
            => ReferenceEquals(receiver, list) && IsList(getter.DeclaringType),
        _ => false,
    };

    private static bool IsRegisterCopy(Instruction instruction) => instruction is { OpCode: OpCode.Move, Index: -1 };

    private static List<Instruction> WithoutJump(IEnumerable<Instruction> instructions)
    {
        var list = instructions.ToList();
        if (list.LastOrDefault() is { OpCode: OpCode.Jump })
            list.RemoveAt(list.Count - 1);
        return list;
    }

    private static bool Same(Instruction a, Instruction b) =>
        a.OpCode == b.OpCode && a.Operands.Count == b.Operands.Count
        && a.Operands.Zip(b.Operands).All(pair => ReferenceEquals(pair.First, pair.Second)
            || pair.First is not Block && pair.Second is not Block && pair.First.ToString() == pair.Second.ToString());

    private static Instruction? Definition(List<Instruction> instructions, Instruction user, LocalVariable local)
    {
        for (var i = instructions.IndexOf(user) - 1; i >= 0; i--)
            if (ReferenceEquals(instructions[i].Destination, local))
                return instructions[i];
        return null;
    }

    private static bool IsListField(IOperand? operand, LocalVariable list, string name) =>
        operand is FieldReference { Containers.Count: 0 } field
        && ReferenceEquals(field.Local, list) && field.Field.Name == name;

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
        ArrayLength length => ReferenceEquals(length.Array, local),
        ArrayAccess element => ReferenceEquals(element.Array, local) || Uses(element.Index, local),
        _ => false,
    };

    private static bool IsList(TypeAnalysisContext? type) =>
        type?.DefaultFullName.StartsWith("System.Collections.Generic.List`1") == true
        || type is GenericInstanceTypeAnalysisContext { GenericType.DefaultFullName: "System.Collections.Generic.List`1" };
}
