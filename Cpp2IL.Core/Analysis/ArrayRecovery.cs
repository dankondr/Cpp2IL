using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Turns the raw Il2CppArray layout (header, then length, then inline elements) back into array ops
public static class ArrayRecovery
{
    private static readonly HashSet<string> ArrayNewFunctions =
    [
        "SzArrayNew",
        "il2cpp_vm_array_new_specific",
        "il2cpp_array_new_specific",
    ];

    // Il2CppArray is {Il2CppObject obj; void* bounds; il2cpp_array_size_t max_length;} then the elements, on all versions(?)
    private static long LengthOffset(int pointerSize) => 3L * pointerSize;
    private static long ElementsOffset(int pointerSize) => 4L * pointerSize;

    public static void Run(MethodAnalysisContext method)
    {
        // Whole-element stores are themselves resolved by RecoverAccesses, so the
        // bulk-copy pass must run first or its redundant-chunk cleanup never sees
        // the MemoryOperand shape it matches.
        RecoverStructArrayBulkCopies(method);
        RecoverMultiDimensionalAllocations(method);
        RecoverOutlinedGetters(method);
        RecoverMultiDimensionalAccesses(method);
        RecoverAccesses(method);
        RecoverElementPointerWalkers(method);
        RecoverReferenceArrayOffsetWalkers(method);
        RecoverStructPointerWalkers(method);
        RecoverObjectFieldAddresses(method);
        RecoverFieldAddressAliases(method);
        RecoverValueTypeFieldAddresses(method);
        RecoverStructElementAddresses(method);
        GroupInitialisers(method.ControlFlowGraph!);
    }

    // A multi-dimensional array (T[,]) keeps its lengths in a bounds block: `b = [array + 2p]`,
    // then one {length, lower bound} pair of 2p bytes per dimension, so `[b + 2p·k]` is
    // GetLength(k). Its elements are row-major after the header: `array + 4p + (i·len1 + j)·size`.
    // An index is taken only when the method compares it with its own dimension's length (the
    // bounds check il2cpp emits before every access), so an address the code never proved is
    // left alone. Lengths become `Array.GetLength` calls; an element is `T[,]::Get/Set/Address`,
    // and a field of a struct element is read or written through `Address`.
    internal static void RecoverMultiDimensionalAccesses(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var definitions = SingleDefinitions(cfg);
        var bounds = new Dictionary<LocalVariable, LocalVariable>();
        foreach (var instruction in cfg.Instructions)
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable block,
                    MemoryOperand { Base: LocalVariable { Type: ArrayTypeAnalysisContext } array, Index: null, Scale: 0 } source] }
                && source.Addend == 2L * pointerSize && definitions.TryGetValue(block, out var single) && single != null)
                bounds[block] = array;
        if (bounds.Count == 0)
            return;

        var int32 = method.AppContext.SystemTypes.SystemInt32Type;
        var allDefinitions = cfg.Instructions.Where(d => d.Destination is LocalVariable)
            .GroupBy(d => (LocalVariable)d.Destination!).ToDictionary(g => g.Key, g => g.ToList());
        var columns = new Dictionary<LocalVariable, LocalVariable>();
        var getLength = method.AppContext.SystemTypes.SystemArrayType?.Methods
            .FirstOrDefault(m => m.Name == "GetLength" && m.Parameters.Count == 1);
        var created = 0;

        // Elements first: their proofs read the length operands before those become calls.
        foreach (var instruction in cfg.Instructions.ToList())
        for (var i = 0; i < instruction.Operands.Count; i++)
        {
            if (instruction.Operands[i] is not MemoryOperand { Base: LocalVariable pointer, Index: null, Scale: 0 } memory)
                continue;
            // `[p + k]` with `p = q + c` is `[q + c + k]`; `q` is the array itself or array + offset.
            var (root, addend) = (pointer, memory.Addend);
            for (var depth = 0; depth < 8 && root.Type is not ArrayTypeAnalysisContext
                                && definitions.TryGetValue(root, out var step)
                                && step is { OpCode: OpCode.Add, Operands: [_, LocalVariable from, Immediate constant] }; depth++)
                (root, addend) = (from, addend + constant.Value);
            var matched = root.Type is ArrayTypeAnalysisContext
                ? Element(root, null, addend, memory, instruction, i)
                : definitions.TryGetValue(root, out var address)
                  && address is { OpCode: OpCode.Add, Operands: [_, var left, var right] }
                    ? Element(left, right, addend, memory, instruction, i) ?? Element(right, left, addend, memory, instruction, i)
                    : null;
            if ((matched ?? Walk(pointer, memory, instruction, i)) is not { } element)
                continue;

            var (array, arrayType, indices, field) = element;
            var store = instruction.OpCode == OpCode.Move && i == 0;
            var block = cfg.Blocks.First(b => b.Instructions.Contains(instruction));
            if (field == null && store)
            {
                instruction.OpCode = OpCode.CallVoid;
                instruction.SetOperands([Accessor(arrayType, "Set"), array, .. indices, instruction.Operands[1]]);
                break;
            }
            if (field == null && instruction is { OpCode: OpCode.Move, Operands: [LocalVariable, _] } && i == 1)
            {
                instruction.OpCode = OpCode.Call;
                instruction.SetOperands([Accessor(arrayType, "Get"), instruction.Operands[0], array, .. indices]);
                break;
            }
            var name = field == null ? "Get" : "Address";
            var accessor = Accessor(arrayType, name);
            var value = NewLocal(accessor.ReturnType);
            block.Instructions.Insert(block.Instructions.IndexOf(instruction),
                new Instruction(-1, OpCode.Call, [accessor, value, array, .. indices]));
            instruction.SetOperand(i, field == null
                ? value
                : new FieldReference(field, value, (int)field.Offset, [], memory.AccessSize));
        }

        // The address arithmetic the elements no longer read is dead; drop it before the
        // lengths it multiplied become calls.
        bool removed;
        do
        {
            var used = cfg.Instructions.SelectMany(DeadCodeEliminator.UsedLocals).ToHashSet();
            removed = false;
            foreach (var dead in cfg.Instructions.Where(d => d is { OpCode: OpCode.Add or OpCode.Multiply
                             or OpCode.ShiftLeft or OpCode.SignExtend32, Destination: LocalVariable destination }
                         && !used.Contains((LocalVariable)d.Destination!)).ToList())
            {
                MakeNop(dead);
                removed = true;
            }
        } while (removed);

        // Then every length still read from a bounds block.
        if (getLength != null)
            foreach (var instruction in cfg.Instructions.ToList())
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                // A local copied from a length is the length where it is read, not where it is written.
                if (ReferenceEquals(instruction.Operands[i], instruction.Destination)
                    || Length(instruction.Operands[i]) is not { } length)
                    continue;
                var value = NewLocal(int32);
                var block = cfg.Blocks.First(b => b.Instructions.Contains(instruction));
                block.Instructions.Insert(block.Instructions.IndexOf(instruction),
                    new Instruction(-1, OpCode.Call, getLength, value, length.Array, new Immediate(length.Dimension)));
                instruction.SetOperand(i, value);
            }

        // A bounds block nothing reads any more is gone with its loads.
        foreach (var (block, _) in bounds)
            if (!cfg.Instructions.Any(instruction => instruction.Operands.Any(o => Mentions(o, block))
                                                     && !ReferenceEquals(instruction.Destination, block)))
                foreach (var definition in cfg.Instructions.Where(d => ReferenceEquals(d.Destination, block)).ToList())
                    MakeNop(definition);
        return;

        (LocalVariable Array, TypeAnalysisContext Dimensioned)? BoundsOf(IOperand operand)
            => operand is LocalVariable block && bounds.TryGetValue(block, out var array) ? (array, array.Type!) : null;

        (LocalVariable Array, int Dimension)? Length(IOperand operand)
        {
            if (operand is LocalVariable local && definitions.TryGetValue(local, out var definition)
                && definition is { OpCode: OpCode.Move, Operands: [_, MemoryOperand copied] })
                operand = copied;
            return operand is MemoryOperand { Index: null, Scale: 0 } memory && memory.Base != null
                && BoundsOf(memory.Base) is { } owner
                && memory.Addend % (2L * pointerSize) == 0
                && memory.Addend / (2L * pointerSize) is var dimension
                && dimension < ((ArrayTypeAnalysisContext)owner.Dimensioned).Rank
                ? (owner.Array, (int)dimension)
                : null;
        }

        bool IsLength(IOperand operand, IOperand array, int dimension)
            => Length(operand) is { } length && length.Dimension == dimension && SameValue(length.Array, array);

        // The receiver is the array operand the address was computed from: `array + offset + addend`,
        // or `array + addend` with no offset (every index before the last is 0).
        (IOperand Array, ArrayTypeAnalysisContext Type, List<IOperand> Indices, FieldAnalysisContext? Field)?
            Element(IOperand array, IOperand? offset, long addend, MemoryOperand memory, Instruction user, int operandIndex)
        {
            var arrayType = array switch
            {
                LocalVariable { Type: ArrayTypeAnalysisContext local } => local,
                FieldReference { Field.FieldType: ArrayTypeAnalysisContext stored } => stored,
                _ => null,
            };
            if (arrayType == null)
                return null;
            var elementType = arrayType.ElementType;
            var size = SizeOf(elementType);
            var relative = addend - ElementsOffset(pointerSize);
            if (size <= 0 || relative < 0
                || (offset == null ? Enumerable.Repeat<IOperand>(new Immediate(0), arrayType.Rank).ToList()
                    : ScaledIndex(offset, size, definitions, 0) is { } flat ? Indices(flat, arrayType.Rank, array)
                    : ConstantOuter(offset, size, array, arrayType.Rank)) is not { } indices
                || indices.Select((index, dimension) => index is Immediate || Compared(index, array, dimension)).Any(ok => !ok))
                return null;
            // A constant last index is folded into the displacement: `grid[1, 1]` of 8-byte elements
            // is `[grid + (len1 << 3) + 0x28]`.
            if (relative >= size)
            {
                if (indices[^1] is not Immediate last)
                    return null;
                indices[^1] = new Immediate(last.Value + relative / size);
            }

            return Part(elementType, size, relative % size, memory, user, operandIndex)
                is { } part ? (array, arrayType, indices, part.Field) : null;
        }

        // A constant outer index scales the last length by index·size in one step: `grid[2, j]`
        // of 4-byte elements is `len1 << 3`. The last index is then 0 or folded into the displacement.
        List<IOperand>? ConstantOuter(IOperand offset, long size, IOperand array, int rank)
            => rank > 1
               && Definition(offset) is { OpCode: OpCode.ShiftLeft or OpCode.Multiply, Operands: [_, var length, Immediate factor] } scaling
               && IsLength(length, array, rank - 1)
               && (scaling.OpCode == OpCode.Multiply ? factor.Value : factor.Value is >= 0 and < 62 ? 1L << (int)factor.Value : 0)
                   is > 0 and var scale
               && scale % size == 0
               && Indices(new Immediate(scale / size), rank - 1, array) is { } outer
                ? [.. outer, new Immediate(0)]
                : null;

        // What an access at `inner` bytes into an element reads: the whole element, or one field of
        // a struct element.
        (bool Whole, FieldAnalysisContext? Field)? Part(TypeAnalysisContext elementType, long size, long inner,
            MemoryOperand memory, Instruction user, int operandIndex)
        {
            if (inner == 0 && (!elementType.IsValueType || ElementSize(elementType, pointerSize) != 0
                               || memory.AccessSize == 0 || memory.AccessSize >= size
                               || ArgumentType(user, operandIndex) is { } parameter
                                  && parameter.FullName == elementType.FullName))
                return (true, null);
            return elementType.IsValueType && ElementSize(elementType, pointerSize) == 0
                && FindValueTypeField(elementType, inner) is { } field
                && (memory.AccessSize == 0 || PrimitiveElementFieldSize(field.FieldType, pointerSize) == memory.AccessSize)
                ? (false, field)
                : null;
        }

        long SizeOf(TypeAnalysisContext elementType) => elementType.IsValueType && ElementSize(elementType, pointerSize) == 0
            ? MetadataElementSize(elementType, pointerSize)
            : ElementSize(elementType, pointerSize);

        static ArrayTypeAnalysisContext? GridType(IOperand operand) => operand switch
        {
            LocalVariable { Type: ArrayTypeAnalysisContext { Rank: 2 } local } => local,
            FieldReference { Field.FieldType: ArrayTypeAnalysisContext { Rank: 2 } stored } => stored,
            _ => null,
        };

        // Walks along the last dimension of a T[,] (only rank 2). A row walk starts a pointer at
        // `data + len1·s` - s the row index scaled by the element size, directly or as a
        // counter that steps with it - and advances it one element per step: the element is
        // [row, column], column a counter the walk gets (0 at the start, +1 per step). An
        // offset walk reads `[grid + off + d]` with `off` stepping by the element size from s
        // alongside a counter k from k0 = (s + d - 4p) / size (the header and k0 may be folded
        // into either s or d): the element is [0, k], and k must be compared with
        // the row length like any index. The row must not change between the walk's start and
        // the access.
        (IOperand Array, ArrayTypeAnalysisContext Type, List<IOperand> Indices, FieldAnalysisContext? Field)?
            Walk(LocalVariable pointer, MemoryOperand memory, Instruction user, int operandIndex)
        {
            if (!allDefinitions.TryGetValue(pointer, out var defs))
                return null;

            if (defs.Count == 1 && defs[0] is { OpCode: OpCode.Add, Operands: [_, var a, var b] })
                foreach (var (array, offset) in new[] { (a, b), (b, a) })
                {
                    if (GridType(array) is not { } offsetGrid || offset is not LocalVariable off
                        || Induction(off) is not { } offInduction)
                        continue;
                    var size = SizeOf(offsetGrid.ElementType);
                    var relative = memory.Addend + offInduction.Start - ElementsOffset(pointerSize);
                    if (size <= 0 || offInduction.Step != size || relative < 0)
                        continue;
                    var counter = allDefinitions.Keys.FirstOrDefault(k => Induction(k) is { Step: 1 } kInduction
                        && kInduction.Start == relative / size && CoInductive(kInduction, offInduction, user));
                    if (counter == null || !Compared(counter, array, 1)
                        || Part(offsetGrid.ElementType, size, relative % size, memory, user, operandIndex) is not { } part)
                        continue;
                    return (array, offsetGrid, [new Immediate(0), counter], part.Field);
                }

            if (defs.Count != 2)
                return null;
            var step = defs.FirstOrDefault(d => d is { OpCode: OpCode.Add, Operands: [_, LocalVariable from, Immediate] }
                && ReferenceEquals(from, pointer));
            var start = defs.FirstOrDefault(d => !ReferenceEquals(d, step));
            if (step == null || start is not { OpCode: OpCode.Add, Operands: [_, var x, var y] })
                return null;
            foreach (var (dataStart, rowOffset) in new[] { (x, y), (y, x) })
            {
                if (Definition(dataStart) is not { OpCode: OpCode.Add, Operands: [_, var array, Immediate header] }
                    || header.Value != ElementsOffset(pointerSize) || GridType(array) is not { } grid)
                    continue;
                var size = SizeOf(grid.ElementType);
                if (size <= 0 || ((Immediate)step.Operands[2]).Value != size || memory.Addend < 0 || memory.Addend >= size)
                    continue;
                var row = ScaledIndex(rowOffset, size, definitions, 0) is { } flat && Factor(flat, array, 1) is { } scaled
                    ? Unextended(scaled)
                    : Definition(rowOffset) is { OpCode: OpCode.Multiply, Operands: [_, var m, var n] }
                      && (IsLength(m, array, 1) ? n : IsLength(n, array, 1) ? m : null) is LocalVariable s
                      && Induction(s) is { Start: 0 } sInduction && sInduction.Step == size
                        ? allDefinitions.Keys.FirstOrDefault(k => Induction(k) is { Start: 0, Step: 1 } kInduction
                            && CoInductive(kInduction, sInduction, start))
                        : null;
                if (row == null || row is not Immediate && !Compared(row, array, 0)
                    || row is LocalVariable rowLocal && ChangesBetween(rowLocal, start, user)
                    || Part(grid.ElementType, size, memory.Addend, memory, user, operandIndex) is not { } part)
                    continue;
                if (!columns.TryGetValue(pointer, out var column))
                {
                    columns[pointer] = column = NewLocal(int32);
                    InsertAfter(start, new Instruction(-1, OpCode.Move, column, new Immediate(0)));
                    InsertAfter(step, new Instruction(-1, OpCode.Add, column, column, new Immediate(1)));
                }
                return (array, grid, [row, column], part.Field);
            }
            return null;
        }

        // `x = c; …; x = x + step`, nothing else.
        (long Start, long Step, Instruction Init, Instruction Stepper)? Induction(LocalVariable local)
        {
            if (!allDefinitions.TryGetValue(local, out var defs) || defs.Count != 2)
                return null;
            var init = defs.FirstOrDefault(d => d is { OpCode: OpCode.Move, Operands: [_, Immediate] });
            var stepper = defs.FirstOrDefault(d => d is { OpCode: OpCode.Add, Operands: [_, LocalVariable from, Immediate] }
                && ReferenceEquals(from, local));
            return init == null || stepper == null
                ? null
                : (((Immediate)init.Operands[1]).Value, ((Immediate)stepper.Operands[2]).Value, init, stepper);
        }

        // Two counters move together at `use` when they start in one block and either step in one
        // block (`use` is not between the two steps), or neither steps before the first `use`,
        // every cycle through `use` steps each, and neither steps again without passing `use`.
        // Either way, wherever `use` runs both have stepped equally often.
        bool CoInductive((long Start, long Step, Instruction Init, Instruction Stepper) first,
            (long Start, long Step, Instruction Init, Instruction Stepper) second, Instruction use)
        {
            if (BlockOf(first.Init) != BlockOf(second.Init) || ReferenceEquals(first.Init, second.Init))
                return false;
            var steps = BlockOf(first.Stepper);
            if (steps == BlockOf(second.Stepper))
            {
                if (steps != BlockOf(use))
                    return true;
                var (a, b, u) = (steps.Instructions.IndexOf(first.Stepper), steps.Instructions.IndexOf(second.Stepper),
                    steps.Instructions.IndexOf(use));
                return u < System.Math.Min(a, b) || u > System.Math.Max(a, b);
            }
            return new[] { first.Stepper, second.Stepper }.All(stepper =>
                !Reaches(first.Init, stepper, use) && !Reaches(second.Init, stepper, use)
                && !Reaches(use, use, stepper) && !Reaches(stepper, stepper, use));
        }

        Block BlockOf(Instruction instruction) => cfg.Blocks.First(b => b.Instructions.Contains(instruction));

        void InsertAfter(Instruction anchor, Instruction inserted)
        {
            var owner = BlockOf(anchor);
            owner.Instructions.Insert(owner.Instructions.IndexOf(anchor) + 1, inserted);
            (allDefinitions.TryGetValue((LocalVariable)inserted.Destination!, out var list)
                ? list : allDefinitions[(LocalVariable)inserted.Destination!] = []).Add(inserted);
        }

        // Whether `local` can be written after `from` and before `to` on some path that does not
        // pass `from` again.
        bool ChangesBetween(LocalVariable local, Instruction from, Instruction to)
            => allDefinitions.TryGetValue(local, out var defs)
               && defs.Any(def => Reaches(from, def, from) && Reaches(def, to, from));

        bool Reaches(Instruction from, Instruction to, Instruction barrier)
        {
            var origin = BlockOf(from);
            var work = new Stack<(Block Block, int Index)>([(origin, origin.Instructions.IndexOf(from) + 1)]);
            var seen = new HashSet<Block>();
            while (work.Count > 0)
            {
                var (block, index) = work.Pop();
                var stopped = false;
                for (var k = index; k < block.Instructions.Count && !stopped; k++)
                {
                    if (ReferenceEquals(block.Instructions[k], to))
                        return true;
                    stopped = ReferenceEquals(block.Instructions[k], barrier);
                }
                if (stopped)
                    continue;
                foreach (var successor in block.Successors)
                    if (seen.Add(successor))
                        work.Push((successor, 0));
            }
            return false;
        }

        // Row-major: flat = (…(i·len1 + j)·len2 + k…). A dimension whose length never multiplies
        // in has index 0: the compiler folded 0·len away.
        // A struct passed whole to a call: the argument slot names its type.
        List<IOperand>? Indices(IOperand flat, int dimensions, IOperand array)
        {
            if (dimensions == 1)
                return [Unextended(flat)];
            var last = dimensions - 1;
            if (Definition(flat) is { OpCode: OpCode.Add, Operands: [_, var a, var b] })
                foreach (var (product, rest) in new[] { (a, b), (b, a) })
                    if (Factor(product, array, last) is { } outer && Indices(outer, last, array) is { } head)
                        return [.. head, Unextended(rest)];
            if (Factor(flat, array, last) is { } only && Indices(only, last, array) is { } leading)
                return [.. leading, new Immediate(0)];
            return [.. Enumerable.Repeat<IOperand>(new Immediate(0), last), Unextended(flat)];
        }

        // The outer index times the dimension's length; a bare length is outer index 1 (`grid[1, x]`
        // reads `len1 + x` with no multiply).
        IOperand? Factor(IOperand operand, IOperand array, int dimension)
            => Definition(operand) is { OpCode: OpCode.Multiply, Operands: [_, var a, var b] }
                ? IsLength(a, array, dimension) ? b : IsLength(b, array, dimension) ? a : null
                : IsLength(operand, array, dimension) ? new Immediate(1) : null;

        // A counter that starts at or above 0 and steps by 1 meets its length before it can pass it,
        // so clang checks it with `cmp len, i; b.eq` rather than an ordering.
        bool Compared(IOperand index, IOperand array, int dimension)
            => cfg.Instructions.Any(check => (check.OpCode is OpCode.CheckLess or OpCode.CheckGreater
                    or OpCode.CheckLessOrEqual or OpCode.CheckGreaterOrEqual
                    || check.OpCode == OpCode.CheckEqual && Unextended(index) is LocalVariable counter && CountsUp(counter))
                && check.Operands.Count == 3
                && (IsLength(check.Operands[1], array, dimension) && SameValue(check.Operands[2], index)
                    || IsLength(check.Operands[2], array, dimension) && SameValue(check.Operands[1], index)));

        // `i = s` with s >= 0, and `i = i + 1` directly or through a copy of `i + 1`; nothing else.
        bool CountsUp(LocalVariable local)
            => allDefinitions.TryGetValue(local, out var defs) && defs.Count == 2
               && defs.Any(d => d is { OpCode: OpCode.Move, Operands: [_, Immediate { Value: >= 0 }] })
               && defs.Any(d => (d is { OpCode: OpCode.Move, Operands: [_, LocalVariable copy] } ? Definition(copy) : d)
                   is { OpCode: OpCode.Add, Operands: [_, LocalVariable from, Immediate { Value: 1 }] }
                   && ReferenceEquals(from, local));

        Instruction? Definition(IOperand operand)
            => operand is LocalVariable local && definitions.TryGetValue(local, out var definition) ? definition : null;

        IOperand Unextended(IOperand index)
            => Definition(index) is { OpCode: OpCode.SignExtend32, Operands: [_, var original] } ? original : index;

        // Copies name the same value: `v = this.grid` and a later `this.grid` operand.
        bool SameValue(IOperand a, IOperand b)
        {
            a = Root(Unextended(a));
            b = Root(Unextended(b));
            return ReferenceEquals(a, b)
                || a is FieldReference fa && b is FieldReference fb && fa.Field == fb.Field
                   && fa.Containers.SequenceEqual(fb.Containers) && SameValue(fa.Local, fb.Local)
                || a is Immediate ia && b is Immediate ib && ia.Value == ib.Value;
        }

        IOperand Root(IOperand operand)
        {
            for (var depth = 0; depth < 8 && Definition(operand) is { OpCode: OpCode.Move, Operands: [_, var source] }
                                 && source is LocalVariable or FieldReference; depth++)
                operand = source;
            return operand;
        }

        static bool Mentions(IOperand operand, LocalVariable local) => operand switch
        {
            LocalVariable l => ReferenceEquals(l, local),
            MemoryOperand m => ReferenceEquals(m.Base, local) || ReferenceEquals(m.Index, local),
            _ => false,
        };

        LocalVariable NewLocal(TypeAnalysisContext type)
        {
            var local = new LocalVariable($"element{created}", new Register(null, $"ELEMENT{created++}"), type);
            method.Locals.Add(local);
            return local;
        }
    }

    // T[,]::Get/Set/Address: runtime methods of the array type, with no metadata row.
    // `new T[w, h]` stores the lengths into a stack buffer (`stp x8, x9, [sp]`) and calls a stub with
    // no metadata of its own: `mov x2, xzr; b NewFull`, i.e. `Array::NewFull(klass, lengths, null)`.
    // NewFull is where the exported `il2cpp_array_new_full` branches, so the stub is proven by its
    // body. Its lengths are the buffer's 8-byte cells, one per dimension of the class's array type.
    internal static void RecoverMultiDimensionalAllocations(MethodAnalysisContext method)
    {
        foreach (var block in method.ControlFlowGraph!.Blocks)
        for (var index = 0; index < block.Instructions.Count; index++)
        {
            var call = block.Instructions[index];
            if (call is not { OpCode: OpCode.Call, Operands: [Immediate target, LocalVariable result,
                    ArrayTypeAnalysisContext { Rank: > 1 } arrayType, AddressOf { Target: LocalVariable buffer }, ..] }
                || FrameStructFieldReads.FrameOffset(buffer) is not { } start
                || !IsArrayNewWithoutBounds(method.AppContext, target.UnsignedValue))
                continue;

            var stores = block.Instructions.Take(index)
                .Where(i => i is { OpCode: OpCode.Move, Operands: [LocalVariable cell, _] } && FrameStructFieldReads.FrameOffset(cell) != null)
                .ToList();
            var lengths = Enumerable.Range(0, arrayType.Rank).Select(dimension => Length(start + dimension * 8)).ToList();
            // The latest store covering the cell: an 8-byte length, or a constant vector whose
            // 64-bit halves are two lengths (`new int[20, 20]` is one `str q0` of {20, 20}).
            IOperand? Length(long cell)
            {
                for (var i = stores.Count - 1; i >= 0; i--)
                {
                    var at = FrameStructFieldReads.FrameOffset((LocalVariable)stores[i].Operands[0])!.Value;
                    if (at == cell)
                        return stores[i].Operands[1] is Vector128Literal vector ? VectorLength(vector, 0) : stores[i].Operands[1];
                    if (at == cell - 8 && stores[i].Operands[1] is Vector128Literal low)
                        return VectorLength(low, 1);
                }
                return null;
            }
            if (lengths.Any(length => length == null))
                continue;

            call.OpCode = OpCode.NewArr;
            call.SetOperands([result, arrayType, .. lengths!]);
            if (result.Type is not ArrayTypeAnalysisContext)
                result.Type = arrayType;
        }
    }

    // One 64-bit half of a constant vector, as a length.
    internal static Immediate? VectorLength(Vector128Literal vector, int half)
    {
        var (lo, hi) = half == 0 ? (vector.X, vector.Y) : (vector.Z, vector.W);
        var value = (long)(uint)BitConverter.SingleToInt32Bits(lo) | (long)(uint)BitConverter.SingleToInt32Bits(hi) << 32;
        return value is >= 0 and <= int.MaxValue ? new Immediate(value) : null;
    }

    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<ApplicationAnalysisContext,
        System.Collections.Concurrent.ConcurrentDictionary<ulong, bool>> ArrayNewStubs = new();

    internal static bool IsArrayNewWithoutBounds(ApplicationAnalysisContext app, ulong address)
        => ArrayNewStubs.GetOrCreateValue(app).GetOrAdd(address, _ =>
            app.InstructionSet is InstructionSets.NewArmV8InstructionSet
            && ProvesArrayNewWithoutBounds(app.Binary.GetVirtualAddressOfExportedFunctionByName("il2cpp_array_new_full"),
                address, at => ReadWord(app, at)));

    private static uint? ReadWord(ApplicationAnalysisContext app, ulong at)
    {
        var offset = app.Binary.MapVirtualAddressToRaw(at, false);
        return offset < 0 || offset > app.Binary.RawLength - 4 ? null
            : System.Buffers.Binary.BinaryPrimitives.ReadUInt32LittleEndian(app.Binary.GetRawBinaryContent().Slice((int)offset, 4));
    }

    // clang can keep a T[,]'s inline GetAt(i, j) out of line, as a function with no metadata. A call
    // to a copy its body proves (ProvesOutlinedGetter) whose receiver is a T[,] of that element size
    // is the array type's Get.
    internal static void RecoverOutlinedGetters(MethodAnalysisContext method)
    {
        var app = method.AppContext;
        if (app.InstructionSet is not InstructionSets.NewArmV8InstructionSet)
            return;
        foreach (var call in method.ControlFlowGraph!.Instructions)
            if (call is { OpCode: OpCode.Call, Operands: [Immediate target, LocalVariable result, var array, var i, var j, ..] }
                && array switch
                {
                    LocalVariable { Type: ArrayTypeAnalysisContext { Rank: 2 } local } => local,
                    FieldReference { Field.FieldType: ArrayTypeAnalysisContext { Rank: 2 } stored } => stored,
                    _ => null,
                } is { } arrayType
                && OutlinedGetters.GetOrCreateValue(app).GetOrAdd(target.UnsignedValue,
                    address => ProvesOutlinedGetter(address, at => ReadWord(app, at))) is { } size
                && size == (arrayType.ElementType.IsValueType && ElementSize(arrayType.ElementType, app.Binary.PointerSizeBytes) == 0
                    ? MetadataElementSize(arrayType.ElementType, app.Binary.PointerSizeBytes)
                    : ElementSize(arrayType.ElementType, app.Binary.PointerSizeBytes)))
                call.SetOperands([Accessor(arrayType, "Get"), result, array, i, j]);
    }

    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<ApplicationAnalysisContext,
        System.Collections.Concurrent.ConcurrentDictionary<ulong, long?>> OutlinedGetters = new();

    // GetAt(array, i, j) of a T[,] whose elements are 2^s bytes, returned in registers:
    //   str x30, [sp, #-0x10]!; ldr x8, [x0, #0x10]; ldr w9, [x8]; cmp w1, w9; b.hs fail
    //   ldr x8, [x8, #0x10]; cmp w2, w8; b.hs fail; madd x8, x8, x1, x2; add x8, x0, x8, lsl #s
    //   ldr|ldp <element>, [x8, #0x20]; ldr x30, [sp], #0x10; ret; fail: bl <throw>
    // Returns the element size the load reads, which is 2^s.
    internal static long? ProvesOutlinedGetter(ulong address, Func<ulong, uint?> read)
    {
        uint?[] expected = [0xf81f0ffe, 0xf9400808, 0xb9400109, 0x6b09003f, null, 0xf9400908, 0x6b08005f, null, 0x9b010908];
        for (var k = 0; k < expected.Length; k++)
            if (read(address + 4 * (ulong)k) is not { } word || expected[k] is { } exact && word != exact)
                return null;
        var fail = address + 13 * 4;
        foreach (var check in new ulong[] { 4, 7 })
            if (read(address + 4 * check) is not { } branch || (branch & 0xff00001f) != 0x54000002
                || address + 4 * check + (ulong)(((int)(branch << 8) >> 13) * 4) != fail)
                return null;
        if (read(address + 9 * 4) is not { } add || (add & 0xffff03ff) != 0x8b080008
            || read(address + 11 * 4) != 0xf84107fe || read(address + 12 * 4) != 0xd65f03c0
            || read(fail) is not { } call || (call & 0xfc000000) != 0x94000000)
            return null;
        long width = read(address + 10 * 4) switch
        {
            0x39408100 => 1, // ldrb w0
            0x79404100 => 2, // ldrh w0
            0xb9402100 or 0xbd402100 => 4, // ldr w0 / s0
            0xf9401100 or 0xfd401100 => 8, // ldr x0 / d0
            0xa9420500 => 16, // ldp x0, x1
            _ => 0,
        };
        return width != 0 && width == 1L << (int)((add >> 10) & 0x3f) ? width : null;
    }

    // The exported `il2cpp_array_new_full` is one branch to NewFull; the stub passes no lower bounds
    // (`mov x2, xzr`) and branches to that same NewFull.
    internal static bool ProvesArrayNewWithoutBounds(ulong export, ulong address, Func<ulong, uint?> read)
        => export != 0
           && read(export) is { } exportJump && (exportJump & 0xfc000000) == 0x14000000
           && read(address) == 0xaa1f03e2
           && read(address + 4) is { } jump && (jump & 0xfc000000) == 0x14000000
           && NonReturningHelperRecovery.BranchTarget(address + 4, jump)
              == NonReturningHelperRecovery.BranchTarget(export, exportJump);

    private static InjectedMethodAnalysisContext Accessor(ArrayTypeAnalysisContext arrayType, string name)
    {
        var app = arrayType.AppContext;
        var indices = Enumerable.Repeat(app.SystemTypes.SystemInt32Type, arrayType.Rank).ToArray();
        return name switch
        {
            "Get" => new(arrayType, name, arrayType.ElementType, System.Reflection.MethodAttributes.Public, indices),
            "Set" => new(arrayType, name, app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Public,
                [.. indices, arrayType.ElementType]),
            _ => new(arrayType, name, new ByRefTypeAnalysisContext(arrayType.ElementType),
                System.Reflection.MethodAttributes.Public, indices),
        };
    }

    // Clang initializes struct arrays in 16-byte chunks: it takes &stackLocal, then copies
    // [local+N] into [arrayHeader+index*stride+N]. Managed IL has no partial struct store;
    // when the first chunk names a complete typed stack local, restore the one honest
    // operation (array[index] = local) and discard the remaining chunks for that element.
    private static void RecoverStructArrayBulkCopies(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        Dictionary<LocalVariable, Instruction?>? definitions = null;
        foreach (var instruction in cfg.Instructions.ToList())
        {
            if (instruction is not { OpCode: OpCode.Move,
                    Operands: [MemoryOperand { Base: LocalVariable { Type: SzArrayTypeAnalysisContext arrayType } array,
                        Index: null, Scale: 0, Addend: var destinationOffset }, var source] }
                || !arrayType.ElementType.IsValueType)
                continue;

            var stride = MetadataElementSize(arrayType.ElementType, pointerSize);
            var relative = destinationOffset - ElementsOffset(pointerSize);
            if (stride <= 0 || relative < 0 || relative % stride != 0
                || (source is LocalVariable direct && direct.Type?.FullName == arrayType.ElementType.FullName
                    ? direct
                    : source is MemoryOperand sourceMemory
                        ? ResolveStackAlias(sourceMemory, method, cfg, instruction, arrayType.ElementType)
                        : null) is not { } value
                || value.Type?.FullName != arrayType.ElementType.FullName)
                continue;

            var elementStart = destinationOffset;
            var elementEnd = elementStart + stride;
            instruction.SetOperands(new ArrayAccess(array, new Immediate(relative / stride)), value);

            // Drop the copy's remaining piece stores: instructions beside the anchor in
            // the same block that write another slice of the same element from the same
            // slice of the stored value. A same-span store whose source is not provably
            // [value + offset] is a real write (e.g. arr[i].field = x beside arr[i] = v)
            // and ends the contiguous piece run.
            var block = cfg.Blocks.FirstOrDefault(b => b.Instructions.Contains(instruction));
            if (block == null)
                continue;
            definitions ??= SingleDefinitions(cfg);
            var anchor = block.Instructions.IndexOf(instruction);
            for (var step = -1; step <= 1; step += 2)
            for (var i = anchor + step; i >= 0 && i < block.Instructions.Count; i += step)
            {
                var chunk = block.Instructions[i];
                if (chunk is not { OpCode: OpCode.Move,
                        Operands: [MemoryOperand { Base: LocalVariable chunkArray,
                            Index: null, Scale: 0, Addend: var chunkOffset }, var chunkSource] }
                    || !ReferenceEquals(chunkArray, array)
                    || chunkOffset < elementStart || chunkOffset >= elementEnd)
                    continue;
                if (!IsSameValueSlice(chunkSource, value, chunkOffset - elementStart, definitions))
                    break;
                MakeNop(chunk);
            }
        }

    }

    // Whether `source` provably reads the `sliceOffset`-byte slice of `value` —
    // [value + sliceOffset] directly or through single-definition Move chains, or
    // through the same &stack alias ResolveStackAlias resolves a stack local from.
    private static bool IsSameValueSlice(IOperand source, LocalVariable value, long sliceOffset,
        Dictionary<LocalVariable, Instruction?> definitions)
    {
        var seen = new HashSet<LocalVariable>();
        while (source is LocalVariable local && seen.Add(local)
                && definitions.TryGetValue(local, out var definition)
                && definition is { OpCode: OpCode.Move, Operands: [_, { } next] })
            source = next;

        if (source is not MemoryOperand { Base: LocalVariable sliceBase, Index: null, Scale: 0,
                Addend: var addend })
            return false;

        if (ReferenceEquals(sliceBase, value))
            return addend == sliceOffset;

        return definitions.TryGetValue(sliceBase, out var pointerDefinition)
            && pointerDefinition is { OpCode: OpCode.Move,
                Operands: [_, AddressOf { Target: LocalVariable origin }] }
            && ((ReferenceEquals(origin, value) && addend == sliceOffset)
                || (StackOffset(origin.Register.Name) is { } originOffset
                    && StackOffset(value.Register.Name) is { } valueOffset
                    && originOffset + addend == valueOffset + sliceOffset));
    }

    private static LocalVariable? ResolveStackAlias(MemoryOperand memory, MethodAnalysisContext method,
        ISILControlFlowGraph cfg, Instruction before, TypeAnalysisContext expectedType)
    {
        if (memory is not { Base: LocalVariable pointer, Index: null, Scale: 0 }
            || cfg.Instructions.TakeWhile(instruction => !ReferenceEquals(instruction, before))
                .LastOrDefault(instruction => ReferenceEquals(instruction.Destination, pointer)) is not { } definition
            || definition is not { OpCode: OpCode.Move,
                Operands: [_, AddressOf { Target: LocalVariable origin }] }
            || StackOffset(origin.Register.Name) is not { } originOffset)
            return null;

        var targetOffset = originOffset + memory.Addend;
        return method.Locals.FirstOrDefault(local => StackOffset(local.Register.Name) == targetOffset
            && local.Type?.FullName == expectedType.FullName);
    }

    private static long? StackOffset(string name)
    {
        if (!name.StartsWith("stack_", StringComparison.Ordinal))
            return null;
        var text = name[6..];
        var negative = text.StartsWith('-');
        if (negative)
            text = text[1..];
        return long.TryParse(text, System.Globalization.NumberStyles.HexNumber, null, out var value)
            ? negative ? -value : value
            : null;
    }

    // IL2CPP passes value-type fields by address as `object + fieldOffset`.
    // Rebind that native address to the managed field even when register typing
    // guessed the destination as the field value itself.
    internal static void RecoverObjectFieldAddresses(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        foreach (var instruction in cfg.Instructions.ToList())
        {
            if (instruction is not { OpCode: OpCode.Add or OpCode.Or,
                    Operands: [LocalVariable destination, LocalVariable owner, Immediate offset] }
                || owner.Type is not { IsValueType: false } ownerType
                )
                continue;

            var accessSize = destination.Type is { } destinationType
                ? (int)TypeSizes.MinimumUnboxedSize(destinationType, method.AppContext.Binary.PointerSizeBytes)
                : 0;
            if (MetadataResolver.FindInstanceFieldPathAtOffset(ownerType, offset.Value, accessSize) is not { } addressed)
                continue;

            var changed = false;
            foreach (var use in cfg.Instructions)
            {
                if (ReferenceEquals(use, instruction))
                    continue;
                for (var i = 0; i < use.Operands.Count; i++)
                {
                    if (ReferenceEquals(use.Operands[i], destination))
                    {
                        use.SetOperand(i, new AddressOf(new FieldReference(addressed.Field, owner,
                            (int)offset.Value, addressed.Containers, accessSize)));
                        changed = true;
                    }
                    else if (use.Operands[i] is MemoryOperand
                        { Base: LocalVariable memoryBase, Index: null, Scale: 0 } memory
                        && ReferenceEquals(memoryBase, destination)
                        && MetadataResolver.FindInstanceFieldPathAtOffset(ownerType,
                            offset.Value + memory.Addend, memory.AccessSize) is { } loaded)
                    {
                        use.SetOperand(i, new FieldReference(loaded.Field, owner,
                            (int)(offset.Value + memory.Addend), loaded.Containers, memory.AccessSize));
                        changed = true;
                    }
                }
            }
            if (changed)
                MakeNop(instruction);
        }
    }

    private static void RecoverFieldAddressAliases(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        foreach (var definition in cfg.Instructions.ToList())
        {
            if (definition is not { OpCode: OpCode.Move,
                    Operands: [LocalVariable alias, AddressOf { Target: FieldReference field }] }
                || cfg.Instructions.Count(instruction => ReferenceEquals(instruction.Destination, alias)) != 1)
                continue;

            var changed = false;
            foreach (var use in cfg.Instructions)
            for (var i = 0; i < use.Operands.Count; i++)
            {
                if (ReferenceEquals(use.Operands[i], alias))
                {
                    use.SetOperand(i, new AddressOf(field));
                    changed = true;
                }
                else if (use.Operands[i] is MemoryOperand
                         { Base: LocalVariable memoryBase, Index: null, Scale: 0, Addend: 0 }
                         && ReferenceEquals(memoryBase, alias))
                {
                    use.SetOperand(i, field);
                    changed = true;
                }
            }

            if (changed)
                MakeNop(definition);
        }
    }

    // ARM64 often keeps both the managed index (0, 1, 2...) and the native byte
    // offset (array header, then += pointer size). Rebind [array + byteOffset] to
    // array[index]; initlocals supplies the missing zero move when XZR lifting was
    // elided from the prologue.
    private static void RecoverReferenceArrayOffsetWalkers(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;

        foreach (var instruction in cfg.Instructions)
            for (var operandIndex = 0; operandIndex < instruction.Operands.Count; operandIndex++)
            {
                if (instruction.Operands[operandIndex] is not MemoryOperand
                    {
                        Base: LocalVariable { Type: SzArrayTypeAnalysisContext arrayType } array,
                        Index: LocalVariable offset,
                        Addend: 0,
                        Scale: 0 or 1
                    }
                    || arrayType.ElementType.IsValueType
                    || !HasInduction(cfg, offset, ElementsOffset(pointerSize), pointerSize)
                    || FindImplicitZeroArrayIndex(method, array) is not { } index)
                    continue;

                instruction.SetOperand(operandIndex, new ArrayAccess(array, index));
            }
    }

    private static bool HasInduction(ISILControlFlowGraph cfg, LocalVariable local, long start, long step) =>
        cfg.Instructions.Any(instruction => instruction is
            { OpCode: OpCode.Move, Operands: [LocalVariable destination, Immediate initial] }
            && ReferenceEquals(destination, local) && initial.Value == start)
        && cfg.Instructions.Any(instruction => instruction is
            { OpCode: OpCode.Add, Operands: [LocalVariable destination, LocalVariable source, Immediate increment] }
            && ReferenceEquals(destination, local) && ReferenceEquals(source, local) && increment.Value == step);

    private static LocalVariable? FindImplicitZeroArrayIndex(MethodAnalysisContext method, LocalVariable array)
    {
        var cfg = method.ControlFlowGraph!;
        var candidates = cfg.Instructions
            .Where(instruction => instruction.OpCode is >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual
                && instruction.Operands.Skip(1).OfType<ArrayLength>().Any(length => ReferenceEquals(length.Array, array)))
            .SelectMany(instruction => instruction.Operands.Skip(1).OfType<LocalVariable>())
            .Distinct()
            .Where(candidate => !method.ParameterLocals.Contains(candidate)
                && cfg.Instructions.Any(instruction => instruction is
                    { OpCode: OpCode.Add, Operands: [LocalVariable destination, LocalVariable source, Immediate { Value: 1 }] }
                    && ReferenceEquals(destination, candidate) && ReferenceEquals(source, candidate)))
            .Where(candidate => cfg.Instructions
                .Where(instruction => ReferenceEquals(instruction.Destination, candidate))
                .All(instruction => instruction is
                    { OpCode: OpCode.Add, Operands: [LocalVariable destination, LocalVariable source, Immediate { Value: 1 }] }
                        && ReferenceEquals(destination, candidate) && ReferenceEquals(source, candidate)
                    || instruction is { OpCode: OpCode.Move, Operands: [LocalVariable zeroDestination, Immediate { Value: 0 }] }
                        && ReferenceEquals(zeroDestination, candidate)))
            .ToList();
        return candidates.Count == 1 ? candidates[0] : null;
    }

    // IL2CPP walks arrays of structs with a native pointer plus the managed loop index. Rebind the
    // pointer to array[index].field so the pointer increments disappear from managed IL.
    private static void RecoverStructPointerWalkers(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;

        foreach (var initial in cfg.Instructions.ToList())
        {
            if (initial is not { OpCode: OpCode.Add, Operands: [LocalVariable pointer,
                    LocalVariable { Type: SzArrayTypeAnalysisContext arrayType } array, Immediate start] }
                || !arrayType.ElementType.IsValueType
                || FindValueTypeField(arrayType.ElementType, start.Value - ElementsOffset(pointerSize)) is not { } initialField
                || FindArrayIndex(cfg, array) is not { } index)
                continue;

            var stride = MetadataElementSize(arrayType.ElementType, pointerSize);
            if (stride <= 0)
                continue;

            var increments = cfg.Instructions.Where(i => i is
            {
                OpCode: OpCode.Add,
                Operands: [LocalVariable destination, LocalVariable source, Immediate { Value: var amount }]
            } && ReferenceEquals(destination, pointer) && ReferenceEquals(source, pointer) && amount == stride).ToHashSet();

            // First collapse pointers derived from the walker (for example `&element.time + 4`).
            foreach (var derived in cfg.Instructions.ToList())
            {
                if (ReferenceEquals(derived, initial) || increments.Contains(derived)
                    || derived is not { OpCode: OpCode.Add or OpCode.Or,
                        Operands: [LocalVariable destination, LocalVariable source, Immediate delta] }
                    || !ReferenceEquals(source, pointer)
                    || FindValueTypeField(arrayType.ElementType,
                        start.Value - ElementsOffset(pointerSize) + delta.Value) is not { } field)
                    continue;

                ReplaceLocalUses(cfg, destination,
                    new AddressOf(new ArrayElementFieldReference(array, index, field)), derived);
                MakeNop(derived);
            }

            foreach (var instruction in cfg.Instructions.ToList())
            {
                if (ReferenceEquals(instruction, initial) || increments.Contains(instruction))
                    continue;

                for (var operandIndex = 0; operandIndex < instruction.Operands.Count; operandIndex++)
                {
                    var operand = instruction.Operands[operandIndex];
                    if (ReferenceEquals(operand, pointer))
                    {
                        instruction.SetOperand(operandIndex,
                            new AddressOf(new ArrayElementFieldReference(array, index, initialField)));
                        continue;
                    }

                    if (operand is MemoryOperand { Base: LocalVariable memoryBase, Index: null, Scale: 0 } memory
                        && ReferenceEquals(memoryBase, pointer)
                        && FindValueTypeField(arrayType.ElementType,
                            start.Value - ElementsOffset(pointerSize) + memory.Addend) is { } field)
                    {
                        instruction.SetOperand(operandIndex, new ArrayElementFieldReference(array, index, field));
                        if (instruction.Destination is LocalVariable destination)
                        {
                            destination.Type = field.FieldType;
                            CanonicalizeAddressTakes(cfg, destination);
                        }
                    }
                }
            }

            MakeNop(initial);
            foreach (var increment in increments)
                MakeNop(increment);
        }
    }

    // AArch64 commonly materializes addresses of later fields with ADD/OR from `&local`.
    private static void RecoverValueTypeFieldAddresses(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var addressed = new HashSet<LocalVariable>();

        foreach (var instruction in cfg.Instructions.ToList())
        {
            if (instruction is not { OpCode: OpCode.Add or OpCode.Or,
                    Operands: [LocalVariable destination, AddressOf { Target: LocalVariable owner }, Immediate offset] }
                || owner.Type is not { IsValueType: true } ownerType
                || FindValueTypeField(ownerType, offset.Value) is not { } field)
                continue;

            addressed.Add(owner);
            ReplaceLocalUses(cfg, destination, new AddressOf(new FieldReference(field, owner, (int)offset.Value)), instruction);
            MakeNop(instruction);
        }

        foreach (var owner in addressed)
        {
            if (owner.Type is not { } ownerType || FindValueTypeField(ownerType, 0) is not { } firstField)
                continue;
            foreach (var instruction in cfg.Instructions)
                for (var i = 0; i < instruction.Operands.Count; i++)
                    if (instruction.Operands[i] is AddressOf { Target: LocalVariable direct }
                        && ReferenceEquals(direct, owner))
                        instruction.SetOperand(i, new AddressOf(new FieldReference(firstField, owner, 0)));
        }
    }

    private static LocalVariable? FindArrayIndex(ISILControlFlowGraph cfg, LocalVariable array)
    {
        var candidates = cfg.Instructions.SelectMany(i => i.Operands)
            .OfType<ArrayLength>().Where(length => ReferenceEquals(length.Array, array))
            .SelectMany(length => cfg.Instructions.Where(i => i.Operands.Contains(length)))
            .SelectMany(i => i.Operands.OfType<LocalVariable>()).Distinct()
            .Where(candidate => cfg.Instructions.Any(i => i is
                { OpCode: OpCode.Move, Operands: [LocalVariable destination, Immediate { Value: 0 }] }
                && ReferenceEquals(destination, candidate))
                && cfg.Instructions.Any(i => i is
                { OpCode: OpCode.Add, Operands: [LocalVariable destination, LocalVariable source, Immediate { Value: 1 }] }
                && ReferenceEquals(destination, candidate) && ReferenceEquals(source, candidate)))
            .ToList();
        return candidates.Count == 1 ? candidates[0] : null;
    }

    private static FieldAnalysisContext? FindValueTypeField(TypeAnalysisContext type, long unboxedOffset) =>
        type.Fields.FirstOrDefault(field => !field.IsStatic
            && (field.BackingData?.FieldOffset ?? field.Offset) == unboxedOffset);

    private static void ReplaceLocalUses(ISILControlFlowGraph cfg, LocalVariable local, IOperand replacement,
        Instruction definition)
    {
        foreach (var instruction in cfg.Instructions)
        {
            if (ReferenceEquals(instruction, definition))
                continue;
            for (var i = 0; i < instruction.Operands.Count; i++)
                if (ReferenceEquals(instruction.Operands[i], local))
                    instruction.SetOperand(i, replacement);
        }
    }

    private static void CanonicalizeAddressTakes(ISILControlFlowGraph cfg, LocalVariable canonical)
    {
        foreach (var instruction in cfg.Instructions)
            for (var i = 0; i < instruction.Operands.Count; i++)
                if (instruction.Operands[i] is AddressOf { Target: LocalVariable alias } address
                    && alias.Register.Equals(canonical.Register))
                {
                    address.Target = canonical;
                    instruction.SetOperand(i, address);
                }
    }

    private static void MakeNop(Instruction instruction)
    {
        instruction.OpCode = OpCode.Nop;
        instruction.SetOperands();
    }

    // Whether RecoverAccesses would resolve this operand into an ArrayLength or
    // ArrayAccess for the given array type. Alias normalization folds displaced
    // bases onto the array through this same predicate, so the full instruction
    // context - sibling agreement and the lifted-lea discipline - applies: a
    // fold must never strand an operand RecoverAccesses will then refuse.
    internal static bool ResolvesAccess(MemoryOperand memory, SzArrayTypeAnalysisContext arrayType, int pointerSize,
        MethodAnalysisContext method, Instruction instruction, int operandIndex,
        Func<Dictionary<LocalVariable, List<(Instruction Instruction, int OperandIndex)>>> uses)
    {
        if (memory.Index == null && memory.Scale == 0 && memory.Addend == LengthOffset(pointerSize))
            return true;

        if (ElementIndex(memory, arrayType, pointerSize) != null)
            return true;

        return ResolveStructElementAccess(instruction, operandIndex, memory, arrayType, pointerSize,
            uses) != null;
    }

    internal static void RecoverAccesses(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var definitions = SingleDefinitions(method.ControlFlowGraph!);
        Dictionary<LocalVariable, List<(Instruction Instruction, int OperandIndex)>>? uses = null;
        var guardContext = new GuardedIndexContext(method);
        var lengthWordBases = new List<LocalVariable>();

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            RecoverAllocation(instruction);

            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                if (instruction.Operands[i] is not MemoryOperand memory)
                    continue;

                var array = memory.Base switch
                {
                    LocalVariable { Type: SzArrayTypeAnalysisContext } typedBase => typedBase,
                    { } baseOperand => ResolveArray(baseOperand, definitions, 0),
                    _ => null,
                };
                if (array?.Type is not SzArrayTypeAnalysisContext arrayType)
                {
                    if (DerivedElementAccess(memory, pointerSize, definitions, instruction, i) is { } derived)
                        instruction.SetOperand(i, derived);
                    else if (GuardedIndexAccess(method, instruction, i, memory, pointerSize, definitions,
                                 () => uses ??= CollectUses(method.ControlFlowGraph!), guardContext) is { } guardedDerived)
                        instruction.SetOperand(i, guardedDerived);
                    else if (LengthWordLoad(instruction, i, memory, pointerSize, definitions) is { } lengthArray)
                    {
                        instruction.SetOperand(i, new ArrayLength(lengthArray));
                        if (memory.Base is LocalVariable lengthWordBase)
                            lengthWordBases.Add(lengthWordBase);
                    }
                    continue;
                }

                if (memory.Index == null && memory.Scale == 0 && memory.Addend == LengthOffset(pointerSize))
                {
                    instruction.SetOperand(i, new ArrayLength(array));
                    continue;
                }

                if (ElementIndex(memory, arrayType, pointerSize) is { } index)
                {
                    instruction.SetOperand(i, new ArrayAccess(array, index));
                    continue;
                }

                if (ResolveStructElementAccess(instruction, i, memory, arrayType, pointerSize,
                        () => uses ??= CollectUses(method.ControlFlowGraph!)) is { } access)
                    instruction.SetOperand(i, access.Field is { } elementField
                        ? new ArrayElementFieldReference(array, access.Index, elementField)
                        : new ArrayAccess(array, access.Index));
                else if (GuardedIndexAccess(method, instruction, i, memory, pointerSize, definitions,
                             () => uses ??= CollectUses(method.ControlFlowGraph!), guardContext) is { } guarded)
                    instruction.SetOperand(i, guarded);
            }
        }

        DropDeadHeaderAddresses(method.ControlFlowGraph!, lengthWordBases, definitions);
    }

    // A length-word load folded into ldlen no longer reads the `array + K` header
    // address it went through. Address arithmetic on a managed reference has no IL
    // spelling, so a chain link nothing reads any more is dropped with the load
    // that needed it - walking back from the folded base through the same
    // Move/Add/Subtract links LengthWordLoad proved - instead of reaching
    // emission as a value. A link still read elsewhere stays.
    private static void DropDeadHeaderAddresses(ISILControlFlowGraph cfg, List<LocalVariable> bases,
        Dictionary<LocalVariable, Instruction?> definitions)
    {
        if (bases.Count == 0)
            return;
        var reads = new Dictionary<LocalVariable, int>();
        foreach (var instruction in cfg.Instructions)
            foreach (var used in DeadCodeEliminator.UsedLocals(instruction))
                reads[used] = reads.GetValueOrDefault(used) + 1;
        var work = new Stack<LocalVariable>(bases);
        while (work.Count > 0)
        {
            var local = work.Pop();
            if (local.Type is SzArrayTypeAnalysisContext || reads.GetValueOrDefault(local) != 0
                || !definitions.TryGetValue(local, out var definition)
                || definition is not { OpCode: OpCode.Move or OpCode.Add or OpCode.Subtract }
                || definition is { OpCode: OpCode.Move, Operands: [_, MemoryOperand] }
                || EvaluateHeaderBase(local, definitions, 0) is not
                    { Root: LocalVariable { Type: SzArrayTypeAnalysisContext }, Multiplier: 1 })
                continue;
            var sources = DeadCodeEliminator.UsedLocals(definition).ToList();
            MakeNop(definition);
            definitions[local] = null;
            foreach (var source in sources)
            {
                reads[source]--;
                work.Push(source);
            }
        }
    }

    // The parameter type a call operand fills, when the operand is a resolved call's argument.
    private static TypeAnalysisContext? ArgumentType(Instruction call, int operandIndex)
    {
        if (call.Operands[0] is not MethodAnalysisContext target || !call.IsCall)
            return null;
        var parameter = operandIndex - (call.OpCode == OpCode.Call ? 2 : 1) - (target.IsStatic ? 0 : 1);
        return parameter >= 0 && parameter < target.Parameters.Count ? target.Parameters[parameter].ParameterType : null;
    }

    private static ArrayAccess? DerivedElementAccess(MemoryOperand memory, int pointerSize,
        Dictionary<LocalVariable, Instruction?> definitions, Instruction user, int operandIndex)
    {
        if (memory is not { Base: LocalVariable pointer, Index: null, Scale: 0 }
            || memory.Addend != ElementsOffset(pointerSize)
            || !definitions.TryGetValue(pointer, out var definition)
            || definition is not { OpCode: OpCode.Add, Operands: [_, var left, var right] })
            return null;

        return Match(left, right) ?? Match(right, left);

        ArrayAccess? Match(IOperand possibleArray, IOperand possibleIndex)
        {
            if (ResolveArray(possibleArray, definitions, 0) is not { } array)
                return null;

            var elementType = ((SzArrayTypeAnalysisContext)array.Type!).ElementType;
            var structElement = elementType.IsValueType && ElementSize(elementType, pointerSize) == 0;
            var elementSize = structElement ? MetadataElementSize(elementType, pointerSize) : ElementSize(elementType, pointerSize);
            // A struct element is the whole element only when the access covers it, or the operand
            // fills a parameter of the element type (`ldp x0, x1` of a 16-byte element passed by value).
            if (structElement && !(memory.AccessSize == 0 || memory.AccessSize >= elementSize
                                   || ArgumentType(user, operandIndex)?.FullName == elementType.FullName))
                return null;
            return elementSize > 0 && ScaledIndex(possibleIndex, elementSize, definitions, 0) is { } index
                ? new ArrayAccess(array, index)
                : null;
        }
    }

    private static LocalVariable? ResolveArray(IOperand operand,
        Dictionary<LocalVariable, Instruction?> definitions, int depth)
    {
        // Copy forwarding can leave an element address built from a re-read of the field the
        // array was loaded from (`add x8, x8, i lsl 4` after `ldr x8, [this, #0x58]` reads as
        // `this.items + i·16`). The native base is the local that load went into: when exactly one
        // local holds that field read, it is the array.
        if (depth <= 8 && operand is FieldReference { Containers.Count: 0, Field.FieldType: SzArrayTypeAnalysisContext } read)
            return FieldReadLocals.GetValue(definitions, Collect).TryGetValue((read.Field, read.Local, read.Offset), out var holder)
                ? holder
                : null;
        if (depth > 8 || operand is not LocalVariable local)
            return null;
        if (local.Type is SzArrayTypeAnalysisContext)
            return local;
        return definitions.TryGetValue(local, out var definition)
            && definition is { OpCode: OpCode.Move, Operands: [_, var source] }
                ? ResolveArray(source, definitions, depth + 1)
                : null;
    }

    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<Dictionary<LocalVariable, Instruction?>,
        Dictionary<(FieldAnalysisContext, LocalVariable?, int), LocalVariable?>> FieldReadLocals = new();

    // Each direct field read held by exactly one local; a read two locals hold maps to null.
    private static Dictionary<(FieldAnalysisContext, LocalVariable?, int), LocalVariable?> Collect(
        Dictionary<LocalVariable, Instruction?> definitions)
    {
        var holders = new Dictionary<(FieldAnalysisContext, LocalVariable?, int), LocalVariable?>();
        foreach (var (local, definition) in definitions)
            if (local.Type is SzArrayTypeAnalysisContext
                && definition is { OpCode: OpCode.Move, Operands: [_, FieldReference { Containers.Count: 0 } read] })
            {
                var key = (read.Field, read.Local, read.Offset);
                holders[key] = holders.ContainsKey(key) ? null : local;
            }
        return holders;
    }

    // A read of the array header's length word through an address chain: the
    // binary materializes `array + 0x18` into its own local and dereferences
    // `[p]` or `[p + k]`, so the base resolves to the array only when the
    // touched word lands exactly on max_length. Only load positions qualify -
    // writing the word has no ldlen spelling and keeps its store diagnostic.
    private static LocalVariable? LengthWordLoad(
        Instruction instruction, int operandIndex, MemoryOperand memory, int pointerSize,
        Dictionary<LocalVariable, Instruction?> definitions)
    {
        if (memory.Index != null || memory.Scale != 0 || IsStorePosition(instruction, operandIndex)
            || EvaluateHeaderBase(memory.Base, definitions, 0) is not
                { Root: LocalVariable { Type: SzArrayTypeAnalysisContext } array, Multiplier: 1 } headerBase
            || headerBase.Offset + memory.Addend != LengthOffset(pointerSize))
            return null;
        return array;
    }

    private static bool IsStorePosition(Instruction instruction, int operandIndex) =>
        operandIndex == 0 && instruction.OpCode
            is OpCode.Move or OpCode.MemoryCopy or OpCode.MemorySet or OpCode.MemoryMove;

    // The base address as `root + constant` through definition chains that are
    // provably address arithmetic: `Move` copies and `Add`/`Subtract` immediates.
    // A `Move` from a MemoryOperand is a real load - the value is the word that
    // was read (e.g. the class pointer), not the address it came from - so it
    // makes the local an opaque root rather than `array + 0`. A local typed as
    // the array proves itself; anything else is an opaque root the caller's
    // array-type test rejects.
    private static Affine? EvaluateHeaderBase(IOperand? operand,
        Dictionary<LocalVariable, Instruction?> definitions, int depth)
    {
        if (depth > 8)
            return null;

        switch (operand)
        {
            case null:
                return null;
            case Immediate { Value: var value }:
                return new Affine(null, 0, value);
            case LocalVariable { Type: SzArrayTypeAnalysisContext } array:
                return new Affine(array, 1, 0);
            case LocalVariable local:
                if (!definitions.TryGetValue(local, out var definition) || definition == null)
                    return new Affine(local, 1, 0);
                return definition switch
                {
                    { OpCode: OpCode.Move, Operands: [_, var source] } when source is not MemoryOperand
                        => EvaluateHeaderBase(source, definitions, depth + 1),
                    { OpCode: OpCode.Add or OpCode.Subtract, Operands: [_, var left, var right] }
                        => Sum(EvaluateHeaderBase(left, definitions, depth + 1),
                               ScaleBy(EvaluateHeaderBase(right, definitions, depth + 1),
                                   definition.OpCode is OpCode.Subtract ? -1 : 1)),
                    _ => new Affine(local, 1, 0),
                };
            default:
                return null;
        }
    }

    // Element accesses where the element-region offset is folded into the base
    // local: the binary materializes `array + elementsOffset` once, then
    // dereferences `[p + i * stride + off]` (or `[p + i + off]` when the index is
    // already in bytes). Solve the base and index as affine expressions, fold
    // the constants into an element index plus a field offset, and only rewrite
    // when a bounds check for the same array proves the index - the conditional
    // jump fed by a `CheckLess` against the array's length must dominate the
    // access on its in-bounds edge. Anything else stays diagnosed.
    private static IOperand? GuardedIndexAccess(
        MethodAnalysisContext method,
        Instruction instruction,
        int operandIndex,
        MemoryOperand memory,
        int pointerSize,
        Dictionary<LocalVariable, Instruction?> definitions,
        Func<Dictionary<LocalVariable, List<(Instruction Instruction, int OperandIndex)>>> uses,
        GuardedIndexContext context)
    {
        // Only positions that consume an element value or store one may be
        // rewritten: a MemoryOperand inside integer or address arithmetic is
        // an element address, not an element, and stays diagnosed.
        if (memory.Index == null || method.DominatorInfo == null
            || instruction.OpCode is not (OpCode.Move
                or OpCode.Call or OpCode.CallVoid or OpCode.IndirectCall
                or OpCode.CheckEqual or OpCode.CheckNotEqual
                or OpCode.CheckLess or OpCode.CheckGreater
                or OpCode.CheckLessOrEqual or OpCode.CheckGreaterOrEqual
                or OpCode.Return or OpCode.Throw))
        {
            return null;
        }

        var baseAffine = Evaluate(memory.Base, definitions, 0, true);
        if (baseAffine is { Root: LocalVariable { Type: SzArrayTypeAnalysisContext rootedType } root, Multiplier: 1 })
        {
            return GuardedIndexAccess(method, instruction, operandIndex, memory, pointerSize,
                definitions, uses, context, root, rootedType, baseAffine.Value);
        }
        if (memory.Base is LocalVariable { Type: SzArrayTypeAnalysisContext baseType } typedBase)
        {
            // The typed base is itself the array (e.g. a field load the affine
            // evaluator cannot follow); its own value is the root.
            return GuardedIndexAccess(method, instruction, operandIndex, memory, pointerSize,
                definitions, uses, context, typedBase, baseType, new Affine(typedBase, 1, 0));
        }
        return null;
    }

    private static IOperand? GuardedIndexAccess(
        MethodAnalysisContext method,
        Instruction instruction,
        int operandIndex,
        MemoryOperand memory,
        int pointerSize,
        Dictionary<LocalVariable, Instruction?> definitions,
        Func<Dictionary<LocalVariable, List<(Instruction Instruction, int OperandIndex)>>> uses,
        GuardedIndexContext context,
        LocalVariable array,
        SzArrayTypeAnalysisContext arrayType,
        Affine baseAffine)
    {
        var elementSize = ElementSize(arrayType.ElementType, pointerSize);
        if (elementSize == 0 && arrayType.ElementType.IsValueType)
            elementSize = MetadataElementSize(arrayType.ElementType, pointerSize);
        if (elementSize <= 0)
        {
            return null;
        }

        // An equality compare on a whole value type cannot be emitted, and an
        // ordering compare on a reference element compares element addresses;
        // leave both diagnosed.
        if ((ElementSize(arrayType.ElementType, pointerSize) == 0
                && instruction.OpCode is >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual)
            || (instruction.OpCode is OpCode.CheckLess or OpCode.CheckGreater
                or OpCode.CheckLessOrEqual or OpCode.CheckGreaterOrEqual
                && !arrayType.ElementType.IsValueType))
        {
            return null;
        }

        var indexAffine = ScaleBy(Evaluate(memory.Index, definitions, 0, true), Math.Max(memory.Scale, 1));
        if (indexAffine is not { Root: { } indexRoot } idx)
        {
            return null;
        }
        if (idx.Multiplier <= 0 || idx.Multiplier % elementSize != 0)
        {
            return null;
        }

        var multiplier = idx.Multiplier / elementSize;
        var tail = idx.Offset + baseAffine.Offset + memory.Addend - ElementsOffset(pointerSize);
        var fieldOffset = tail % elementSize;
        if (fieldOffset < 0)
            fieldOffset += elementSize;
        var bias = (tail - fieldOffset) / elementSize;

        // The check compares the element index `multiplier * root + bias`
        // against the length word, so that is the affine the guard must match.
        if (!ProveIndexGuard(method, instruction, array, new Affine(indexRoot, multiplier, bias),
                definitions, uses, context))
        {
            return null;
        }

        IOperand indexOperand = indexRoot;
        var inserted = new List<Instruction>();
        if (multiplier != 1)
        {
            var scaled = NewIndexTemp(method, ref context.TempIndex);
            inserted.Add(new Instruction(-1, OpCode.Multiply, scaled, indexOperand, new Immediate(multiplier)));
            indexOperand = scaled;
        }
        if (bias != 0)
        {
            var adjusted = NewIndexTemp(method, ref context.TempIndex);
            inserted.Add(new Instruction(-1, bias > 0 ? OpCode.Add : OpCode.Subtract, adjusted, indexOperand,
                new Immediate(Math.Abs(bias))));
            indexOperand = adjusted;
        }

        (IOperand Index, FieldAnalysisContext? Field)? resolved;
        if (arrayType.ElementType.IsValueType && ElementSize(arrayType.ElementType, pointerSize) == 0)
        {
            // Whole-element or member accesses of a struct can only be emitted
            // when the value flows to or from a slot typed as that struct (or a
            // member load) - a scalar-typed slot means the operand is really an
            // element address in disguise.
            var sibling = instruction.Operands[operandIndex == 0 ? 1 : 0];
            if (sibling is LocalVariable { Type: { } siblingType }
                && siblingType != arrayType.ElementType
                && fieldOffset == 0)
            {
                return null;
            }
            var normalized = new MemoryOperand(array, indexOperand,
                ElementsOffset(pointerSize) + fieldOffset, (int)elementSize, memory.AccessSize);
            resolved = ResolveStructElementAccess(instruction, operandIndex, normalized, arrayType,
                pointerSize, uses);
        }
        else
        {
            resolved = fieldOffset == 0 ? (indexOperand, null) : ((IOperand, FieldAnalysisContext?)?)null;
        }

        if (resolved is not { } access)
        {
            return null;
        }

        // A rewritten Move either loads the element into a slot (whose declared
        // type and transitive uses must accept it) or stores a value into the
        // element (whose type must fit the slot): anything else would emit an
        // element access where the coerced types cannot convert.
        var targetType = access.Field?.FieldType ?? arrayType.ElementType;
        if (!EmittedOperandFits(method, instruction, operandIndex, targetType, pointerSize, uses()))
        {
            return null;
        }

        if (context.Home(instruction) is not { } accessBlock)
            return null;

        if (inserted.Count != 0)
            accessBlock.Instructions.InsertRange(accessBlock.Instructions.IndexOf(instruction), inserted);

        return access.Field is { } elementField
            ? new ArrayElementFieldReference(array, access.Index, elementField)
            : new ArrayAccess(array, access.Index);
    }

    // Whether an operand carrying `emittedType` may occupy the slot it would
    // land in: `Move` destination and store source must convert to the slot
    // contract, a call argument must fit its parameter, a return its return
    // type, a throw a reference element. Simplifier copy propagation carries
    // the same operand into a moved local's uses, so each consumer is checked
    // the same way.
    private static bool EmittedOperandFits(
        MethodAnalysisContext method,
        Instruction instruction,
        int operandIndex,
        TypeAnalysisContext emittedType,
        int pointerSize,
        Dictionary<LocalVariable, List<(Instruction Instruction, int OperandIndex)>> uses,
        HashSet<LocalVariable>? visited = null)
        => instruction.OpCode switch
        {
            OpCode.Move => operandIndex == 1
                ? MoveDestinationAccepts(instruction.Operands[0], emittedType, method, pointerSize,
                    uses, visited)
                : StoredSourceAccepts(instruction.Operands[1], emittedType, method, pointerSize),
            OpCode.Call or OpCode.CallVoid => CallOperandSlotFits(instruction, operandIndex, emittedType),
            OpCode.CheckEqual or OpCode.CheckNotEqual => true,
            OpCode.CheckLess or OpCode.CheckGreater
                or OpCode.CheckLessOrEqual or OpCode.CheckGreaterOrEqual
                => ElementSize(emittedType, pointerSize) != 0,
            OpCode.Return => EmittedOperandFitsReturn(method, emittedType),
            OpCode.Throw => !emittedType.IsValueType,
            _ => false,
        };

    private static bool EmittedOperandFitsReturn(MethodAnalysisContext method, TypeAnalysisContext emittedType)
    {
        TypeAnalysisContext? returnType;
        try
        {
            returnType = method.ReturnType;
        }
        catch
        {
            returnType = null;
        }
        return returnType == null || emittedType.IsAssignableTo(returnType);
    }

    // The `this` or parameter slot an element operand lands in inside a call:
    // it must be assignable to the callee's receiver or parameter contract.
    private static bool CallOperandSlotFits(
        Instruction instruction,
        int operandIndex,
        TypeAnalysisContext emittedType)
    {
        if (instruction.Operands[0] is not MethodAnalysisContext callee)
            return true;
        var parameterIndex = operandIndex - (instruction.OpCode == OpCode.Call ? 2 : 1);
        if (!callee.IsStatic)
        {
            if (parameterIndex == 0)
                return !emittedType.IsValueType
                    && (callee.DeclaringType == null || emittedType.IsAssignableTo(callee.DeclaringType));
            parameterIndex--;
        }
        if (parameterIndex < 0 || parameterIndex >= callee.Parameters.Count
            || callee.Parameters[parameterIndex].ParameterType is not { } parameterType)
            return true;
        if (parameterType is ByRefTypeAnalysisContext { ElementType: { } pointee })
            parameterType = pointee;
        return emittedType.IsAssignableTo(parameterType);
    }

    // Whether an element value may land in `destination`: a local's declared
    // type must accept it and its transitive consumers must consume such a
    // value, while a field or nested element slot simply has to be assignable.
    private static bool MoveDestinationAccepts(
        IOperand destination,
        TypeAnalysisContext elementType,
        MethodAnalysisContext method,
        int pointerSize,
        Dictionary<LocalVariable, List<(Instruction Instruction, int OperandIndex)>> uses,
        HashSet<LocalVariable>? visited)
        => destination switch
        {
            // A store through `&local` writes the local's slot, so the copy's
            // consumers must keep seeing the emitted value.
            AddressOf { Target: LocalVariable addressed }
                => (addressed.Type is not { } addressedDeclared || elementType.IsAssignableTo(addressedDeclared))
                    && PropagationSafe(method, addressed, elementType, pointerSize, uses, visited),
            LocalVariable local => (local.Type is not { } declared || elementType.IsAssignableTo(declared))
                && PropagationSafe(method, local, elementType, pointerSize, uses, visited),
            FieldReference field => elementType.IsAssignableTo(field.Field.FieldType),
            SelectedFieldReference selectedField => elementType.IsAssignableTo(selectedField.FieldType),
            ArrayElementFieldReference elementField => elementType.IsAssignableTo(elementField.Field.FieldType),
            ArrayAccess { Array.Type: SzArrayTypeAnalysisContext destinationArray }
                => elementType.IsAssignableTo(destinationArray.ElementType),
            // A store into unmanaged memory keeps its own diagnostic; the
            // operand inside it is still the element's value.
            MemoryOperand => true,
            _ => false,
        };

    // Whether `source` stores a value that fits the element slot: locals and
    // field-like operands carry a declared type, scalar constants fit a
    // scalar element, and a string literal fits a reference element.
    private static bool StoredSourceAccepts(
        IOperand source,
        TypeAnalysisContext elementType,
        MethodAnalysisContext method,
        int pointerSize)
        => source switch
        {
            LocalVariable local => (LocalVariables.EmittedSlotLocalType(local, method) ?? local.Type)
                is { } sourceType && sourceType.IsAssignableTo(elementType),
            FieldReference field => field.Field.FieldType.IsAssignableTo(elementType),
            SelectedFieldReference selectedField => selectedField.FieldType.IsAssignableTo(elementType),
            ArrayElementFieldReference elementField => elementField.Field.FieldType.IsAssignableTo(elementType),
            ArrayAccess { Array.Type: SzArrayTypeAnalysisContext sourceArray }
                => sourceArray.ElementType.IsAssignableTo(elementType),
            Immediate or FloatLiteral or DoubleLiteral => ElementSize(elementType, pointerSize) != 0,
            StringLiteral => !elementType.IsValueType,
            _ => false,
        };

    // Whether every transitive consumer of a rewritten Move destination can
    // hold the emitted operand's type: Move copies are followed through, each
    // consumer's slot is checked like the rewrite's own, and integer or
    // address arithmetic on the operand would see the access where a raw
    // local was expected.
    private static bool PropagationSafe(
        MethodAnalysisContext method,
        LocalVariable destination,
        TypeAnalysisContext emittedType,
        int pointerSize,
        Dictionary<LocalVariable, List<(Instruction Instruction, int OperandIndex)>> uses,
        HashSet<LocalVariable>? visited = null)
    {
        visited ??= [];
        if (!visited.Add(destination) || !uses.TryGetValue(destination, out var sites))
            return true;

        var numeric = ElementSize(emittedType, pointerSize) != 0;
        foreach (var (site, operandIndex) in sites)
        {
            var safe = site.Operands[operandIndex] switch
            {
                // `&local` is the address of the slot, not of the element:
                // writes through it must keep landing on the local.
                AddressOf => false,
                // As an unmanaged memory base the operand still carries its
                // value (the load keeps its own diagnostic); as an index it
                // must be a scalar.
                MemoryOperand useMemory => ReferenceEquals(useMemory.Index, destination) ? numeric : true,
                _ => site.OpCode switch
                {
                    OpCode.Move => operandIndex == 1
                        && MoveDestinationAccepts(site.Operands[0], emittedType, method, pointerSize,
                            uses, visited),
                    OpCode.Call or OpCode.CallVoid => CallOperandSlotFits(site, operandIndex, emittedType),
                    OpCode.CheckEqual or OpCode.CheckNotEqual => true,
                    OpCode.CheckLess or OpCode.CheckGreater
                        or OpCode.CheckLessOrEqual or OpCode.CheckGreaterOrEqual => numeric,
                    OpCode.ConditionalJump => numeric || !emittedType.IsValueType,
                    OpCode.Return => EmittedOperandFitsReturn(method, emittedType),
                    OpCode.Throw => !emittedType.IsValueType,
                    _ => false,
                },
            };
            if (!safe)
                return false;
        }
        return true;
    }

    // A bounds check proves an element index when an unsigned compare of that
    // index against this array's length feeds a conditional jump (through
    // Move/Not chains, one `Not` per inverted sense) whose in-bounds edge
    // dominates the access. On ARM64 the unsigned compare is the carry flag:
    // a `CheckLess` whose destination is the "C" register - `B.HS`/`B.LO`
    // branches read it, and FlagConditionRecovery's signed folds never rewrite
    // it, while signed compares fold into Check* opcodes on other registers.
    private static bool ProveIndexGuard(
        MethodAnalysisContext method,
        Instruction accessInstruction,
        LocalVariable array,
        Affine elementIndex,
        Dictionary<LocalVariable, Instruction?> definitions,
        Func<Dictionary<LocalVariable, List<(Instruction Instruction, int OperandIndex)>>> uses,
        GuardedIndexContext context)
    {
        if (method.DominatorInfo is not { } dominators
            || context.Home(accessInstruction) is not { } accessBlock)
        {
            return false;
        }

        foreach (var candidate in method.ControlFlowGraph!.Instructions)
        {
            // Only the unsigned compare proves the index: `CheckLess` onto the
            // carry flag against this array's length word.
            if (candidate.OpCode != OpCode.CheckLess
                || candidate.Operands is not [LocalVariable { Register.Name: "C" } flag, _, _]
                || Evaluate(candidate.Operands[1], definitions, 0, true) is not { } compared
                || !ReferenceEquals(compared.Root, elementIndex.Root)
                || compared.Multiplier != elementIndex.Multiplier
                || compared.Offset != elementIndex.Offset)
                continue;

            if (EvaluateSeed(candidate.Operands[2], context.AllDefinitions, method, []) is not
                    { Type: SeedType.Length, Array: { } checkedArray }
                || !ReferenceEquals(checkedArray, array))
                continue;

            if (GuardedEdges(flag, uses(), context.HomeMap) is { } inBounds
                && inBounds.Any(inBoundsBlock => dominators.Dominates(inBoundsBlock, accessBlock)))
            {
                return true;
            }
        }

        return false;
    }

    // Walks the flag's readers through Move/Not copies; every ConditionalJump it
    // reaches yields an in-bounds successor - the jump target when the (possibly
    // inverted) comparison is true in bounds, the fall-through edge otherwise.
    private static IEnumerable<Block> GuardedEdges(
        LocalVariable flag,
        Dictionary<LocalVariable, List<(Instruction Instruction, int OperandIndex)>> uses,
        Dictionary<Instruction, Block> home)
    {
        var inBoundsEdges = new List<Block>();
        var frontier = new Queue<(LocalVariable Local, int NotCount)>();
        var visited = new HashSet<LocalVariable>();
        frontier.Enqueue((flag, 0));

        while (frontier.Count != 0)
        {
            var (local, nots) = frontier.Dequeue();
            if (!visited.Add(local) || !uses.TryGetValue(local, out var sites))
                continue;

            var running = nots;
            foreach (var (site, operandIndex) in sites)
            {
                switch (site)
                {
                    case { OpCode: OpCode.Not, Operands: [LocalVariable destination, var source] }
                        when operandIndex == 1 && ReferenceEquals(source, local):
                        if (ReferenceEquals(destination, local))
                            running++;
                        else
                            frontier.Enqueue((destination, running + 1));
                        break;
                    case { OpCode: OpCode.Move, Operands: [LocalVariable destination, var source] }
                        when operandIndex == 1 && ReferenceEquals(source, local):
                        frontier.Enqueue((destination, running));
                        break;
                    case { OpCode: OpCode.ConditionalJump } when operandIndex == 1
                        && home.TryGetValue(site, out var jumpBlock):
                        var inBounds = running % 2 == 0;
                        var target = site.Operands[0] switch
                        {
                            Block block => block,
                            Instruction targetInstruction => home.GetValueOrDefault(targetInstruction),
                            _ => null,
                        };
                        if (target == null)
                            break;
                        if (inBounds)
                        {
                            if (jumpBlock.Successors.Any(s => s != target))
                                inBoundsEdges.Add(target);
                        }
                        else if (jumpBlock.Successors.FirstOrDefault(s => s != target && s != jumpBlock)
                                 is { } fallThrough)
                            inBoundsEdges.Add(fallThrough);
                        break;
                }
            }
        }

        return inBoundsEdges;
    }

    private sealed class GuardedIndexContext(MethodAnalysisContext method)
    {
        private Dictionary<LocalVariable, List<Instruction>>? _allDefinitions;
        private Dictionary<Instruction, Block>? _homeMap;

        public int TempIndex;

        public Dictionary<LocalVariable, List<Instruction>> AllDefinitions => _allDefinitions ??= BuildAllDefinitions();

        public Dictionary<Instruction, Block> HomeMap => _homeMap ??= method.ControlFlowGraph!.Blocks
            .SelectMany(block => block.Instructions.Select(instruction => (instruction, block)))
            .ToDictionary(pair => pair.instruction, pair => pair.block);

        public Block? Home(Instruction instruction) => HomeMap.GetValueOrDefault(instruction);

        private Dictionary<LocalVariable, List<Instruction>> BuildAllDefinitions()
        {
            var result = new Dictionary<LocalVariable, List<Instruction>>();
            foreach (var instruction in method.ControlFlowGraph!.Instructions)
                if (instruction.Destination is LocalVariable destination)
                    (result.TryGetValue(destination, out var list) ? list : result[destination] = []).Add(instruction);
            return result;
        }
    }

    private static IOperand? ScaledIndex(IOperand operand, long elementSize,
        Dictionary<LocalVariable, Instruction?> definitions, int depth)
    {
        if (depth > 8 || elementSize <= 0)
            return null;
        if (elementSize == 1)
            return operand;
        if (operand is not LocalVariable local || !definitions.TryGetValue(local, out var definition) || definition == null)
            return null;

        IOperand? index = definition switch
        {
            { OpCode: OpCode.ShiftLeft, Operands: [_, var source, Immediate shift] }
                when shift.Value is >= 0 and < 63 && 1L << (int)shift.Value == elementSize => source,
            { OpCode: OpCode.Multiply, Operands: [_, var source, Immediate factor] }
                when factor.Value == elementSize => source,
            _ => null,
        };
        if (index is LocalVariable extended && definitions.TryGetValue(extended, out var extension)
            && extension is { OpCode: OpCode.SignExtend32, Operands: [_, var original] })
            index = original;
        return index;
    }

    // Group initializers after an array allocation together so ILSpy decompiles them better
    private static void GroupInitialisers(ISILControlFlowGraph cfg)
    {
        var movedAny = false;

        foreach (var block in cfg.Blocks.ToList())
        {
            foreach (var allocation in block.Instructions.ToList())
            {
                if (allocation.OpCode != OpCode.NewArr || allocation.Operands[0] is not LocalVariable array)
                    continue;

                var stores = new List<(Block Block, Instruction Instruction)>();
                var current = block;
                var index = current.Instructions.IndexOf(allocation) + 1;

                while (true)
                {
                    if (index >= current.Instructions.Count)
                    {
                        // only a straight-line run can be regrouped without changing what runs when
                        if (current.Successors.Count != 1 || current.Successors[0].Predecessors.Count != 1)
                            break;

                        current = current.Successors[0];
                        index = 0;
                        continue;
                    }

                    var instruction = current.Instructions[index];

                    if (IsElementStore(instruction, array))
                    {
                        stores.Add((current, instruction));
                        index++;
                        continue;
                    }

                    if (!ReadsArray(instruction, array))
                    {
                        index++;
                        continue;
                    }

                    // Found the first read. Move the allocation and its stores immediately in front, so the whole array is built in one chain with the elements already computed.
                    if (stores.Count > 1)
                    {
                        foreach (var (storeBlock, store) in stores)
                            storeBlock.Instructions.Remove(store);

                        block.Instructions.Remove(allocation);

                        var moved = new List<Instruction> { allocation };
                        moved.AddRange(stores.Select(s => s.Instruction));

                        current.Instructions.InsertRange(current.Instructions.IndexOf(instruction), moved);
                        movedAny = true;
                    }

                    break;
                }
            }
        }

        // Emptying a block out entirely leaves branches pointing at nothing to jump to
        if (movedAny)
            cfg.RemoveEmptyBlocks();
    }

    private static bool IsElementStore(Instruction instruction, LocalVariable array) =>
        instruction.OpCode == OpCode.Move && instruction.Operands[0] is ArrayAccess { Index: Immediate } stored
                                          && ReferenceEquals(stored.Array, array)
                                          && !ReadsArray(instruction, array);

    private static bool ReadsArray(Instruction instruction, LocalVariable array)
    {
        for (var i = 0; i < instruction.Operands.Count; i++)
        {
            if (i == 0 && instruction.OpCode == OpCode.Move)
                continue;

            var reads = instruction.Operands[i] switch
            {
                LocalVariable local => ReferenceEquals(local, array),
                ArrayAccess access => ReferenceEquals(access.Array, array),
                ArrayLength length => ReferenceEquals(length.Array, array),
                MemoryOperand memory => ReferenceEquals(memory.Base, array) || ReferenceEquals(memory.Index, array),
                AddressOf { Target: LocalVariable addressed } => ReferenceEquals(addressed, array),
                _ => false
            };

            if (reads)
                return true;
        }

        return false;
    }

    private static void RecoverAllocation(Instruction instruction)
    {
        // Call "SzArrayNew", result, typeof(T[]), length, ...
        if (!instruction.IsCall || instruction.Operands is not [StringLiteral { Value: var name }, LocalVariable result, TypeAnalysisContext type, { } length, ..]
            || !ArrayNewFunctions.Contains(name))
            return;

        instruction.OpCode = OpCode.NewArr;
        instruction.SetOperands(result, type, length);

        if (result.Type is not SzArrayTypeAnalysisContext)
            result.Type = type;
    }

    private static IOperand? ElementIndex(MemoryOperand memory, SzArrayTypeAnalysisContext arrayType, int pointerSize)
    {
        var elementSize = ElementSize(arrayType.ElementType, pointerSize);
        var offset = memory.Addend - ElementsOffset(pointerSize);

        if (offset < 0 || elementSize == 0 || offset % elementSize != 0)
            return null;

        if (memory.Index == null)
            return memory.Scale == 0 ? new Immediate(offset / elementSize) : null;

        return memory.Scale == elementSize && offset == 0 ? memory.Index : null;
    }

    // A dereference into an array of value-typed elements lands on an element
    // when the offset is past the header and element-aligned, on a member of
    // the element when a flat field covers the access width exactly. The
    // returned operand is the element index; field is null for a whole-element
    // access. Nested members, interior gaps and widths no member covers stay
    // unproven.
    private static (IOperand Index, FieldAnalysisContext? Field)? StructElementAccess(
        MemoryOperand memory, SzArrayTypeAnalysisContext arrayType, long accessWidth, int pointerSize)
    {
        var elementType = arrayType.ElementType;
        if (!elementType.IsValueType || ElementSize(elementType, pointerSize) != 0)
            return null;

        var elementSize = MetadataElementSize(elementType, pointerSize);
        if (elementSize <= 0)
            return null;

        var offset = memory.Addend - ElementsOffset(pointerSize);
        if (offset < 0)
            return null;

        IOperand index;
        long fieldOffset;
        if (memory.Index == null)
        {
            if (memory.Scale != 0)
                return null;
            index = new Immediate(offset / elementSize);
            fieldOffset = offset % elementSize;
        }
        else
        {
            if (memory.Scale != elementSize || offset >= elementSize)
                return null;
            index = memory.Index;
            fieldOffset = offset;
        }

        if (fieldOffset == 0 && accessWidth == elementSize)
            return (index, null);

        if (accessWidth <= 0
            || MetadataResolver.FindInstanceFieldPathAtOffset(elementType, fieldOffset, (int)accessWidth)
                is not { Field: { } field, Containers: { Count: 0 } }
            || PrimitiveElementFieldSize(field.FieldType, pointerSize) != accessWidth)
            return null;

        return (index, field);
    }

    // Wraps StructElementAccess with the instruction context a rewrite needs:
    // the width of a load or store comes from its Move sibling when the operand
    // itself records none, the sibling's declared type must agree with what is
    // being read or written, and a Move source whose destination is only ever
    // used as a pointer is a lifted lea - the element-address pass rewrites
    // those into &array[i]. The uses table is computed lazily; most operands
    // never need it.
    private static (IOperand Index, FieldAnalysisContext? Field)? ResolveStructElementAccess(
        Instruction instruction, int operandIndex, MemoryOperand memory,
        SzArrayTypeAnalysisContext arrayType, int pointerSize,
        Func<Dictionary<LocalVariable, List<(Instruction Instruction, int OperandIndex)>>> uses)
    {
        var sibling = operandIndex <= 1 && instruction is { OpCode: OpCode.Move, Operands: [_, { }] }
            ? instruction.Operands[1 - operandIndex]
            : null;

        if (operandIndex == 1 && sibling is LocalVariable destination
            && uses().TryGetValue(destination, out var destinationUses)
            && destinationUses.Count != 0
            && destinationUses.All(use => use.Instruction.IsCall
                || IsMemoryBase(use.Instruction.Operands[use.OperandIndex], destination)))
            return null;

        var accessWidth = memory.AccessSize != 0
            ? memory.AccessSize
            : sibling switch
            {
                // A SIMD store records no access size on the operand; a whole
                // vector literal is always a full 16-byte element write.
                Vector128Literal => 16,
                LocalVariable { Type: { } siblingType }
                    => (int)TypeSizes.MinimumUnboxedSize(siblingType, pointerSize),
                _ => 0,
            };

        if (StructElementAccess(memory, arrayType, accessWidth, pointerSize) is not { } access)
            return null;

        var targetType = access.Field?.FieldType ?? arrayType.ElementType;
        if (sibling is LocalVariable { Type: { } contract }
            && (contract.IsValueType
                ? contract.FullName != targetType.FullName
                : targetType.IsValueType))
            return null;

        return access;
    }

    private static long ElementSize(TypeAnalysisContext elementType, int pointerSize)
    {
        if (!elementType.IsValueType)
            return pointerSize;

        return elementType.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" => 1,
            "System.Int16" or "System.UInt16" or "System.Char" => 2,
            "System.Int32" or "System.UInt32" or "System.Single" => 4,
            "System.Int64" or "System.UInt64" or "System.Double" => 8,
            "System.IntPtr" or "System.UIntPtr" => pointerSize,
            _ => 0 // struct arrays are handled by the element-address path, which sizes them from metadata
        };
    }

    // Recovers &array[i] over struct arrays. Struct elements are never loaded outright, the compiler
    // computes their address via lea chains and calls through it. We solve the index as a linear function
    // of a local and demand an exact hit on the metadata stride, so a real load can't match by accident.
    private static void RecoverStructElementAddresses(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var cfg = method.ControlFlowGraph!;

        var definitions = SingleDefinitions(cfg);
        var uses = CollectUses(cfg);

        foreach (var instruction in cfg.Instructions)
        {
            if (instruction.IsCall)
            {
                for (var i = 1; i < instruction.Operands.Count; i++)
                {
                    if (MatchElementAddress(instruction.Operands[i], pointerSize, definitions) is { } inlined)
                        instruction.SetOperand(i, inlined);
                }

                continue;
            }

            // a Move from memory could be a load or a lifted lea, and only the uses tell them apart
            if (instruction is not { OpCode: OpCode.Move, Operands: [LocalVariable destination, MemoryOperand] })
                continue;

            if (definitions.TryGetValue(destination, out var single) && single == null)
                continue;

            if (!uses.TryGetValue(destination, out var destinationUses) || destinationUses.Count == 0
                || !destinationUses.All(u => u.Instruction.IsCall || IsMemoryBase(u.Instruction.Operands[u.OperandIndex], destination)))
                continue;

            if (MatchElementAddress(instruction.Operands[1], pointerSize, definitions) is { } address)
                instruction.SetOperand(1, address);
        }
    }

    private static AddressOf? MatchElementAddress(IOperand operand, int pointerSize, Dictionary<LocalVariable, Instruction?> definitions)
    {
        if (operand is not MemoryOperand memory
            || memory.Base is not LocalVariable { Type: SzArrayTypeAnalysisContext arrayType } array)
            return null;

        var elementType = arrayType.ElementType;
        if (!elementType.IsValueType || ElementSize(elementType, pointerSize) != 0)
            return null;

        var elementSize = MetadataElementSize(elementType, pointerSize);
        if (elementSize <= 0)
            return null;

        return StructElementIndex(memory, array, elementSize, pointerSize, definitions) is { } index
            ? new AddressOf(new ArrayAccess(array, index))
            : null;
    }

    private static bool IsMemoryBase(IOperand operand, LocalVariable local)
        => operand is MemoryOperand { Base: LocalVariable baseLocal } && ReferenceEquals(baseLocal, local);

    private static long MetadataElementSize(TypeAnalysisContext elementType, int pointerSize)
    {
        var metadataSize = TypeSizes.UnboxedSize(elementType, pointerSize);
        if (metadataSize > 0)
            return metadataSize;

        long size = 0;
        foreach (var field in elementType.Fields.Where(field => !field.IsStatic))
        {
            var fieldSize = PrimitiveElementFieldSize(field.FieldType, pointerSize);
            if (fieldSize <= 0)
                return 0;
            size = Math.Max(size, (field.BackingData?.FieldOffset ?? field.Offset) + fieldSize);
        }
        return size;
    }

    private static long PrimitiveElementFieldSize(TypeAnalysisContext type, int pointerSize) =>
        !type.IsValueType ? pointerSize : type.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" => 1,
            "System.Int16" or "System.UInt16" or "System.Char" => 2,
            "System.Int32" or "System.UInt32" or "System.Single" => 4,
            "System.Int64" or "System.UInt64" or "System.Double" => 8,
            "System.IntPtr" or "System.UIntPtr" => pointerSize,
            _ => TypeSizes.UnboxedSize(type, pointerSize)
        };

    private static IOperand? StructElementIndex(MemoryOperand memory, LocalVariable array, long elementSize, int pointerSize,
        Dictionary<LocalVariable, Instruction?> definitions)
    {
        var indexAffine = memory.Index is LocalVariable indexLocal
            ? ScaleBy(Evaluate(indexLocal, definitions, 0), Math.Max(memory.Scale, 1))
            : new Affine(null, 0, 0);

        if (Sum(indexAffine, new Affine(null, 0, memory.Addend)) is not { } address)
            return null;

        if (ReferenceEquals(address.Root, array))
            return null;

        var offset = address.Offset - ElementsOffset(pointerSize);

        if (address.Root != null)
            return address.Multiplier == elementSize && offset == 0 ? address.Root : null;

        return offset >= 0 && offset % elementSize == 0 ? new Immediate(offset / elementSize) : null;
    }

    // value = Multiplier * Root + Offset (a null Root means it's just a constant)
    private readonly record struct Affine(LocalVariable? Root, long Multiplier, long Offset);

    private static Affine? Evaluate(IOperand operand, Dictionary<LocalVariable, Instruction?> definitions,
        int depth, bool subtractIsAffine = false)
    {
        if (depth > 8)
            return null;

        switch (operand)
        {
            case Immediate { Value: var value }:
                return new Affine(null, 0, value);

            case LocalVariable local:
            {
                if (!definitions.TryGetValue(local, out var definition) || definition == null)
                    return new Affine(local, 1, 0);

                return definition switch
                {
                    { OpCode: OpCode.Move, Operands: [_, MemoryOperand lea] } => EvaluateLea(lea, definitions, depth + 1, subtractIsAffine),
                    { OpCode: OpCode.Move, Operands: [_, var source] } => Evaluate(source, definitions, depth + 1, subtractIsAffine),
                    { OpCode: OpCode.Add, Operands: [_, var left, var right] } => Sum(Evaluate(left, definitions, depth + 1, subtractIsAffine), Evaluate(right, definitions, depth + 1, subtractIsAffine)),
                    { OpCode: OpCode.Subtract, Operands: [_, var minuend, var subtrahend] } when subtractIsAffine => Sum(Evaluate(minuend, definitions, depth + 1, true), ScaleBy(Evaluate(subtrahend, definitions, depth + 1, true), -1)),
                    { OpCode: OpCode.ShiftLeft, Operands: [_, var left, Immediate { Value: >= 0 and < 32 } shift] } => ScaleBy(Evaluate(left, definitions, depth + 1, subtractIsAffine), 1L << (int)shift.Value),
                    { OpCode: OpCode.Multiply, Operands: [_, var left, Immediate factor] } => ScaleBy(Evaluate(left, definitions, depth + 1, subtractIsAffine), factor.Value),
                    _ => new Affine(local, 1, 0)
                };
            }

            default:
                return null;
        }
    }

    private static Affine? EvaluateLea(MemoryOperand lea, Dictionary<LocalVariable, Instruction?> definitions,
        int depth, bool subtractIsAffine = false)
    {
        var result = (Affine?)new Affine(null, 0, lea.Addend);

        if (lea.Base != null)
            result = Sum(result, Evaluate(lea.Base, definitions, depth, subtractIsAffine));

        if (lea.Index != null)
            result = Sum(result, ScaleBy(Evaluate(lea.Index, definitions, depth, subtractIsAffine), Math.Max(lea.Scale, 1)));

        return result;
    }

    private static Affine? Sum(Affine? left, Affine? right)
    {
        if (left is not { } l || right is not { } r)
            return null;

        if (l.Root != null && r.Root != null && !ReferenceEquals(l.Root, r.Root))
            return null;

        return new Affine(l.Root ?? r.Root, l.Multiplier + r.Multiplier, l.Offset + r.Offset);
    }

    private static Affine? ScaleBy(Affine? value, long factor)
        => value is { } affine ? new Affine(affine.Root, affine.Multiplier * factor, affine.Offset * factor) : null;

    // null means the local has more than one definition
    private static Dictionary<LocalVariable, Instruction?> SingleDefinitions(ISILControlFlowGraph cfg)
    {
        var definitions = new Dictionary<LocalVariable, Instruction?>();

        foreach (var instruction in cfg.Instructions)
            if (instruction.Destination is LocalVariable destination)
                definitions[destination] = definitions.ContainsKey(destination) ? null : instruction;

        return definitions;
    }

    internal static Dictionary<LocalVariable, List<(Instruction Instruction, int OperandIndex)>> CollectUses(ISILControlFlowGraph cfg)
    {
        var uses = new Dictionary<LocalVariable, List<(Instruction, int)>>();

        foreach (var instruction in cfg.Instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var operand = instruction.Operands[i];

                if (ReferenceEquals(operand, instruction.Destination))
                    continue;

                foreach (var local in OperandLocals(operand))
                {
                    if (!uses.TryGetValue(local, out var sites))
                        uses[local] = sites = [];
                    sites.Add((instruction, i));
                }
            }
        }

        return uses;
    }

    private static IEnumerable<LocalVariable> OperandLocals(IOperand operand)
    {
        switch (operand)
        {
            case LocalVariable direct:
                yield return direct;
                break;
            case MemoryOperand memory:
                if (memory.Base is LocalVariable baseLocal)
                    yield return baseLocal;
                if (memory.Index is LocalVariable indexLocal)
                    yield return indexLocal;
                break;
            case AddressOf { Target: LocalVariable addressed }:
                yield return addressed;
                break;
        }
    }

    // IL2CPP's managed array code often drops the array itself and keeps only an
    // element pointer: a local seeded at `array + elementsOffset`, stepped once per
    // iteration by the element stride (typically a post-indexed load writeback) and
    // dereferenced in lockstep with a loop counter. When every definition of the
    // pointer proves the same array root and every step is exactly the element
    // stride, dereferences of it are element accesses. The element index is the
    // loop's own counter: an up-counter seeded at 0 checked against the length, or
    // a down-counter seeded from the length itself (`index = length - counter`).
    private static void RecoverElementPointerWalkers(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var definitions = new Dictionary<LocalVariable, List<Instruction>>();
        foreach (var candidate in cfg.Instructions)
            if (candidate.Destination is LocalVariable destination)
                (definitions.TryGetValue(destination, out var list) ? list : definitions[destination] = []).Add(candidate);

        var resolvedPointers = new Dictionary<LocalVariable, ElementPointer?>();
        var resolvedCounters = new Dictionary<LocalVariable, List<LoopCounter>?>();
        var tempIndex = 0;

        foreach (var block in cfg.Blocks)
        {
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                var instruction = block.Instructions[i];
                for (var o = 0; o < instruction.Operands.Count; o++)
                {
                    if (instruction.Operands[o] is not MemoryOperand { Base: LocalVariable baseLocal } memory)
                        continue;

                    if (!resolvedPointers.TryGetValue(baseLocal, out var pointer))
                        resolvedPointers[baseLocal] = pointer = ResolveElementPointer(baseLocal, definitions,
                            pointerSize, method);
                    if (pointer is not { } elementPointer)
                        continue;

                    var offset = elementPointer.ByteOffset + memory.Addend - ElementsOffset(pointerSize);
                    if (offset < 0 || offset % elementPointer.ElementSize != 0)
                        continue;
                    var indexOffset = offset / elementPointer.ElementSize;

                    // A dereference wider than the element reads across elements; leave it alone
                    if (memory.AccessSize > elementPointer.ElementSize)
                        continue;

                    List<Instruction>? insert = null;
                    IOperand? index;
                    if (memory.Index != null)
                    {
                        // [pointer + index * stride] - a fixed element pointer plus an explicit index
                        if (elementPointer.HasSteps || memory.Scale != elementPointer.ElementSize)
                            continue;
                        index = memory.Index;
                        if (indexOffset != 0)
                        {
                            var adjusted = NewIndexTemp(method, ref tempIndex);
                            (insert ??= []).Add(new Instruction(-1, OpCode.Add, adjusted, index,
                                new Immediate(indexOffset)));
                            index = adjusted;
                        }
                    }
                    else if (!elementPointer.HasSteps)
                    {
                        index = new Immediate(indexOffset);
                    }
                    else
                    {
                        if (!resolvedCounters.TryGetValue(elementPointer.Array, out var counters))
                            resolvedCounters[elementPointer.Array] =
                                counters = LoopCountersFor(method, elementPointer.Array, definitions);
                        if (counters == null)
                            continue;

                        if (FindLoopCounter(counters, definitions, block) is not { } counter)
                            continue;

                        if (counter.Direction == CounterDirection.Down)
                        {
                            var difference = NewIndexTemp(method, ref tempIndex);
                            (insert ??= []).Add(new Instruction(-1, OpCode.Subtract, difference,
                                new ArrayLength(elementPointer.Array), counter.Local));
                            index = difference;
                            var delta = counter.SeedDelta + indexOffset;
                            if (delta != 0)
                            {
                                var adjusted = NewIndexTemp(method, ref tempIndex);
                                insert!.Add(new Instruction(-1, OpCode.Add, adjusted, index, new Immediate(delta)));
                                index = adjusted;
                            }
                        }
                        else
                        {
                            var delta = indexOffset - counter.SeedDelta;
                            index = counter.Local;
                            if (delta != 0)
                            {
                                var adjusted = NewIndexTemp(method, ref tempIndex);
                                (insert ??= []).Add(new Instruction(-1, OpCode.Add, adjusted, index,
                                    new Immediate(delta)));
                                index = adjusted;
                            }
                        }
                    }

                    if (insert != null)
                    {
                        block.Instructions.InsertRange(i, insert);
                        i += insert.Count;
                    }
                    instruction.SetOperand(o, new ArrayAccess(elementPointer.Array, index));
                }
            }
        }

        // Drop the pointer chain once no remaining use escapes its own definitions.
        var removed = new HashSet<Instruction>();
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var (pointerLocal, elementPointer) in resolvedPointers)
            {
                if (elementPointer is not { } resolved || resolved.Definitions.All(removed.Contains))
                    continue;

                var stillUsed = cfg.Instructions.Any(u => !removed.Contains(u)
                    && !resolved.Definitions.Contains(u)
                    && u.Operands.Any(o => OperandLocals(o).Any(used => ReferenceEquals(used, pointerLocal))));
                if (stillUsed)
                    continue;

                foreach (var definition in resolved.Definitions)
                    if (removed.Add(definition))
                        MakeNop(definition);
                changed = true;
            }
        }
    }

    private static LocalVariable NewIndexTemp(MethodAnalysisContext method, ref int counter)
    {
        var name = $"elementIndex{counter++}";
        var local = new LocalVariable(name, new Register(null, name), method.AppContext.SystemTypes.SystemInt32Type);
        method.Locals.Add(local);
        return local;
    }

    private readonly record struct ElementPointer(LocalVariable Array, long ByteOffset, long ElementSize,
        bool HasSteps, List<Instruction> Definitions);

    // Prove a local is `array + constant`: every seed definition must resolve to the
    // same array at the same byte offset, and every self-step must be a definition we
    // can account for. A Move from an undefined non-parameter local is the phi-removal
    // copy of the loop-carried version - it adds no constraint. SSA pair shapes like
    // `p = phi(pBack)`/`pBack = p + stride` are handled by treating the Move-linked
    // group of locals as a single value.
    private static ElementPointer? ResolveElementPointer(LocalVariable pointer,
        Dictionary<LocalVariable, List<Instruction>> definitions, int pointerSize, MethodAnalysisContext method)
    {
        var group = PhiGroupFor(pointer, definitions, method);
        var defs = GroupDefinitions(group, definitions);
        if (defs.Count == 0)
            return null;

        var seeds = new List<(LocalVariable Array, long Offset)>();
        var steps = new List<long>();

        foreach (var def in defs)
        {
            switch (def)
            {
                case { OpCode: OpCode.Add, Operands: [_, LocalVariable source, Immediate step] }
                    when group.Contains(source):
                    if (step.Value <= 0)
                        return null;
                    steps.Add(step.Value);
                    break;
                case { OpCode: OpCode.Add or OpCode.Or, Operands: [_, var source, Immediate delta] }:
                    if (ResolvePointerRoot(source, definitions, method, [], 0) is not { } added)
                        return null;
                    seeds.Add((added.Array, added.Offset + delta.Value));
                    break;
                case { OpCode: OpCode.Move, Operands: [_, var source] }:
                    if (source is LocalVariable sourceLocal && group.Contains(sourceLocal)
                        || IsLoopCarriedCopy(source, definitions, method))
                        break;
                    if (ResolvePointerRoot(source, definitions, method, [], 0) is not { } moved)
                        return null;
                    seeds.Add(moved);
                    break;
                default:
                    return null;
            }
        }

        if (seeds.Count == 0)
            return null;

        var array = seeds[0].Array;
        var offset = seeds[0].Offset;
        if (array.Type is not SzArrayTypeAnalysisContext arrayType
            || seeds.Skip(1).Any(seed => !ReferenceEquals(seed.Array, array) || seed.Offset != offset))
            return null;

        var elementSize = ElementSize(arrayType.ElementType, pointerSize);
        if (elementSize <= 0 || steps.Any(step => step != elementSize))
            return null;

        return new ElementPointer(array, offset, elementSize, steps.Count > 0, defs);
    }

    private static bool IsLoopCarriedCopy(IOperand operand, Dictionary<LocalVariable, List<Instruction>> definitions,
        MethodAnalysisContext method) =>
        operand is LocalVariable local
        && !definitions.ContainsKey(local)
        && method.ParameterLocals?.Contains(local) != true;

    private static (LocalVariable Array, long Offset)? ResolvePointerRoot(IOperand operand,
        Dictionary<LocalVariable, List<Instruction>> definitions, MethodAnalysisContext method,
        HashSet<LocalVariable> visiting, int depth)
    {
        if (depth > 8 || operand is not LocalVariable local || !visiting.Add(local))
            return null;

        var found = TryResolveLocalPointerRoot(local, definitions, method, visiting, depth);
        visiting.Remove(local);
        return found;
    }

    private static (LocalVariable, long)? TryResolveLocalPointerRoot(LocalVariable local,
        Dictionary<LocalVariable, List<Instruction>> definitions, MethodAnalysisContext method,
        HashSet<LocalVariable> visiting, int depth)
    {
        if (local.Type is { } type)
            return type is SzArrayTypeAnalysisContext ? (local, 0) : null;

        var group = PhiGroupFor(local, definitions, method);
        var defs = GroupDefinitions(group, definitions);
        if (defs.Count == 0)
            return null;

        (LocalVariable, long)? found = null;
        foreach (var def in defs)
        {
            // loop-carried copies and pure self-references don't reseed the value
            if (def is { OpCode: OpCode.Move, Operands: [_, var copySource] }
                && (copySource is LocalVariable copyLocal && group.Contains(copyLocal)
                    || IsLoopCarriedCopy(copySource, definitions, method)))
                continue;

            // a constant stride step inside the phi group is transparent to the root;
            // any other self-referencing write makes the value vary per iteration
            if (def.Operands.Count > 1 && def.Operands[1] is LocalVariable stepSource
                && group.Contains(stepSource))
            {
                if (def is { OpCode: OpCode.Add, Operands: [_, _, Immediate] })
                    continue;
                return null;
            }

            var seed = def switch
            {
                { OpCode: OpCode.Move, Operands: [_, var moveSource] }
                    => ResolvePointerRoot(moveSource, definitions, method, visiting, depth + 1),
                { OpCode: OpCode.Add or OpCode.Or, Operands: [_, var operandSource, Immediate delta] }
                    => ResolvePointerRoot(operandSource, definitions, method, visiting, depth + 1) is { } rooted
                        ? (rooted.Array, rooted.Offset + delta.Value)
                        : null,
                _ => null,
            };

            if (seed is not { } resolvedSeed)
                return null;
            if (found == null)
                found = resolvedSeed;
            else if (found.Value != resolvedSeed)
                return null;
        }

        return found;
    }

    // The loop-carried phi group of a local: itself plus every untyped non-parameter
    // local reachable through Move copies, e.g. `p`/`pBack` from `Move p, pBack`.
    private static HashSet<LocalVariable> PhiGroupFor(LocalVariable local,
        Dictionary<LocalVariable, List<Instruction>> definitions, MethodAnalysisContext method)
    {
        var group = new HashSet<LocalVariable> { local };
        var queue = new Queue<LocalVariable>();
        queue.Enqueue(local);
        while (queue.Count > 0)
        {
            var member = queue.Dequeue();
            if (!definitions.TryGetValue(member, out var defs))
                continue;
            foreach (var def in defs)
            {
                if (def is { OpCode: OpCode.Move, Operands: [_, LocalVariable { Type: null } source] }
                    && method.ParameterLocals?.Contains(source) != true
                    && group.Add(source))
                    queue.Enqueue(source);
            }
        }

        return group;
    }

    private static List<Instruction> GroupDefinitions(HashSet<LocalVariable> group,
        Dictionary<LocalVariable, List<Instruction>> definitions) =>
        group.SelectMany(member => definitions.TryGetValue(member, out var defs) ? defs : []).ToList();

    private enum SeedType { Constant, Length }
    private readonly record struct Seed(SeedType Type, LocalVariable? Array, long Delta);
    private enum CounterDirection { Up, Down }
    private readonly record struct LoopCounter(LocalVariable Local, CounterDirection Direction, long SeedDelta,
        HashSet<LocalVariable> Group);

    private static Seed? EvaluateSeed(IOperand operand, Dictionary<LocalVariable, List<Instruction>> definitions,
        MethodAnalysisContext method, HashSet<LocalVariable> visiting) =>
        operand switch
        {
            Immediate immediate => new Seed(SeedType.Constant, null, immediate.Value),
            ArrayLength length => new Seed(SeedType.Length, length.Array, 0),
            LocalVariable local when !visiting.Add(local) => null,
            LocalVariable local => EvaluateLocalSeed(local, definitions, method, visiting),
            _ => null,
        };

    private static Seed? EvaluateLocalSeed(LocalVariable local,
        Dictionary<LocalVariable, List<Instruction>> definitions, MethodAnalysisContext method,
        HashSet<LocalVariable> visiting)
    {
        Seed? found = null;
        var group = PhiGroupFor(local, definitions, method);
        var defs = GroupDefinitions(group, definitions);
        if (defs.Count == 0)
        {
            visiting.Remove(local);
            return null;
        }

        var failed = false;
        foreach (var def in defs)
        {
            if (def is { OpCode: OpCode.Move, Operands: [_, var source] }
                && (source is LocalVariable sourceLocal && group.Contains(sourceLocal)
                    || IsLoopCarriedCopy(source, definitions, method)))
                continue;
            if (IsSelfDefinition(def, group))
                continue;

            var seed = EvaluateDefSeed(def, definitions, method, visiting);

            if (seed is not { } evaluated)
            {
                failed = true;
                break;
            }
            if (found == null)
                found = evaluated;
            else if (found.Value != evaluated)
            {
                failed = true;
                break;
            }
        }

        visiting.Remove(local);
        return failed ? null : found;
    }

    // The value a definition writes, expressed as a seed: a constant, or the length of a
    // specific array plus a delta. Move copies, sign-width masks (and -1 / 0xFFFFFFFF)
    // and constant offsets keep the seed; anything else is opaque.
    private static Seed? EvaluateDefSeed(Instruction def,
        Dictionary<LocalVariable, List<Instruction>> definitions, MethodAnalysisContext method,
        HashSet<LocalVariable> visiting) =>
        def switch
        {
            { OpCode: OpCode.Move, Operands: [_, var src] }
                => EvaluateSeed(src, definitions, method, visiting),
            { OpCode: OpCode.And, Operands: [_, var src, Immediate mask] }
                when mask.Value is -1 or 0xFFFFFFFFL
                => EvaluateSeed(src, definitions, method, visiting),
            { OpCode: OpCode.Add, Operands: [_, var src, Immediate delta] }
                => EvaluateSeed(src, definitions, method, visiting) is { } s
                    ? new Seed(s.Type, s.Array, s.Delta + delta.Value)
                    : null,
            { OpCode: OpCode.Subtract, Operands: [_, var src, Immediate delta] }
                => EvaluateSeed(src, definitions, method, visiting) is { } s
                    ? new Seed(s.Type, s.Array, s.Delta - delta.Value)
                    : null,
            _ => null,
        };

    // The definition rewrites a phi-group member in terms of another member —
    // it steps the value rather than reseeding it.
    private static bool IsSelfDefinition(Instruction def, HashSet<LocalVariable> group) =>
        def.OpCode switch
        {
            OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Modulo
                or OpCode.ShiftLeft or OpCode.ShiftRight or OpCode.And or OpCode.Or or OpCode.Xor
                or OpCode.Not or OpCode.Negate or OpCode.SignExtend32
                => def.Operands.Count > 1 && def.Operands[0] is LocalVariable destination && group.Contains(destination)
                    && def.Operands[1] is LocalVariable source && group.Contains(source),
            _ => false,
        };

    private static bool IsSelfStep(Instruction def, HashSet<LocalVariable> group, out bool isDown)
    {
        isDown = def.OpCode == OpCode.Subtract;
        return def is { OpCode: OpCode.Add or OpCode.Subtract, Operands: [LocalVariable d, LocalVariable s, Immediate { Value: 1 }] }
            && group.Contains(d) && group.Contains(s);
    }

    private static List<LoopCounter>? LoopCountersFor(MethodAnalysisContext method, LocalVariable array,
        Dictionary<LocalVariable, List<Instruction>> definitions)
    {
        var counters = new List<LoopCounter>();
        var seenGroups = new List<HashSet<LocalVariable>>();
        foreach (var local in definitions.Keys)
        {
            if (method.ParameterLocals?.Contains(local) == true)
                continue;

            var group = PhiGroupFor(local, definitions, method);
            // Phi partners share one group; evaluate it once
            if (seenGroups.Any(g => g.SetEquals(group)))
                continue;
            seenGroups.Add(group);
            var up = false;
            var down = false;
            var seeds = new List<Seed>();
            var failed = false;
            foreach (var def in GroupDefinitions(group, definitions))
            {
                if (IsSelfStep(def, group, out var isDown))
                {
                    if (isDown) down = true; else up = true;
                    continue;
                }
                if (def is { OpCode: OpCode.Move, Operands: [_, var source] }
                    && (source is LocalVariable sourceLocal && group.Contains(sourceLocal)
                        || IsLoopCarriedCopy(source, definitions, method)))
                    continue;
                if (IsSelfDefinition(def, group))
                {
                    failed = true;
                    break;
                }

                var seed = EvaluateDefSeed(def, definitions, method, []);

                if (seed is not { } evaluated)
                {
                    failed = true;
                    break;
                }
                seeds.Add(evaluated);
            }

            if (failed || up == down || seeds.Count == 0)
                continue;

            var first = seeds[0];
            if (seeds.Skip(1).Any(seed => seed != first))
                continue;

            if (down
                && first is { Type: SeedType.Length, Array: { } seedArray }
                && ReferenceEquals(seedArray, array))
            {
                counters.Add(new LoopCounter(local, CounterDirection.Down, first.Delta, group));
            }
            else if (up
                && first.Type == SeedType.Constant
                && CheckedAgainstLength(method, local, array, definitions))
            {
                counters.Add(new LoopCounter(local, CounterDirection.Up, first.Delta, group));
            }
        }

        return counters.Count == 0 ? null : counters;
    }

    private static bool CheckedAgainstLength(MethodAnalysisContext method, LocalVariable candidate,
        LocalVariable array, Dictionary<LocalVariable, List<Instruction>> definitions) =>
        method.ControlFlowGraph!.Instructions.Any(instruction =>
            instruction.OpCode is >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual
            && instruction.Operands.Skip(1).Any(o => ReferenceEquals(o, candidate))
            && instruction.Operands.Skip(1).Any(o =>
                EvaluateSeed(o, definitions, method, []) is { Type: SeedType.Length, Array: { } lengthArray }
                && ReferenceEquals(lengthArray, array)));

    private static LoopCounter? FindLoopCounter(List<LoopCounter> counters,
        Dictionary<LocalVariable, List<Instruction>> definitions, Block block)
    {
        // A down-counter only equals `length - index` inside the loop it steps in; require the
        // step to share the access's block. Up-counters are index-valued anywhere they are live.
        var down = counters.Where(c => c.Direction == CounterDirection.Down
            && GroupDefinitions(c.Group, definitions).Any(d => block.Instructions.Contains(d)
                && IsSelfStep(d, c.Group, out var isDown) && isDown)).ToList();
        if (down.Count == 1)
            return down[0];
        if (down.Count > 1)
            return null;

        var ups = counters.Where(c => c.Direction == CounterDirection.Up).ToList();
        if (ups.Count == 1)
            return ups[0];
        var inBlock = ups.Where(c => GroupDefinitions(c.Group, definitions).Any(d => block.Instructions.Contains(d)
            && IsSelfStep(d, c.Group, out var isDown) && !isDown)).ToList();
        return inBlock.Count == 1 ? inBlock[0] : null;
    }

}
