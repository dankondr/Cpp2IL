using System;
using System.Collections.Generic;
using System.Linq;
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
        RecoverAccesses(method);
        RecoverElementPointerWalkers(method);
        RecoverReferenceArrayOffsetWalkers(method);
        RecoverStructPointerWalkers(method);
        RecoverObjectFieldAddresses(method);
        RecoverFieldAddressAliases(method);
        RecoverValueTypeFieldAddresses(method);
        RecoverStructElementAddresses(method);
        RecoverStructArrayBulkCopies(method);
        GroupInitialisers(method.ControlFlowGraph!);
    }

    // Clang initializes struct arrays in 16-byte chunks: it takes &stackLocal, then copies
    // [local+N] into [arrayHeader+index*stride+N]. Managed IL has no partial struct store;
    // when the first chunk names a complete typed stack local, restore the one honest
    // operation (array[index] = local) and discard the remaining chunks for that element.
    private static void RecoverStructArrayBulkCopies(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
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

            foreach (var chunk in cfg.Instructions)
                if (!ReferenceEquals(chunk, instruction) && chunk is
                    { OpCode: OpCode.Move, Operands: [MemoryOperand { Base: LocalVariable chunkArray,
                        Index: null, Scale: 0, Addend: var chunkOffset }, _] }
                    && ReferenceEquals(chunkArray, array)
                    && chunkOffset >= elementStart && chunkOffset < elementEnd)
                    MakeNop(chunk);
        }
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
    // ArrayAccess for the given array type.
    internal static bool ResolvesAccess(MemoryOperand memory, SzArrayTypeAnalysisContext arrayType, int pointerSize)
    {
        if (memory.Index == null && memory.Scale == 0 && memory.Addend == LengthOffset(pointerSize))
            return true;

        return ElementIndex(memory, arrayType, pointerSize) != null;
    }

    internal static void RecoverAccesses(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var definitions = SingleDefinitions(method.ControlFlowGraph!);

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
                    if (DerivedElementAccess(memory, pointerSize, definitions) is { } derived)
                        instruction.SetOperand(i, derived);
                    continue;
                }

                if (memory.Index == null && memory.Scale == 0 && memory.Addend == LengthOffset(pointerSize))
                {
                    instruction.SetOperand(i, new ArrayLength(array));
                    continue;
                }

                if (ElementIndex(memory, arrayType, pointerSize) is { } index)
                    instruction.SetOperand(i, new ArrayAccess(array, index));
            }
        }
    }

    private static ArrayAccess? DerivedElementAccess(MemoryOperand memory, int pointerSize,
        Dictionary<LocalVariable, Instruction?> definitions)
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

            var elementSize = ElementSize(((SzArrayTypeAnalysisContext)array.Type!).ElementType, pointerSize);
            return ScaledIndex(possibleIndex, elementSize, definitions, 0) is { } index
                ? new ArrayAccess(array, index)
                : null;
        }
    }

    private static LocalVariable? ResolveArray(IOperand operand,
        Dictionary<LocalVariable, Instruction?> definitions, int depth)
    {
        if (depth > 8 || operand is not LocalVariable local)
            return null;
        if (local.Type is SzArrayTypeAnalysisContext)
            return local;
        return definitions.TryGetValue(local, out var definition)
            && definition is { OpCode: OpCode.Move, Operands: [_, var source] }
                ? ResolveArray(source, definitions, depth + 1)
                : null;
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

    private static Affine? Evaluate(IOperand operand, Dictionary<LocalVariable, Instruction?> definitions, int depth)
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
                    { OpCode: OpCode.Move, Operands: [_, MemoryOperand lea] } => EvaluateLea(lea, definitions, depth + 1),
                    { OpCode: OpCode.Move, Operands: [_, var source] } => Evaluate(source, definitions, depth + 1),
                    { OpCode: OpCode.Add, Operands: [_, var left, var right] } => Sum(Evaluate(left, definitions, depth + 1), Evaluate(right, definitions, depth + 1)),
                    { OpCode: OpCode.ShiftLeft, Operands: [_, var left, Immediate { Value: >= 0 and < 32 } shift] } => ScaleBy(Evaluate(left, definitions, depth + 1), 1L << (int)shift.Value),
                    { OpCode: OpCode.Multiply, Operands: [_, var left, Immediate factor] } => ScaleBy(Evaluate(left, definitions, depth + 1), factor.Value),
                    _ => new Affine(local, 1, 0)
                };
            }

            default:
                return null;
        }
    }

    private static Affine? EvaluateLea(MemoryOperand lea, Dictionary<LocalVariable, Instruction?> definitions, int depth)
    {
        var result = (Affine?)new Affine(null, 0, lea.Addend);

        if (lea.Base != null)
            result = Sum(result, Evaluate(lea.Base, definitions, depth));

        if (lea.Index != null)
            result = Sum(result, ScaleBy(Evaluate(lea.Index, definitions, depth), Math.Max(lea.Scale, 1)));

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

    private static Dictionary<LocalVariable, List<(Instruction Instruction, int OperandIndex)>> CollectUses(ISILControlFlowGraph cfg)
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
