using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Analysis;

// A small value type the ABI passes in one integer register is carried whole: the
// register's bits are the struct's byte layout, so a mask, shift, extension or
// compare against the register reads the bytes at those positions - `And x,#255`
// on a packed `Nullable<T>` is `hasValue`, `Lsr #32` is the second of two int
// fields, and `CheckLess packed,256` on a two-byte struct tests whether the high
// field is zero. Left as integer ops they surface as "Unrecoverable integer
// operation" on every use; this pass rewrites the ones whose read range lands
// exactly on a layout field into a field read and leaves every other read
// diagnosed.
//
// The packed value is the low `min(size, 8)` bytes of the register; bytes past
// the struct are treated as zero, matching what the callee's ABI writes.
internal static class PackedRegisterFields
{
    private enum LeafKind
    {
        // Any leaf whose emitted value equals its stored bits.
        Integral,
        // The read keeps the field's bits verbatim and the destination takes the
        // field's own type, so any concrete leaf is a read of that field.
        Whole,
        // The read zero-extends: only an unsigned or boolean leaf's value matches.
        Unsigned,
        // The read sign-extends: a signed leaf's value matches (a boolean is 0/1).
        Signed,
        // Comparison targets may additionally name a reference field (a null test).
        Any,
    }

    private enum Comparison
    {
        Equal,
        NotEqual,
        Less,
        LessOrEqual,
        Greater,
        GreaterOrEqual,
    }

    public static bool Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph;
        if (graph == null)
            return false;

        var pointerSize = method.AppContext.Binary.PointerSizeBytes;

        // The flag-pair fold follows a temporary to its definition, which is only
        // meaningful while the local has exactly one. SSA guarantees that; after
        // removal a coalesced local can be redefined, so only single-definition
        // locals join the map - a `TEMP` that survived coalescing still folds.
        var definitions = new Dictionary<LocalVariable, Instruction>();
        var redefined = new HashSet<LocalVariable>();
        foreach (var instruction in graph.Instructions)
        {
            if (instruction.Destination is not LocalVariable destination)
                continue;
            if (!definitions.TryAdd(destination, instruction))
                redefined.Add(destination);
        }
        foreach (var local in redefined)
            definitions.Remove(local);

        var foldedSources = new HashSet<Instruction>();
        var changed = false;
        foreach (var instruction in graph.Instructions)
        {
            changed |= RewriteSelectingOperation(method, instruction, pointerSize);
            changed |= RewritePackedComparison(method, instruction, definitions,
                foldedSources, pointerSize);
        }

        // A subtraction whose only consumers were rewritten flag checks carries no
        // remaining semantics - drop it rather than emit a dead diagnostic.
        foreach (var subtraction in foldedSources)
        {
            if (IsStillUsed(graph, subtraction))
                continue;
            subtraction.OpCode = OpCode.Nop;
            changed = true;
        }

        return changed;
    }

    private static bool IsStillUsed(ISILControlFlowGraph graph, Instruction subtraction)
    {
        if (subtraction.Destination is not LocalVariable dead)
            return true;
        foreach (var instruction in graph.Instructions)
        {
            if (ReferenceEquals(instruction, subtraction))
                continue;
            foreach (var operand in instruction.Operands)
                if (LocalVariables.OperandLocals(operand).Any(local => ReferenceEquals(local, dead)))
                    return true;
        }
        return false;
    }

    private static bool RewriteSelectingOperation(MethodAnalysisContext method,
        Instruction instruction, int pointerSize)
    {
        var operandWidth = instruction.NativeIntegerWidthBits == 32 ? 4 : 8;
        switch (instruction.OpCode)
        {
            case OpCode.Move:
                if (instruction.Operands.Count != 2)
                    return false;
                if (instruction.NativeReadWidthBits is { } readBits
                    && readBits > 0 && readBits % 8 == 0)
                    return TryWholeRead(method, instruction, 0, readBits / 8, pointerSize,
                        instruction.NativeReadSignExtend == true ? LeafKind.Signed : LeafKind.Unsigned);
                // A move into an integer-typed local is the W-register truncation of
                // the packed struct: the destination type is the read contract.
                if (instruction.Destination is LocalVariable { Type: { } destinationType }
                    && IlGenerator.IntegralStackWidth(destinationType) is var stackWidth
                    && stackWidth is 4 or 8)
                    return TryWholeRead(method, instruction, 0, stackWidth, pointerSize,
                        LeafKind.Whole);
                return false;

            case OpCode.SignExtend32:
                return instruction.Operands.Count == 2
                    && TryWholeRead(method, instruction, 0, 4, pointerSize, LeafKind.Signed);

            case OpCode.ShiftRight:
                // `P >> n` keeps bytes [n/8, packedSize) of the source register:
                // when that range is exactly one field the shift is the field's
                // read, and when it reaches only layout padding the shift is
                // zero. The leaf fills the range, so the field's bits land in
                // the destination verbatim - the width (and with it the
                // signedness beyond the leaf) is a property of the destination
                // local, which takes the leaf's own type.
                if (instruction.Operands.Count == 3
                    && instruction.Operands[2] is Immediate { Value: var bits }
                    && bits >= 0 && bits % 8 == 0
                    && PackedOperandType(instruction.Operands[1], pointerSize) is { } shiftedType)
                {
                    var shiftedSize = PackedSize(shiftedType, pointerSize);
                    if (bits / 8 >= shiftedSize
                        || !AnyFieldInRange(shiftedType, (int)(bits / 8),
                            shiftedSize - (int)(bits / 8), pointerSize))
                    {
                        SetConstant(instruction, instruction.Destination!, 0);
                        return true;
                    }
                    if (TryWholeRead(method, instruction, (int)(bits / 8),
                            shiftedSize - (int)(bits / 8), pointerSize, LeafKind.Whole))
                        return true;
                }
                goto default;

            case OpCode.And:
                // A contiguous run of set bits selects a bit range of the register:
                // `P & mask` keeps the covered bits in place - a plain read at
                // offset zero, a shifted read anywhere else, and zero when every
                // masked bit is layout padding.
                IOperand? maskOperand;
                long maskValue;
                if (instruction.Operands.Count == 3
                    && instruction.Operands[1] is Immediate { Value: var leftMask })
                {
                    maskValue = leftMask;
                    maskOperand = instruction.Operands[2];
                }
                else if (instruction.Operands.Count == 3
                    && instruction.Operands[2] is Immediate { Value: var rightMask })
                {
                    maskValue = rightMask;
                    maskOperand = instruction.Operands[1];
                }
                else
                {
                    maskValue = 0;
                    maskOperand = null;
                }
                if (maskOperand != null
                    && TryBitMaskRun(maskValue, out var bitOffset, out var bitWidth)
                    && PackedOperandType(maskOperand, pointerSize) is { } masked)
                {
                    var packedSize = PackedSize(masked, pointerSize);
                    if (bitOffset == 0 && bitWidth >= 8 * packedSize)
                    {
                        // The mask keeps the whole packed value.
                        instruction.OpCode = OpCode.Move;
                        instruction.SetOperands(instruction.Destination!, maskOperand);
                        return true;
                    }
                    var maskByteWidth = (bitOffset + bitWidth + 7) / 8 - bitOffset / 8;
                    // An offset-zero read lands in the destination verbatim. When
                    // the destination stores no more than the mask's width - an
                    // untyped local takes the leaf's own type - the leaf's
                    // signedness never reaches a wider slot and any integral leaf
                    // spells the read. A wider destination would see the mask's
                    // zero extension, so there the leaf must be unsigned.
                    var destinationWidth = instruction.Destination switch
                    {
                        LocalVariable { Type: null } => -2,
                        LocalVariable { Type: { } slotType } =>
                            IlGenerator.IntegralStackWidth(slotType),
                        _ => -3,
                    };
                    if (SingleFieldSpanning(masked, bitOffset / 8, maskByteWidth,
                                pointerSize) is var (maskedField, maskedOffset)
                        && bitOffset == 8 * maskedOffset
                        && ResolvedFieldType(masked, null, maskedField) is { } maskedLeafType
                        && TypeSizes.MinimumUnboxedSize(maskedLeafType, pointerSize)
                                is var maskedLeafWidth
                        && maskedLeafWidth > 0
                        && bitWidth >= LeafBitWidth(maskedLeafType, pointerSize)
                        && ProjectOperand(maskOperand, masked, (int)maskedOffset,
                                (int)maskedLeafWidth, method, pointerSize,
                                MaskLeafKind(bitOffset, maskedLeafWidth,
                                    destinationWidth,
                                    LeafBitWidth(maskedLeafType, pointerSize)))
                                is var (field, _))
                    {
                        var destination = instruction.Destination!;
                        if (bitOffset == 0)
                        {
                            instruction.OpCode = OpCode.Move;
                            instruction.SetOperands(destination, field);
                            Retype(destination, field.Field.FieldType);
                        }
                        else
                        {
                            instruction.OpCode = OpCode.ShiftLeft;
                            instruction.SetOperands(destination, field,
                                new Immediate(bitOffset));
                            Retype(destination,
                                method.AppContext.SystemTypes.SystemInt64Type);
                        }
                        return true;
                    }
                    // A mask that covers no whole field can still sit inside the
                    // offset-0 leaf alone: the pack's bits at mask positions are
                    // that field's bits, so `packed & mask` spells `field & mask`
                    // verbatim - a bit test on the field keeps the And.
                    if (TopLevelLeafAt(masked, 0, pointerSize)
                            is var (lowField, lowFieldOffset, lowFieldSize)
                        && lowFieldOffset == 0
                        && bitOffset + bitWidth <= 8 * lowFieldSize
                        && ResolvedFieldType(masked, null, lowField) is { } lowLeafType
                        && TypeSizes.MinimumUnboxedSize(lowLeafType, pointerSize)
                                is var lowLeafWidth
                        && lowLeafWidth == lowFieldSize
                        && ProjectOperand(maskOperand, masked, 0, (int)lowLeafWidth,
                                method, pointerSize, LeafKind.Integral)
                            is var (lowLeaf, _))
                    {
                        instruction.SetOperand(ReferenceEquals(maskOperand, instruction.Operands[1]) ? 1 : 2, lowLeaf);
                        return true;
                    }
                    // Masked padding reads as zero; a mask over real field bits
                    // that is not a whole-field selection stays diagnosed.
                    if (!AnyFieldInRange(masked, bitOffset / 8, maskByteWidth,
                            pointerSize))
                    {
                        SetConstant(instruction, instruction.Destination!, 0);
                        return true;
                    }
                    return false;
                }
                goto default;

            default:
                return RewriteIntegerOperands(method, instruction, operandWidth, pointerSize);
        }
    }

    // Every remaining integer op reads the low `operandWidth` bytes of each source
    // (a ShiftLeft additionally drops the top bytes its count shifts out). A packed
    // operand whose whole read range is one field is replaced by that field; the
    // opcode stays and the emitted op is `field op rhs`.
    private static bool RewriteIntegerOperands(MethodAnalysisContext method,
        Instruction instruction, int operandWidth, int pointerSize)
    {
        var changed = false;
        for (var index = 1; index < instruction.Operands.Count; index++)
        {
            if (OperandReadRange(instruction, index, operandWidth) is not { } range
                || PackedOperandType(instruction.Operands[index], pointerSize) is not { } type
                || ProjectOperand(instruction.Operands[index], type, range.Offset, range.Width,
                    method, pointerSize, LeafKind.Integral) is not var (field, _))
                continue;
            instruction.SetOperand(index, field);
            changed = true;
        }

        // A shifted read can exceed the field's own width: the native result is the
        // register width, so a widened destination keeps the i8 contract.
        if (changed && instruction.OpCode == OpCode.ShiftLeft && operandWidth == 8
            && instruction.Destination is LocalVariable wideDestination)
            wideDestination.Type = method.AppContext.SystemTypes.SystemInt64Type;

        return changed;
    }

    private static (int Offset, int Width)? OperandReadRange(Instruction instruction,
        int operandIndex, int operandWidth)
        => instruction.OpCode switch
        {
            OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Modulo
                or OpCode.Or or OpCode.Xor or OpCode.And
                => operandIndex is 1 or 2 ? (0, operandWidth) : null,
            OpCode.ShiftLeft => operandIndex == 1
                ? (0, instruction.Operands[2] is Immediate { Value: var bits }
                    && bits >= 0 && bits % 8 == 0 && bits / 8 < operandWidth
                        ? operandWidth - (int)(bits / 8)
                        : operandWidth)
                : null,
            OpCode.Not or OpCode.Negate => operandIndex == 1 ? (0, operandWidth) : null,
            _ => null,
        };

    // `P >>`/`P &`/`ext(P)` rewrites collapse the whole instruction into a read of
    // the one field the byte range selects: `Move destination, field`.
    private static bool TryWholeRead(MethodAnalysisContext method, Instruction instruction,
        int offset, int width, int pointerSize, LeafKind leafKind)
    {
        var operand = instruction.Operands[1];
        if (PackedOperandType(operand, pointerSize) is not { } type)
            return false;
        if (ProjectOperand(operand, type, offset, width, method, pointerSize, leafKind)
                is not var (field, leafType))
            return false;

        instruction.OpCode = OpCode.Move;
        instruction.SetOperands(instruction.Destination!, field);
        Retype(instruction.Destination!, leafType);
        return true;
    }

    // Only an untyped destination adopts the leaf type. A typed local is left
    // alone: an addressed or shared local's declared type belongs to the whole
    // struct it stores, and the leaf's emitted stack type (small fields push
    // i32) coerces into it in the usual way.
    private static void Retype(IOperand destination, TypeAnalysisContext type)
    {
        if (destination is LocalVariable { Type: null } local)
            local.Type = type;
    }

    private static bool RewritePackedComparison(MethodAnalysisContext method,
        Instruction instruction, IReadOnlyDictionary<LocalVariable, Instruction> definitions,
        HashSet<Instruction> foldedSources, int pointerSize)
    {
        var relation = instruction.OpCode switch
        {
            OpCode.CheckEqual => Comparison.Equal,
            OpCode.CheckNotEqual => Comparison.NotEqual,
            OpCode.CheckLess => Comparison.Less,
            OpCode.CheckLessOrEqual => Comparison.LessOrEqual,
            OpCode.CheckGreater => Comparison.Greater,
            OpCode.CheckGreaterOrEqual => Comparison.GreaterOrEqual,
            _ => (Comparison?)null,
        };
        if (relation == null || instruction.Operands.Count != 3)
            return false;

        // `CheckX(t, 0)` on `t = P - K` (or `K - P`) is the flag pair for `P R K`.
        if (instruction.Operands[1] is LocalVariable temp
            && instruction.Operands[2] is Immediate { Value: 0 }
            && definitions.TryGetValue(temp, out var definition)
            && definition.OpCode == OpCode.Subtract && definition.Operands.Count == 3
            && !ReferenceEquals(definition, instruction))
        {
            var (operand, constant, swapped) = definition.Operands[1] is Immediate { Value: var left }
                ? (definition.Operands[2], left, true)
                : definition.Operands[2] is Immediate { Value: var right }
                    ? (definition.Operands[1], right, false)
                    : (null, 0L, false);
            if (operand != null
                && TryPackedCompare(method, instruction, operand,
                    Swap(relation.Value, swapped), constant, pointerSize))
            {
                foldedSources.Add(definition);
                return true;
            }
            return false;
        }

        if (instruction.Operands[2] is Immediate { Value: var bound }
            && TryPackedCompare(method, instruction, instruction.Operands[1], relation.Value,
                bound, pointerSize))
            return true;
        if (instruction.Operands[1] is Immediate { Value: var flipped }
            && TryPackedCompare(method, instruction, instruction.Operands[2],
                Swap(relation.Value, true), flipped, pointerSize))
            return true;
        return false;
    }

    private static Comparison Swap(Comparison relation, bool swapped)
        => swapped ? relation switch
        {
            Comparison.Less => Comparison.Greater,
            Comparison.Greater => Comparison.Less,
            Comparison.LessOrEqual => Comparison.GreaterOrEqual,
            Comparison.GreaterOrEqual => Comparison.LessOrEqual,
            _ => relation,
        } : relation;

    private static bool TryPackedCompare(MethodAnalysisContext method, Instruction instruction,
        IOperand packedOperand, Comparison relation, long constant, int pointerSize)
    {
        if (PackedOperandType(packedOperand, pointerSize) is not { } type)
            return false;
        var packedSize = PackedSize(type, pointerSize);
        if (packedSize <= 0)
            return false;

        if (relation is Comparison.Equal or Comparison.NotEqual)
            return TryPackedEquality(method, instruction, packedOperand, type, packedSize,
                relation == Comparison.NotEqual, constant, pointerSize);
        return TryPackedOrder(method, instruction, packedOperand, type, packedSize,
            relation, constant, pointerSize);
    }

    // `packed R k` for an ordering. Under 8 bytes the packed value is always
    // nonnegative, so signed and unsigned agree: `R` becomes `packed <= bound`
    // with `bound = k-1` for `<`/`>=`. Split at the bound's top byte w:
    // `packed <= bound` is `hi == 0 && lo <= bound`, and `hi` must name one field.
    private static bool TryPackedOrder(MethodAnalysisContext method, Instruction instruction,
        IOperand packedOperand, TypeAnalysisContext type, int packedSize,
        Comparison relation, long constant, int pointerSize)
    {
        if (packedSize >= 8 || instruction.Destination is not { } destination)
            return false;

        var bound = relation is Comparison.Less or Comparison.GreaterOrEqual
            ? constant - 1 : constant;
        var negate = relation is Comparison.GreaterOrEqual or Comparison.Greater;

        if (bound < 0)
        {
            SetConstant(instruction, destination, negate ? 1 : 0);
            return true;
        }

        var width = BytesNeeded(bound);
        if (width >= packedSize)
        {
            // The bound reaches the whole packed value: `packed <= bound` holds iff
            // the layout's maximum does not exceed it (an unbounded layout's maximum
            // is its byte width).
            if (PackedMaximum(type, packedSize, pointerSize) > bound)
                return false;
            SetConstant(instruction, destination, negate ? 0 : 1);
            return true;
        }

        var loMaximum = PackedMaximum(type, width, pointerSize);
        if (loMaximum > bound)
            return false;
        // `hi == 0`: the bytes above the bound are padding plus at most one
        // leaf field - the register's pad bytes are zero by construction, so
        // the check asks that leaf == 0.
        if (SingleFieldSpanning(type, width, packedSize - width, pointerSize)
                is not var (highField, highOffset))
            return false;
        if (ResolvedFieldType(type, null, highField) is not { } highLeafType
            || TypeSizes.MinimumUnboxedSize(highLeafType, pointerSize) is var highLeafWidth
                && highLeafWidth <= 0
            || ProjectOperand(packedOperand, type, (int)highOffset, (int)highLeafWidth,
                    method, pointerSize, LeafKind.Any) is not var (high, _))
            return false;

        instruction.OpCode = negate ? OpCode.CheckNotEqual : OpCode.CheckEqual;
        instruction.SetOperands(destination, high, new Immediate(0));
        return true;
    }

    // The single top-level field the bytes [offset, offset+width) cover, when every
    // non-padding byte belongs to it and it does not straddle the range's edge. A
    // field spanning the boundary is rejected: `field == 0` would also constrain the
    // low part the bound still allows.
    private static (FieldAnalysisContext Field, long Offset)? SingleFieldSpanning(
        TypeAnalysisContext type, int offset, int width, int pointerSize)
    {
        FieldAnalysisContext? found = null;
        long foundOffset = 0;
        for (var a = offset; a < offset + width; a++)
        {
            if (TopLevelLeafAt(type, a, pointerSize) is not var (field, fieldOffset, fieldSize))
                continue;
            if (found == null)
            {
                if (fieldOffset < offset || fieldOffset + fieldSize > offset + width)
                    return null;
                found = field;
                foundOffset = fieldOffset;
            }
            else if (!ReferenceEquals(found, field))
            {
                return null;
            }
        }
        return found == null ? null : (found, foundOffset);
    }

    // `packed == k` / `!= k`: out-of-range constants and constants a bounded field
    // can never hold fold to a constant; a one-field struct compares the field.
    private static bool TryPackedEquality(MethodAnalysisContext method, Instruction instruction,
        IOperand packedOperand, TypeAnalysisContext type, int packedSize,
        bool negate, long constant, int pointerSize)
    {
        var destination = instruction.Destination;
        if (destination == null)
            return false;

        var outOfRange = constant < 0
            || packedSize < 8 && constant >= (1L << (8 * packedSize));
        if (outOfRange || PackedContradictsConstant(type, constant, packedSize, pointerSize))
        {
            SetConstant(instruction, destination, negate ? 1 : 0);
            return true;
        }

        if (ProjectOperand(packedOperand, type, 0, packedSize, method, pointerSize,
                LeafKind.Any) is not var (single, _))
            return false;
        instruction.OpCode = negate ? OpCode.CheckNotEqual : OpCode.CheckEqual;
        instruction.SetOperands(destination, single, new Immediate(constant));
        return true;
    }

    private static void SetConstant(Instruction instruction, IOperand destination, int value)
    {
        instruction.OpCode = OpCode.Move;
        instruction.SetOperands(destination, new Immediate(value));
    }

    // A field path is admissible when the read range [offset, offset+width) is
    // exactly one leaf member of the layout and the leaf's emitted value is the
    // read's value under the given signedness. A reference leaf only names a null
    // test (LeafKind.Any on comparisons). The leaf's declared type resolves
    // through the operand's generic instances - `Nullable<T>.value` reads as
    // whatever `T` was instantiated to - and comes back beside the reference.
    private static (FieldReference Field, TypeAnalysisContext LeafType)? ProjectOperand(
        IOperand operand, TypeAnalysisContext type, int offset, int width,
        MethodAnalysisContext method, int pointerSize, LeafKind leafKind)
    {
        if (width <= 0)
            return null;
        if (MetadataResolver.FindInstanceFieldPathAtOffset(type, offset, width)
                is { Field: var exactLeaf, Containers: var containers })
        {
            // The whole read range is one leaf - the usual case.
            return ProjectLeaf(operand, type, offset, width, exactLeaf, containers,
                method, pointerSize, leafKind);
        }

        // A read wider than one leaf still spells it when every other byte in
        // the range is layout padding: the ABI writes those bytes zero, so the
        // read's value is the leaf's - `mov w8, packed` on `Nullable<int>`
        // reads `hasValue` because bytes 1-3 are padding before `value` at 4.
        // The value lands unsigned-extended (the padding, not the leaf,
        // provides the top bits), so a signed leaf's negative value would come
        // out wrong and stays diagnosed.
        if (SingleFieldSpanning(type, offset, width, pointerSize)
                is var (paddedLeaf, paddedOffset)
            && ResolvedFieldType(type, null, paddedLeaf) is { } paddedType
            && TypeSizes.MinimumUnboxedSize(paddedType, pointerSize) is var paddedWidth
            && paddedWidth > 0
            && IsUnsignedLeaf(paddedType)
            && LeafAdmissible(paddedType, leafKind))
            return ProjectLeaf(operand, type, (int)paddedOffset, (int)paddedWidth, paddedLeaf,
                null, method, pointerSize, leafKind);

        return null;
    }

    private static (FieldReference Field, TypeAnalysisContext LeafType)? ProjectLeaf(
        IOperand operand, TypeAnalysisContext type, int offset, int width,
        FieldAnalysisContext leaf, IReadOnlyList<FieldAnalysisContext>? containers,
        MethodAnalysisContext method, int pointerSize, LeafKind leafKind)
    {
        if (ResolvedFieldType(type, containers, leaf) is not { } leafType)
            return null;
        if (TypeSizes.MinimumUnboxedSize(leafType, pointerSize) != width)
            return null;
        if (!LeafAdmissible(leafType, leafKind))
            return null;

        var projected = operand switch
        {
            LocalVariable local => new FieldReference(leaf, local, offset, containers, width),
            FieldReference outer => new FieldReference(leaf, outer.Local,
                (int)(outer.Offset + offset),
                outer.Containers.Append(outer.Field)
                    .Concat(containers ?? []).ToList(), width),
            _ => null,
        };
        if (projected == null
            || MetadataResolver.MemberPathUnspellable((projected.Field, projected.Containers),
                method, store: false, addressed: false))
            return null;
        return (projected, leafType);
    }

    // The leaf admissibility a mask needs. An offset-zero mask is a plain read:
    // the destination stores it, so a slot no wider than the leaf - or one
    // retyped to the leaf's own type - never observes the mask's zero extension
    // and any integral leaf spells it. A wider slot sees the extension, so the
    // leaf must be unsigned there. A shifted mask emits `leaf << bitOffset`,
    // which sign-extends the leaf first: only a leaf whose bits reach bit 63
    // shifts its sign extension out of the i64 result - anything narrower must
    // be unsigned so no sign bits exist in the first place.
    private static LeafKind MaskLeafKind(int bitOffset, long leafWidth,
        int destinationWidth, long leafBits)
    {
        if (bitOffset == 0)
            return destinationWidth is -2 || (destinationWidth > 0 && destinationWidth <= leafWidth)
                ? LeafKind.Integral
                : LeafKind.Unsigned;
        return bitOffset + leafBits >= 64 ? LeafKind.Integral : LeafKind.Unsigned;
    }

    // The leaf's concrete type: a generic parameter declared on the packed type
    // (or on a generic-typed container in the path) takes that level's argument.
    private static TypeAnalysisContext? ResolvedFieldType(TypeAnalysisContext owner,
        IReadOnlyList<FieldAnalysisContext>? containers, FieldAnalysisContext leaf)
    {
        var declaring = owner;
        if (containers != null)
            foreach (var container in containers)
            {
                if (InstantiateFieldType(declaring, container) is not { } containerType)
                    return null;
                declaring = containerType;
            }
        return InstantiateFieldType(declaring, leaf);
    }

    private static TypeAnalysisContext? InstantiateFieldType(TypeAnalysisContext declaring,
        FieldAnalysisContext field)
    {
        if (declaring is not GenericInstanceTypeAnalysisContext instance)
            return ContainsGenericParameter(field.FieldType) ? null : field.FieldType;
        return HasUnresolvableParameter(field.FieldType, instance.GenericArguments.Count)
            ? null
            : GenericInstantiation.Instantiate(field.FieldType, instance.GenericArguments, []);
    }

    // A generic parameter the instance cannot bind: a method parameter (the
    // method's own arguments are unknown here) or a type index past the
    // instance's argument list. Anything containing one stays unresolved.
    private static bool HasUnresolvableParameter(TypeAnalysisContext type, int typeArguments,
        int depth = 0)
    {
        if (depth > 8)
            return true;
        var element = type switch
        {
            GenericParameterTypeAnalysisContext parameter =>
                parameter.Type != Il2CppTypeEnum.IL2CPP_TYPE_VAR || parameter.Index >= typeArguments
                    ? type : null,
            GenericInstanceTypeAnalysisContext instance =>
                instance.GenericArguments.Any(argument =>
                    HasUnresolvableParameter(argument, typeArguments, depth + 1)) ? type : null,
            SzArrayTypeAnalysisContext array => array.ElementType,
            ArrayTypeAnalysisContext array => array.ElementType,
            ByRefTypeAnalysisContext byRef => byRef.ElementType,
            PointerTypeAnalysisContext pointer => pointer.ElementType,
            PinnedTypeAnalysisContext pinned => pinned.ElementType,
            BoxedTypeAnalysisContext boxed => boxed.ElementType,
            CustomModifierTypeAnalysisContext modifier => modifier.ElementType,
            _ => null,
        };
        return ReferenceEquals(element, type)
            || element != null && HasUnresolvableParameter(element, typeArguments, depth + 1);
    }

    private static bool ContainsGenericParameter(TypeAnalysisContext type, int depth = 0)
        => depth <= 8 && type switch
        {
            GenericParameterTypeAnalysisContext => true,
            GenericInstanceTypeAnalysisContext instance =>
                instance.GenericArguments.Any(argument => ContainsGenericParameter(argument, depth + 1)),
            SzArrayTypeAnalysisContext array => ContainsGenericParameter(array.ElementType, depth + 1),
            ArrayTypeAnalysisContext array => ContainsGenericParameter(array.ElementType, depth + 1),
            ByRefTypeAnalysisContext byRef => ContainsGenericParameter(byRef.ElementType, depth + 1),
            PointerTypeAnalysisContext pointer => ContainsGenericParameter(pointer.ElementType, depth + 1),
            PinnedTypeAnalysisContext pinned => ContainsGenericParameter(pinned.ElementType, depth + 1),
            BoxedTypeAnalysisContext boxed => ContainsGenericParameter(boxed.ElementType, depth + 1),
            CustomModifierTypeAnalysisContext modifier => ContainsGenericParameter(modifier.ElementType, depth + 1),
            _ => false,
        };

    private static bool LeafAdmissible(TypeAnalysisContext leafType, LeafKind leafKind)
        => leafKind switch
        {
            LeafKind.Any => IlGenerator.IntegralStackWidth(leafType) != 0 || !leafType.IsValueType,
            LeafKind.Integral => IlGenerator.IntegralStackWidth(leafType) != 0,
            // The destination takes the leaf's own type, so the read is the field's
            // value no matter its kind; an unresolved generic parameter is not a leaf.
            LeafKind.Whole => leafType is not (GenericParameterTypeAnalysisContext
                or ByRefTypeAnalysisContext or PointerTypeAnalysisContext),
            LeafKind.Unsigned => IlGenerator.IntegralStackWidth(leafType) != 0
                && IsUnsignedLeaf(leafType),
            LeafKind.Signed => IlGenerator.IntegralStackWidth(leafType) != 0
                && (!IsUnsignedLeaf(leafType) || leafType.FullName == "System.Boolean"),
            _ => false,
        };

    private static bool IsUnsignedLeaf(TypeAnalysisContext type)
        => type.FullName is "System.Boolean" or "System.Byte" or "System.Char"
            or "System.UInt16" or "System.UInt32" or "System.UInt64" or "System.UIntPtr"
            || type is { IsEnumType: true, DefaultEnumUnderlyingType: { } underlying }
                && IsUnsignedLeaf(underlying);

    // The operand is a small struct in an integer register: a value type with no
    // integral stack spelling of its own, on an integer (not vector) register.
    private static TypeAnalysisContext? PackedOperandType(IOperand operand, int pointerSize)
    {
        var type = operand switch
        {
            LocalVariable { Type: { } localType } => localType,
            FieldReference { Field.FieldType: { } fieldType } => fieldType,
            _ => null,
        };
        if (type is null or not { IsValueType: true }
            or ByRefTypeAnalysisContext or PointerTypeAnalysisContext
            or GenericParameterTypeAnalysisContext
            || IlGenerator.IntegralStackWidth(type) != 0)
            return null;
        var register = operand switch
        {
            LocalVariable local => local.Register.Name,
            FieldReference field => field.Local.Register.Name,
            _ => null,
        };
        if (register != null && register.StartsWith("TEMP_VEC", StringComparison.Ordinal)
            || register is { Length: > 1 } && register[0] == 'V' && char.IsDigit(register[1]))
            return null;
        return type;
    }

    private static int PackedSize(TypeAnalysisContext type, int pointerSize)
    {
        var size = TypeSizes.LaidOutSize(type, pointerSize);
        return size <= 0 ? 0 : (int)Math.Min(size, 8);
    }

    // The largest value the low `bytes` of the packed value can hold when every
    // byte is known to sit inside a Boolean field (each contributes at most 1 at
    // its position); an unbounded byte falls back to the width's own maximum.
    private static long PackedMaximum(TypeAnalysisContext type, int bytes, int pointerSize)
    {
        var maximum = 0L;
        var bounded = true;
        for (var a = 0; a < bytes; a++)
        {
            if (LeafAt(type, a, pointerSize) is var (leaf, containers)
                && ResolvedFieldType(type, containers, leaf) is { FullName: "System.Boolean" })
                maximum += 1L << (8 * a);
            else
            {
                bounded = false;
                break;
            }
        }
        return bounded ? maximum : (1L << (8 * bytes)) - 1;
    }

    // `packed == k` is provably false when a Boolean-covered byte of `k` demands
    // a value greater than 1.
    private static bool PackedContradictsConstant(TypeAnalysisContext type, long constant,
        int packedSize, int pointerSize)
    {
        for (var a = 0; a < packedSize; a++)
            if (LeafAt(type, a, pointerSize) is var (leaf, containers)
                && ResolvedFieldType(type, containers, leaf) is { FullName: "System.Boolean" }
                && ((constant >> (8 * a)) & 0xFF) > 1)
                return true;
        return false;
    }

    // The top-level member covering a byte of the layout, with the range it
    // occupies; generic instances take the recomputed layout.
    private static (FieldAnalysisContext Field, long Offset, long Size)? TopLevelLeafAt(
        TypeAnalysisContext type, long byteOffset, int pointerSize)
    {
        if (type is GenericInstanceTypeAnalysisContext instance)
            return GenericInstanceFieldLayout.FindFieldContainingOffset(instance, byteOffset);
        foreach (var field in type.Fields)
        {
            if (field.IsStatic || (field.Attributes & FieldAttributes.Literal) != 0)
                continue;
            var fieldOffset = field.BackingData?.FieldOffset ?? field.Offset;
            var fieldSize = TypeSizes.MinimumUnboxedSize(field.FieldType, pointerSize);
            if (fieldSize > 0 && byteOffset >= fieldOffset && byteOffset < fieldOffset + fieldSize)
                return (field, fieldOffset, fieldSize);
        }
        return null;
    }

    // The leaf member covering a byte of the layout, with the fields traversed
    // to reach it: descends through struct-typed fields; a primitive, enum or
    // reference member is the leaf.
    private static (FieldAnalysisContext Field, List<FieldAnalysisContext> Containers)? LeafAt(
        TypeAnalysisContext type, long byteOffset, int pointerSize)
    {
        var path = new List<FieldAnalysisContext>();
        var declaring = type;
        for (var depth = 0; depth <= 4; depth++)
        {
            if (TopLevelLeafAt(declaring, byteOffset, pointerSize)
                    is not var (containing, containingOffset, _))
                return null;

            path.Add(containing);
            if (InstantiateFieldType(declaring, containing) is not { } fieldType
                || !fieldType.IsValueType || IlGenerator.IntegralStackWidth(fieldType) != 0
                || fieldType.FullName is "System.Single" or "System.Double"
                || TypeSizes.MinimumUnboxedSize(fieldType, pointerSize) <= 0)
                return (containing, path.Count > 1 ? path.GetRange(0, path.Count - 1) : []);
            declaring = fieldType;
            byteOffset -= containingOffset;
        }
        return null;
    }

    // A run of contiguous set bits: `0xFF00` selects bits 8-15, `0x100` bit 8,
    // `-1` the whole register; anything with a gap is not a field selection.
    private static bool TryBitMaskRun(long value, out int offset, out int width)
    {
        offset = 0;
        width = 0;
        var mask = unchecked((ulong)value);
        if (mask == 0)
            return false;
        while ((mask & 1) == 0)
        {
            mask >>= 1;
            offset++;
        }
        while ((mask & 1) == 1)
        {
            mask >>= 1;
            width++;
        }
        return mask == 0;
    }

    // The meaningful bits of a leaf: a bool occupies only its low bit, every
    // other leaf all of its stored bits. A mask keeping fewer than this many of
    // the leaf's low bits is a bit test the field read cannot spell.
    private static int LeafBitWidth(TypeAnalysisContext leafType, int pointerSize)
    {
        if (leafType is { IsEnumType: true, DefaultEnumUnderlyingType: { } underlying })
            return LeafBitWidth(underlying, pointerSize);
        return leafType.FullName == "System.Boolean"
            ? 1
            : 8 * Math.Max(0, (int)TypeSizes.MinimumUnboxedSize(leafType, pointerSize));
    }

    private static bool AnyFieldInRange(TypeAnalysisContext type, int offset, int width,
        int pointerSize)
    {
        for (var a = offset; a < offset + width; a++)
            if (TopLevelLeafAt(type, a, pointerSize) != null)
                return true;
        return false;
    }

    private static int BytesNeeded(long bound)
    {
        if (bound <= 0)
            return 0;
        var bytes = 0;
        for (var value = bound; value > 0; value >>= 8)
            bytes++;
        return bytes;
    }
}
