using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.Utils;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Recovers ARM64 ELF block-memory imports - `memcpy`, `memset`, `memmove` - whose call
/// sites stay unresolved by the normal resolvers. A `bl` into a linker GOT veneer
/// (adrp; ldr; [add]; br) loads a pointer slot whose dynamic relocation names the
/// import; that relocated symbol plus the raw ABI argument layout are the only
/// evidence used. No fixed addresses, no game-specific tokens.
///
/// The pass runs at the end of method analysis, after SSA removal and copy forwarding,
/// so the operands it inspects are the ones emission will see - a call rewritten here
/// cannot drift into an unprovable shape later.
///
/// The rewrite commits only when the destination operand provably denotes a region
/// that cannot hold managed references: cpblk/initblk emit no GC write barriers, so a
/// destination that could carry reference slots must stay an unresolved call and keep
/// its diagnostic rather than silently skip the barriers a managed store would need.
/// The returned dst pointer is preserved as a native int only when the lifted result
/// local is still read and can legally hold a native int.
/// </summary>
public static class BlockMemoryImportRecovery
{
    private static readonly string? DiagnosticsPath =
        Environment.GetEnvironmentVariable("CPP2IL_BLOCKMEM_DIAG");
    private static readonly object DiagnosticsLock = new();

    public static void Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet)
            return;

        var binary = method.AppContext.Binary;
        var unresolvedOther = 0;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Call || instruction.Operands[0] is not Immediate target)
                continue;

            var name = ResolveImportName(binary, target.UnsignedValue);
            if (name is not ("memcpy" or "memset" or "memmove"))
            {
                if (DiagnosticsPath != null && name != null)
                    Record(method, instruction, target.UnsignedValue, name, "other-import", "");
                else
                    unresolvedOther++;
                continue;
            }

            var rewritten = TryRewriteCall(method, instruction, name, out var detail);
            if (DiagnosticsPath != null)
                Record(method, instruction, target.UnsignedValue, name,
                    rewritten ? "rewritten" : "rejected", detail);
        }
        if (DiagnosticsPath != null && unresolvedOther > 0)
            lock (DiagnosticsLock)
                System.IO.File.AppendAllText(DiagnosticsPath,
                    $"other\t{method.UnderlyingPointer:x}\t-\t-\tunresolved-call\t{unresolvedOther}\n");
    }

    private static void Record(MethodAnalysisContext method, Instruction instruction, ulong target,
        string name, string outcome, string detail)
    {
        lock (DiagnosticsLock)
            System.IO.File.AppendAllText(DiagnosticsPath!,
                $"{method.UnderlyingPointer:x}\t{instruction.Index}\t{target:x}\t{name}\t{outcome}\t{detail}\n");
    }

    private static string Describe(IOperand? operand, MethodAnalysisContext method)
    {
        if (operand is null)
            return "-";
        var type = operand switch
        {
            LocalVariable local => $"{local.Type?.FullName ?? "untyped"}|{IlGenerator.EmittedOperandType(operand, method)?.FullName ?? "noemit"}|def={DescribeDef(local, method)}",
            _ => $"{IlGenerator.EmittedOperandType(operand, method)?.FullName ?? "noemit"}",
        };
        return $"{operand.GetType().Name}({type})";
    }

    private static string DescribeDef(LocalVariable local, MethodAnalysisContext method)
    {
        var defs = method.ControlFlowGraph!.Instructions
            .Where(i => ReferenceEquals(i.Destination, local))
            .Select(i => $"{i.OpCode}[{string.Join(",", i.Sources.Select(s => s is LocalVariable l ? $"L:{l.Type?.FullName ?? "?"}" : s.GetType().Name))}]")
            .ToList();
        return defs.Count == 0 ? "none" : string.Join("+", defs);
    }

    // Resolves a call target that is a GOT veneer to the relocated symbol name on the
    // pointer slot its ldr reads - e.g. "memcpy" for `bl memcpy@plt`. Returns null for
    // any other shape: direct calls, unresolved stubs, relocations to other symbols.
    private static string? ResolveImportName(Il2CppBinary binary, ulong target)
    {
        if (!NewArm64KeyFunctionAddresses.TryDecodeGotVeneerSlot(target, ReadWord, out var slot))
            return null;
        return binary.TryGetRelocatedSymbolNameAtPointerSlot(slot, out var name) ? name : null;

        uint? ReadWord(ulong va)
        {
            if (!binary.TryMapVirtualAddressToRaw(va, out var raw) || raw < 0 || raw + 4 > binary.RawLength)
                return null;
            return BitConverter.ToUInt32(binary.GetRawBinaryContent().Slice((int)raw, 4).ToArray(), 0);
        }
    }

    // Rewrites an unresolved Call to the matching block op when the operand proofs
    // below hold. A Call carrying an Immediate target was lifted with the raw ABI
    // operand layout and can never have been remapped - only resolved
    // MethodAnalysisContext targets go through RemapRawArguments - so operands 2..4
    // are still the X0..X2 argument slots positionally. Returns false when any
    // evidence is missing - the call keeps its unresolved diagnostic instead.
    internal static bool TryRewriteCall(MethodAnalysisContext method, Instruction call, string? importName)
        => TryRewriteCall(method, call, importName, out _);

    internal static bool TryRewriteCall(MethodAnalysisContext method, Instruction call, string? importName,
        out string detail)
    {
        detail = "";
        var opcode = importName switch
        {
            "memcpy" => OpCode.MemoryCopy,
            "memset" => OpCode.MemorySet,
            "memmove" => OpCode.MemoryMove,
            _ => OpCode.Invalid,
        };
        if (opcode == OpCode.Invalid)
        {
            detail = "not-import";
            return false;
        }

        if (call.OpCode != OpCode.Call
            || call.Operands.Count < 5
            || call.Operands[0] is not Immediate)
        {
            detail = $"shape:op={call.OpCode} count={call.Operands.Count}";
            return false;
        }

        var destination = call.Operands[2];
        var content = call.Operands[3];
        var count = call.Operands[4];

        // Raw block ops write bytes without write barriers, so the destination's region
        // must provably hold no managed references. memset's fill byte and every size
        // argument need an integral shape; a memcpy/memmove source only has to produce
        // a pointer - reading a managed region through it needs no barrier.
        if (!IsProvablyReferenceFreeRegion(destination, count, method, []))
        {
            detail = $"dst={Describe(destination, method)}";
            return false;
        }
        if (!IsScalarOperand(count, method))
        {
            detail = $"count={Describe(count, method)}";
            return false;
        }
        if (opcode == OpCode.MemorySet
                ? !IsScalarOperand(content, method)
                : !IsPointerOperandRepresentable(content, method))
        {
            detail = $"content={Describe(content, method)}";
            return false;
        }

        var result = call.Operands[1] as LocalVariable;
        if (result != null && method.ControlFlowGraph!.Instructions
                .Any(consumer => consumer.Sources.Contains(result)))
        {
            if (!CanMaterializeReturn(result, method))
            {
                detail = $"result={Describe(result, method)}";
                return false;
            }

            // The native functions return dst: materialize it as a native int so the
            // result keeps a pointer value no matter what the destination operand was.
            call.SetOperands(destination, content, count, result);
        }
        else
            call.SetOperands(destination, content, count);

        call.OpCode = opcode;
        detail = $"dst={Describe(destination, method)} src={Describe(content, method)} n={Describe(count, method)}";
        return true;
    }

    /// <summary>
    /// Whether the operand can be loaded as a pointer-shaped stack value (&, *, native
    /// int, an integral address literal, or a concrete managed reference - conv.u on an
    /// O value is unverifiable but produces the object's address, matching the native
    /// pointer the register held). Used for memcpy/memmove sources: reading a region
    /// through cpblk needs no barrier, only representability. System.Object-typed and
    /// generic values are rejected: an untyped local may legally hold a boxed
    /// integer, for which conv.u yields the box's address instead of the value.
    /// </summary>
    internal static bool IsPointerOperandRepresentable(IOperand operand, MethodAnalysisContext context) =>
        operand is Immediate
        || IlGenerator.EmittedOperandType(operand, context) is { } emitted
            && (IlGenerator.IntegralStackWidth(emitted) != 0
                || emitted is { IsValueType: false }
                    and not GenericParameterTypeAnalysisContext
                    && emitted.FullName != "System.Object");

    /// <summary>
    /// Whether the operand emits as an integral value suitable for a byte count or a
    /// memset fill byte. Pointers and managed pointers are rejected even though they
    /// share the native-int width: a pointer in a count slot is never the ABI's intent.
    /// </summary>
    internal static bool IsScalarOperand(IOperand operand, MethodAnalysisContext context)
    {
        if (operand is Immediate)
            return true;
        var emitted = IlGenerator.EmittedOperandType(operand, context);
        return emitted is not (null or PointerTypeAnalysisContext or ByRefTypeAnalysisContext)
            && IlGenerator.IntegralStackWidth(emitted) != 0;
    }

    /// <summary>
    /// Whether the operand provably addresses a region containing no managed reference
    /// slots, so raw byte stores into it cannot bypass GC write barriers. Managed
    /// pointer and unmanaged pointer values qualify through their element type or
    /// unmanaged contract; integral locals must trace every definition back to a
    /// proven pointer source; managed references address the object itself and are
    /// bounded to a field span checked byte for byte.
    /// </summary>
    internal static bool IsProvablyReferenceFreeRegion(IOperand operand, IOperand count,
        MethodAnalysisContext context) =>
        IsProvablyReferenceFreeRegion(operand, count, context, []);

    private static bool IsProvablyReferenceFreeRegion(IOperand operand, IOperand count,
        MethodAnalysisContext context, HashSet<LocalVariable> visiting)
    {
        switch (operand)
        {
            case Immediate:
                return true;
            case AddressOf { Target: LocalVariable local }:
                return IsReferenceFree(IlGenerator.EmittedLocalType(local, context));
            case AddressOf { Target: FieldReference field }:
                return IsReferenceFree(field.Field.FieldType);
            case AddressOf { Target: ArrayAccess access }:
                return access.Array.Type is SzArrayTypeAnalysisContext array
                    && IsReferenceFree(array.ElementType);
            case AddressOf { Target: ArrayElementFieldReference elementField }:
                return IsReferenceFree(elementField.Field.FieldType);
            case AddressOf:
                return false;
            case LocalVariable local:
                return IlGenerator.EmittedOperandType(local, context) switch
                {
                    PointerTypeAnalysisContext pointer => IsReferenceFree(pointer.ElementType),
                    ByRefTypeAnalysisContext byRef => IsReferenceFree(byRef.ElementType),
                    // IntPtr, native handles: unmanaged pointer values by contract.
                    { } t when IlGenerator.IntegralStackWidth(t) == -1 => true,
                    // An integral register is only a pointer if its producers prove one.
                    { } t when IlGenerator.IntegralStackWidth(t) > 0 =>
                        HasUnmanagedProvenance(local, count, context, visiting),
                    // A managed reference converts to the object's base address.
                    { IsValueType: false } t when t.FullName != "System.Object"
                        && t is not GenericParameterTypeAnalysisContext =>
                        t is SzArrayTypeAnalysisContext dstArray
                            ? IsReferenceFree(dstArray.ElementType)
                            : ManagedRegionRefFree(t, 0, count, context),
                    // Untyped/object-typed: provable only when every definition stores a
                    // real reference (never a boxed integer) into a provable region.
                    _ => HasManagedReferenceProvenance(local, 0, count, context, visiting),
                };
            case FieldReference field:
                // A field's value used directly as the address. The referent region is
                // whatever the field's declared type describes; an integral field
                // cannot be traced to a referent, so it is unproven.
                return field.Field.FieldType switch
                {
                    PointerTypeAnalysisContext pointer => IsReferenceFree(pointer.ElementType),
                    ByRefTypeAnalysisContext byRef => IsReferenceFree(byRef.ElementType),
                    { } t when IlGenerator.IntegralStackWidth(t) == -1 => true,
                    { IsValueType: false } t when t.FullName != "System.Object"
                        && t is not GenericParameterTypeAnalysisContext =>
                        t is SzArrayTypeAnalysisContext dstArray
                            ? IsReferenceFree(dstArray.ElementType)
                            : ManagedRegionRefFree(t, 0, count, context),
                    _ => false,
                };
            default:
                return false;
        }
    }

    // The destinations a still-integral local can be loaded from: every definition
    // must produce a pointer value into a provably reference-free region.
    private static bool HasUnmanagedProvenance(LocalVariable local, IOperand count,
        MethodAnalysisContext context, HashSet<LocalVariable> visiting)
    {
        if (!visiting.Add(local))
            return false;
        try
        {
            var defs = context.ControlFlowGraph!.Instructions
                .Where(i => ReferenceEquals(i.Destination, local)).ToList();
            return defs.Count != 0 && defs.All(def => def.OpCode switch
            {
                OpCode.Move or OpCode.Phi or OpCode.SignExtend32 =>
                    def.Sources.All(s => IsProvablyReferenceFreeRegion(s, count, context, visiting)),
                OpCode.Add or OpCode.Subtract =>
                    ProvableOffsetPointer(def.Operands[1], def.Operands[2],
                        def.OpCode == OpCode.Subtract, count, context, visiting),
                OpCode.Call => ProvableCallReturn(def),
                _ => false,
            });
        }
        finally
        {
            visiting.Remove(local);
        }
    }

    // A call result used as a destination: provable when the callee's return type is
    // an unmanaged pointer contract (IntPtr, or T* into reference-free memory).
    private static bool ProvableCallReturn(Instruction def) =>
        def.Operands[0] is MethodAnalysisContext callee
        && callee.ReturnType is { } returnType
        && (returnType is PointerTypeAnalysisContext pointer
                ? IsReferenceFree(pointer.ElementType)
                : returnType is ByRefTypeAnalysisContext byRef
                    ? IsReferenceFree(byRef.ElementType)
                    : IlGenerator.IntegralStackWidth(returnType) == -1);

    // A `base ± offset` destination: the provenance of the region the offset lands in.
    // Managed bases resolve through the field/array layout at that offset; unmanaged
    // bases stay in whatever region the base already proved.
    private static bool ProvableOffsetPointer(IOperand baseOperand, IOperand offsetOperand,
        bool negated, IOperand count, MethodAnalysisContext context, HashSet<LocalVariable> visiting)
    {
        long? offset = offsetOperand is Immediate imm
            ? negated ? -(long)imm.UnsignedValue : (long)imm.UnsignedValue
            : null;

        switch (baseOperand)
        {
            case Immediate:
                return true;
            case AddressOf { Target: LocalVariable local }:
                return offset is { } o1
                    && ManagedRegionRefFree(IlGenerator.EmittedLocalType(local, context), o1, count, context);
            case AddressOf { Target: FieldReference field }:
                return offset is { } o2
                    && ManagedRegionRefFree(field.Field.FieldType, o2, count, context);
            case AddressOf { Target: ArrayAccess access }:
                return access.Array.Type is SzArrayTypeAnalysisContext addressedArray
                    && IsReferenceFree(addressedArray.ElementType);
            case AddressOf:
                return false;
            case LocalVariable baseLocal:
                switch (IlGenerator.EmittedOperandType(baseLocal, context))
                {
                    case PointerTypeAnalysisContext pointer:
                        return IsReferenceFree(pointer.ElementType);
                    case ByRefTypeAnalysisContext byRef:
                        return IsReferenceFree(byRef.ElementType);
                    case { } t when IlGenerator.IntegralStackWidth(t) == -1:
                        return true;
                    case { } t when IlGenerator.IntegralStackWidth(t) > 0:
                        return HasUnmanagedProvenance(baseLocal, count, context, visiting);
                    case SzArrayTypeAnalysisContext array:
                        // Elements are homogeneous: an offset past the object header
                        // stays inside reference-free elements.
                        return offset is { } o3
                            && o3 >= 4L * context.AppContext.Binary.PointerSizeBytes
                            && IsReferenceFree(array.ElementType);
                    case { IsValueType: false } t when t.FullName != "System.Object"
                        && t is not GenericParameterTypeAnalysisContext:
                        return offset is { } o4
                            && ManagedRegionRefFree(t, o4, count, context);
                    default:
                        // Untyped base + offset: prove through the defs' managed
                        // sources at the same offset.
                        return offset is { } o5
                            && HasManagedReferenceProvenance(baseLocal, o5, count, context, visiting);
                }
            default:
                return false;
        }
    }

    // Every definition of this local must store a managed reference (not a boxed
    // integer - box would make conv.u read the box header instead of the value)
    // whose declared type's storage at `offset` is reference-free.
    private static bool HasManagedReferenceProvenance(LocalVariable local, long offset,
        IOperand count, MethodAnalysisContext context, HashSet<LocalVariable> visiting)
    {
        if (!visiting.Add(local))
            return false;
        try
        {
            var defs = context.ControlFlowGraph!.Instructions
                .Where(i => ReferenceEquals(i.Destination, local)).ToList();
            if (defs.Count == 0)
                return false;
            return defs.All(def => def.OpCode switch
            {
                OpCode.Move or OpCode.Phi => def.Sources.All(source =>
                    source is LocalVariable sourceLocal
                    && IlGenerator.EmittedOperandType(sourceLocal, context) is { } sourceType
                    && sourceType is { IsValueType: false }
                        and not GenericParameterTypeAnalysisContext
                        and not SzArrayTypeAnalysisContext
                    && sourceType.FullName != "System.Object"
                    && ManagedRegionRefFree(sourceType, offset, count, context)),
                OpCode.Call => def.Operands[0] is MethodAnalysisContext callee
                    && callee.ReturnType is { IsValueType: false } returnType
                    && returnType.FullName != "System.Object"
                    && returnType is not GenericParameterTypeAnalysisContext
                    && ManagedRegionRefFree(returnType, offset, count, context),
                OpCode.Newobj => def.Operands[1] is TypeAnalysisContext constructed
                    && constructed is { IsValueType: false }
                    && ManagedRegionRefFree(constructed, offset, count, context),
                _ => false,
            });
        }
        finally
        {
            visiting.Remove(local);
        }
    }

    // Whether the byte range [offset, offset+n) inside `owner`'s instance layout is
    // provably free of managed reference slots. Requires an immediate byte count:
    // every intersecting field must be reference-free, and the range may not extend
    // past the owner's declared instance size (past it sits unknown heap, which may
    // hold references). Header and padding gaps count as opaque non-reference bytes.
    private static bool ManagedRegionRefFree(TypeAnalysisContext owner, long offset,
        IOperand countOperand, MethodAnalysisContext context)
    {
        if (owner == null || countOperand is not Immediate count)
            return false;
        var length = (long)count.UnsignedValue;
        if (offset < 0 || length < 0)
            return false;
        var end = offset + length;
        if (end < offset)
            return false;

        var pointerSize = context.AppContext.Binary.PointerSizeBytes;
        var position = offset;
        for (var guard = 0; position < end && guard < 512; guard++)
        {
            // The field starting exactly here, or the one containing this offset.
            var field = MetadataResolver.FindInstanceFieldAtOffset(owner, position);
            var fieldSize = field != null ? FieldStorageSize(field, pointerSize) : 0;
            if (field == null)
            {
                foreach (var candidate in InstanceFields(owner).Where(f => FieldOffset(f) < position))
                {
                    var span = FieldStorageSize(candidate, pointerSize);
                    if (span <= 0)
                        // A field of unknowable extent started earlier - it may
                        // contain this offset, so the region cannot be bounded.
                        return false;
                    if (position < FieldOffset(candidate) + span)
                    {
                        field = candidate;
                        fieldSize = FieldOffset(candidate) + span - position;
                        break;
                    }
                }
            }
            if (field != null)
            {
                if (!IsReferenceFree(field.FieldType))
                    return false;
                position += fieldSize;
                continue;
            }
            // Header or padding: opaque bytes, skip to the next declared field.
            var next = InstanceFields(owner)
                .Select(f => (long)FieldOffset(f))
                .Where(o => o > position)
                .OrderBy(o => o)
                .Cast<long?>()
                .FirstOrDefault();
            if (next is { } nextOffset)
            {
                position = nextOffset;
                continue;
            }
            // No further declared fields: the range must stay inside the object's
            // declared instance size, which metadata provides for real types.
            var bound = InstanceDataSize(owner, pointerSize);
            return bound > 0 && end <= bound;
        }
        return position >= end;
    }

    private static IEnumerable<FieldAnalysisContext> InstanceFields(TypeAnalysisContext owner)
    {
        for (var candidate = owner; candidate != null; candidate = candidate.BaseType)
            foreach (var field in candidate.Fields.Where(field =>
                    !field.IsStatic && (field.Attributes & FieldAttributes.Literal) == 0))
                yield return field;
    }

    private static long FieldOffset(FieldAnalysisContext field) =>
        field.BackingData?.FieldOffset ?? field.Offset;

    private static long FieldStorageSize(FieldAnalysisContext field, int pointerSize)
    {
        var type = field.FieldType;
        if (type == null)
            return 0;
        if (!type.IsValueType || type is PointerTypeAnalysisContext or ByRefTypeAnalysisContext)
            return pointerSize;
        if (type.IsEnumType && type.EnumUnderlyingType is { } underlying)
            type = underlying;
        return TypeSizes.MinimumUnboxedSize(type, pointerSize);
    }

    // Declared instance size: for reference types the metadata's instance_size is the
    // boxed object size; for value types the unboxed field extent.
    private static long InstanceDataSize(TypeAnalysisContext owner, int pointerSize)
    {
        var definition = owner.Definition
            ?? (owner as GenericInstanceTypeAnalysisContext)?.GenericType.Definition;
        var raw = definition?.RawSizes.instance_size ?? 0;
        return owner.IsValueType ? Math.Max(0, raw - 2L * pointerSize) : raw;
    }

    // Whether a lifted result local can receive the returned dst pointer: the local's
    // declared type must accept a native-int store (or be unclaimed, in which case it
    // takes the native-int type). Reference/object slots cannot - boxing an address
    // would lose the value - so the rewrite refuses rather than drop the write.
    private static bool CanMaterializeReturn(LocalVariable result, MethodAnalysisContext context)
    {
        if (result.Type == null)
        {
            result.Type = context.AppContext.SystemTypes.SystemIntPtrType;
            return true;
        }
        var emitted = IlGenerator.EmittedOperandType(result, context);
        return emitted != null && IlGenerator.IntegralStackWidth(emitted) != 0;
    }

    // Reference-free means the type's storage provably contains no managed object
    // references: primitives and enums qualify trivially, unmanaged pointers and
    // byrefs count as opaque bytes, and a value type qualifies when every instance
    // field does. Generic parameters are never proven - T can be a reference type.
    private static bool IsReferenceFree(TypeAnalysisContext? type) =>
        IsReferenceFree(type, []);

    private static bool IsReferenceFree(TypeAnalysisContext? type, HashSet<TypeAnalysisContext> visited)
    {
        if (type == null)
            return false;
        // Revisited is fine: a value type cannot contain a by-value cycle, so the
        // only repeat is the primitive's own m_value self-field or a substructure
        // already proven elsewhere. A live `All` walk never reaches a revisit after
        // a proven-false verdict - it short-circuits first.
        if (!visited.Add(type))
            return true;
        if (type is PointerTypeAnalysisContext or ByRefTypeAnalysisContext)
            return true;
        if (type is GenericParameterTypeAnalysisContext)
            return false;
        if (type.FullName == "System.Void")
            return true;
        if (!type.IsValueType)
            return false;
        return type.Fields.Where(field => !field.IsStatic)
            .All(field => field.FieldType != null && IsReferenceFree(field.FieldType, visited));
    }
}
