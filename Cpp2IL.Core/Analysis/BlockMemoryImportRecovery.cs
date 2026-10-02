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
/// Recovers ARM64 ELF imports whose call sites stay unresolved by the normal
/// resolvers. A `bl` into a linker GOT veneer (adrp; ldr; [add]; br) loads a
/// pointer slot whose dynamic relocation names the import; that relocated symbol
/// plus the raw ABI argument layout are the only evidence used. No fixed
/// addresses, no game-specific tokens.
///
/// The pass runs at the end of method analysis, after SSA removal and copy
/// forwarding, so the operands it inspects are the ones emission will see - a
/// call rewritten here cannot drift into an unprovable shape later.
///
/// Every resolved import gets its name, so an unproven use stays diagnosed as
/// `Unknown call target operand: "memcpy"` rather than an anonymous address.
/// `memcpy`/`memset`/`memmove` become block ops when the destination operand
/// provably denotes a region that cannot hold managed references: cpblk/initblk
/// emit no GC write barriers, so a destination that could carry reference slots
/// must stay a named call rather than silently skip the barriers a managed store
/// would need. `modf`/`modff`/`sincos`/`sincosf` become their managed math
/// equivalents plus a store through the out pointer, only when the out pointer
/// provably targets a managed store destination. The returned dst pointer is
/// preserved as a native int only when the lifted result local is still read and
/// can legally hold a native int.
/// </summary>
public static class BlockMemoryImportRecovery
{
    private static readonly string? DiagnosticsPath =
        Environment.GetEnvironmentVariable("CPP2IL_BLOCKMEM_DIAG");
    private static readonly object DiagnosticsLock = new();

    public static void Run(MethodAnalysisContext method) => Run(method, null);

    internal static void Run(MethodAnalysisContext method, Func<ulong, string?>? importNameResolver)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet)
            return;

        var binary = method.AppContext.Binary;
        var imports = new List<(Instruction Call, string Name)>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (!instruction.IsCall)
                continue;
            var name = instruction.Operands[0] switch
            {
                Immediate target => importNameResolver != null
                    ? importNameResolver(target.UnsignedValue)
                    : ResolveImportName(binary, target.UnsignedValue),
                StringLiteral { Value: { Length: > 0 } value } => value,
                _ => null,
            };
            if (name != null)
                imports.Add((instruction, name));
        }

        TypeCopiedFrameSlots(method, imports);

        var unresolvedOther = 0;
        foreach (var (instruction, name) in imports)
        {
            ulong? immediateTarget = instruction.Operands[0] is Immediate target
                ? target.UnsignedValue
                : null;

            var detail = "";
            var rewritten = name is "memcpy" or "memset" or "memmove"
                ? TryRewriteCall(method, instruction, name, out detail)
                : name is "modf" or "modff" or "sincos" or "sincosf"
                    && TryRewriteScalarOutImportCall(method, instruction, name, out detail);

            if (!rewritten && immediateTarget is { } unresolved)
            {
                // An unresolved import keeps a diagnostic, but it deserves its
                // symbol name instead of a bare address.
                instruction.SetOperand(0, new StringLiteral(name));
                if (DiagnosticsPath != null)
                    Record(method, instruction, unresolved, name,
                        name is "memcpy" or "memset" or "memmove" ? "rejected" : "named", detail);
                else
                    unresolvedOther++;
            }
            else if (DiagnosticsPath != null)
                Record(method, instruction, immediateTarget ?? 0, name,
                    rewritten ? "rewritten" : "rejected", detail);
        }
        if (DiagnosticsPath != null && unresolvedOther > 0)
            lock (DiagnosticsLock)
                System.IO.File.AppendAllText(DiagnosticsPath,
                    $"other\t{method.UnderlyingPointer:x}\t-\t-\tunresolved-call\t{unresolvedOther}\n");
    }

    /// <summary>
    /// Names GOT-veneer import calls before metadata resolution runs. An import is
    /// never a managed method body, but an unresolved immediate target is open to
    /// <see cref="MetadataResolver.ResolveCallsViaMethodInfo"/>: a MethodInfo* an
    /// earlier call left in the hidden-argument register makes it resolve
    /// `bl __stack_chk_fail@plt` (or memcpy) as that managed method. Key functions
    /// keep their address - KeyFunctionRecovery identifies them by it.
    /// </summary>
    internal static void NameImports(MethodAnalysisContext method, Func<ulong, string?>? importNameResolver = null)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet)
            return;

        var binary = method.AppContext.Binary;
        BaseKeyFunctionAddresses? keyFunctions = null;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (!instruction.IsCall || instruction.Operands[0] is not Immediate target)
                continue;
            keyFunctions ??= method.AppContext.GetOrCreateKeyFunctionAddresses();
            if (keyFunctions.IsKeyFunctionAddress(target.UnsignedValue))
                continue;
            var name = importNameResolver != null
                ? importNameResolver(target.UnsignedValue)
                : ResolveImportName(binary, target.UnsignedValue);
            if (name is not { Length: > 0 })
                continue;
            instruction.SetOperand(0, new StringLiteral(name));

            // In SSA a returned dst nothing reads is provably dead. Copy coalescing
            // later folds that X0 def into whatever X0 local is live around the
            // call (often `this`), where it would read as a use and block the
            // block-op rewrite, so the dead def gets its own local now.
            if (name is "memcpy" or "memset" or "memmove"
                && instruction.Operands.Count > 1 && instruction.Operands[1] is LocalVariable result
                && !method.ControlFlowGraph.Instructions.Any(reader => !ReferenceEquals(reader, instruction)
                    && reader.Operands.Any(operand => LocalVariables.OperandLocals(operand).Contains(result))))
            {
                var discarded = new LocalVariable($"discarded_{instruction.Index}",
                    new Register(null, $"DISCARDED_{instruction.Index}"), null);
                method.Locals.Add(discarded);
                instruction.SetOperand(1, discarded);
            }
        }
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
    internal static string? ResolveImportName(Il2CppBinary binary, ulong target)
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

        // Operand 0 is the call target - an Immediate before naming or a
        // StringLiteral once the import is named; the name passed in already
        // says which import it is, so either form is fine.
        if (call.OpCode != OpCode.Call || call.Operands.Count < 5)
        {
            detail = $"shape:op={call.OpCode} count={call.Operands.Count}";
            return false;
        }

        var destination = call.Operands[2];
        var content = call.Operands[3];
        var count = call.Operands[4];

        if (count is Immediate { Value: > 0 } extent)
        {
            if (opcode == OpCode.MemorySet && content is Immediate { Value: 0 }
                && destination is AddressOf { Target: FieldReference { Field.IsStatic: false } first }
                && TrySplitFieldZeroFill(method, call, first, extent.Value))
            {
                detail = $"fields dst={Describe(destination, method)} n={extent.Value}";
                return true;
            }
            var pointerSize = method.AppContext.Binary.PointerSizeBytes;
            destination = WholeMemberAddress(destination, extent.Value, pointerSize);
            if (opcode != OpCode.MemorySet)
                content = WholeMemberAddress(content, extent.Value, pointerSize);
        }

        // A copy out of a local nothing else in the method writes or addresses reads
        // bytes the lift lost track of (a by-reference struct argument mapped to the
        // wrong frame slot); spelling it as a copy would read an unassigned local.
        if (opcode != OpCode.MemorySet && content is AddressOf { Target: LocalVariable source }
            && !source.IsThis && !method.ParameterLocals.Contains(source)
            && !method.ControlFlowGraph!.Instructions.Any(other => !ReferenceEquals(other, call)
                && other.Operands.Any(operand => LocalVariables.OperandLocals(operand).Contains(source))))
        {
            detail = $"src-unwritten={Describe(content, method)}";
            return false;
        }

        // The hidden return buffer local is typed as the value it points at, so a
        // block op through it writes the returned value: its storage is the address.
        var returnBuffer = ReturnBufferLocal(method);
        var intoReturnBuffer = returnBuffer != null && ReferenceEquals(destination, returnBuffer);
        if (intoReturnBuffer)
            destination = new AddressOf(returnBuffer!);

        // A block op that assigns one value type whole is emitted typed (initobj,
        // ldobj/stobj), which keeps the GC barriers a reference field needs.
        IOperand typedDestination = destination, typedContent = content;
        var typed = IlGenerator.TypedBlockPointee(opcode, ref typedDestination, ref typedContent, count, method) != null;

        // Raw block ops write bytes without write barriers, so the destination's region
        // must provably hold no managed references. memset's fill byte and every size
        // argument need an integral shape; a memcpy/memmove source only has to produce
        // a pointer - reading a managed region through it needs no barrier.
        if (!typed && (intoReturnBuffer || !IsProvablyReferenceFreeRegion(destination, count, method, [])))
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
            if (intoReturnBuffer)
            {
                // The returned dst is the return buffer: the value it now holds.
                if (method.ControlFlowGraph.FindBlockByInstruction(call) is not { } block)
                {
                    detail = "block";
                    return false;
                }
                call.SetOperands(destination, content, count);
                block.Instructions.Insert(block.Instructions.IndexOf(call) + 1,
                    new Instruction(-1, OpCode.Move, result, returnBuffer!));
            }
            else
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
        }
        else
            call.SetOperands(destination, content, count);

        call.OpCode = opcode;
        detail = $"dst={Describe(destination, method)} src={Describe(content, method)} n={Describe(count, method)}";
        return true;
    }

    // The hidden return-buffer parameter local (X8 on ARM64), which LocalVariables
    // types as the returned value type.
    private static LocalVariable? ReturnBufferLocal(MethodAnalysisContext method) =>
        method.AppContext.InstructionSet.CallingConventionResolver?.HiddenReturnBufferRegister(method) is { } register
            ? method.Locals.FirstOrDefault(local => local.Register.Number == register.Number
                && local.Register.Version == -1 && local.Type is { IsValueType: true })
            : null;

    // IL2CPP copies struct temporaries between frame slots with memcpy, and those
    // slots carry no type of their own. A copy of exactly sizeof(T) bytes between
    // an untyped slot and storage proven to hold a T gives the slot T, in either
    // direction and to a fixpoint, so a chain of temporaries types from one
    // anchor. A slot that another frame local overlaps is left alone: those bytes
    // have a second name.
    private static void TypeCopiedFrameSlots(MethodAnalysisContext method,
        List<(Instruction Call, string Name)> imports)
    {
        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var (call, name) in imports)
                if (name is "memcpy" or "memmove" && call is { OpCode: OpCode.Call, Operands.Count: >= 5 }
                    && call.Operands[4] is Immediate { Value: > 0 } count)
                    changed |= TypeSlotFromPartner(call.Operands[2], call.Operands[3], count.Value, method)
                        | TypeSlotFromPartner(call.Operands[3], call.Operands[2], count.Value, method);
        }
    }

    private static bool TypeSlotFromPartner(IOperand slotAddress, IOperand partner, long count,
        MethodAnalysisContext method)
    {
        if (slotAddress is not AddressOf { Target: LocalVariable { Type: null } slot }
            || LocalVariables.TryStackOffset(slot.Register.Name) is not { } start
            || IlGenerator.EmittedOperandType(partner, method) is not ByRefTypeAnalysisContext
                { ElementType: { IsValueType: true } type }
            || type is GenericParameterTypeAnalysisContext
            || TypeSizes.MinimumUnboxedSize(type, method.AppContext.Binary.PointerSizeBytes) != count
            || method.Locals.Any(other => !ReferenceEquals(other, slot)
                && LocalVariables.TryStackOffset(other.Register.Name) is { } offset
                && offset > start && offset < start + count))
            return false;
        slot.Type = type;
        return true;
    }

    // `&obj.Last.Root` is how field resolution spells `obj + 0x10`: the first leaf at
    // that offset. A block op of `count` bytes there addresses the outermost member
    // that starts at the same byte and spans exactly `count` - `&obj.Last` for a
    // 320-byte struct. Any other pointer, or a path whose offsets do not add up to
    // the reference's own, is returned unchanged.
    private static IOperand WholeMemberAddress(IOperand pointer, long count, int pointerSize)
    {
        if (pointer is not AddressOf { Target: FieldReference { Field.IsStatic: false } leaf })
            return pointer;
        var path = leaf.Containers.Append(leaf.Field).ToList();
        if (path.Sum(FieldOffset) != leaf.Offset)
            return pointer;
        for (var depth = 0; depth < path.Count; depth++)
        {
            if (path.Skip(depth + 1).Any(member => FieldOffset(member) != 0)
                || FieldStorageSize(path[depth], pointerSize) != count)
                continue;
            return depth == path.Count - 1
                ? pointer
                : new AddressOf(new FieldReference(path[depth], leaf.Local, leaf.Offset, path.Take(depth).ToList()));
        }
        return pointer;
    }

    // A zero fill over a managed object's fields is each covered field's default:
    // clang merges `Last = new Pose(); Frames = 0;` into one memset over both. Every
    // covered field must lie wholly inside the range (padding between them is
    // unobservable); a struct field becomes a typed MemorySet (initobj), a scalar or
    // reference field a store of its zero. The call becomes the first of those and
    // the rest follow it. Anything not covered whole, unspellable, or whose returned
    // dst is still read keeps the call.
    private static bool TrySplitFieldZeroFill(MethodAnalysisContext method, Instruction call, FieldReference first,
        long count)
    {
        if (call.Operands[1] is LocalVariable result
            && method.ControlFlowGraph!.Instructions.Any(consumer => consumer.Sources.Contains(result)))
            return false;

        var root = first.Local;
        var owner = IlGenerator.EmittedOperandType(root, method) is ByRefTypeAnalysisContext byRef
            ? byRef.ElementType
            : IlGenerator.EmittedOperandType(root, method);
        if (owner is null or PointerTypeAnalysisContext or GenericParameterTypeAnalysisContext
            || owner.FullName == "System.Object"
            || first.Containers.Append(first.Field).Sum(FieldOffset) != first.Offset
            || count > int.MaxValue
            || MetadataResolver.CoveredFields(owner, first.Offset, (int)count, wholeStructs: true)
                is not { Count: > 0 } parts
            || method.ControlFlowGraph!.FindBlockByInstruction(call) is not { } block)
            return false;

        var stores = new List<Instruction>();
        foreach (var part in parts)
        {
            var type = part.Field.FieldType;
            var scalar = !type.IsValueType || IlGenerator.IntegralStackWidth(type) != 0
                || type.FullName is "System.Single" or "System.Double";
            if (MetadataResolver.MemberPathUnspellable((part.Field, part.Containers), method,
                    store: true, addressed: !scalar))
                return false;
            var field = new FieldReference(part.Field, root, (int)part.Offset, part.Containers, part.Size);
            if (scalar)
            {
                stores.Add(new Instruction(-1, OpCode.Move, field, type.FullName switch
                {
                    "System.Single" => new FloatLiteral(0f),
                    "System.Double" => new DoubleLiteral(0d),
                    _ => new Immediate(0),
                }));
                continue;
            }
            IOperand address = new AddressOf(field), zero = new Immediate(0);
            if (IlGenerator.TypedBlockPointee(OpCode.MemorySet, ref address, ref zero, new Immediate(part.Size),
                    method) == null)
                return false;
            stores.Add(new Instruction(-1, OpCode.MemorySet, new AddressOf(field), new Immediate(0),
                new Immediate(part.Size)));
        }

        call.OpCode = stores[0].OpCode;
        call.SetOperands([.. stores[0].Operands]);
        block.Instructions.InsertRange(block.Instructions.IndexOf(call) + 1, stores.Skip(1));
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
        || (operand is not AddressOf { Target: FieldReference addressField }
            || !InteriorFieldProvenance(addressField))
            && IlGenerator.EmittedOperandType(operand, context) is { } emitted
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
                // A local's storage ends with its own type: a longer block op would
                // write past it (a frame slot typed by its first field is the usual case).
                var localType = IlGenerator.EmittedLocalType(local, context);
                return IsReferenceFree(localType)
                    && count is Immediate { Value: >= 0 } extent
                    && extent.Value <= TypeSizes.MinimumUnboxedSize(localType,
                        context.AppContext.Binary.PointerSizeBytes);
            case AddressOf { Target: FieldReference field }:
                // A pointer into a nested member or a byref referent's field resolves
                // only through interior-field provenance; the & it emits cannot spell
                // a verifiable void*/cpblk address, so the call keeps its diagnostic.
                return !InteriorFieldProvenance(field) && IsReferenceFree(field.Field.FieldType);
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
                return !InteriorFieldProvenance(field) && field.Field.FieldType switch
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

    // An address resolvable only through interior-field provenance - a nested member
    // path or a field inside a byref referent. Taking its address emits a managed
    // pointer (&) that cpblk consumes unverifiably and conv.u cannot convert, so the
    // block op must stay a diagnosed call rather than recover to invalid IL.
    private static bool InteriorFieldProvenance(FieldReference field) =>
        field.Containers.Count > 0 || field.Local.Type is ByRefTypeAnalysisContext;

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

    /// <summary>
    /// Rewrites a named libm import whose ABI puts an out pointer in an integer
    /// argument slot: `modf`/`modff` (x in s0/d0, iptr in x0) and
    /// `sincos`/`sincosf` (x in s0/d0, sin ptr in x0, cos ptr in x1). The result
    /// becomes the managed call's return value plus a `Move` through each out
    /// pointer - `Move &local, v` collapses to a local store, `Move [byref], v`
    /// to a managed-pointer store, `[stack base+off]` to a frame-slot store, and
    /// `Move fieldRef, v` to stfld. When the pointer's provenance cannot be
    /// resolved to one of those shapes the call stays named instead of emitting
    /// an unverifiable raw store. Because the pass runs last, operands[1]/[2]/[3]/[10]
    /// are still the ABI slots: return local, X0, X1 and V0.
    /// </summary>
    internal static bool TryRewriteScalarOutImportCall(MethodAnalysisContext method, Instruction call,
        string? importName)
        => TryRewriteScalarOutImportCall(method, call, importName, out _);

    internal static bool TryRewriteScalarOutImportCall(MethodAnalysisContext method, Instruction call,
        string? importName, out string detail)
    {
        detail = "";
        var names = importName switch
        {
            "modf" or "modff" => new[] { "Truncate" },
            "sincos" or "sincosf" => new[] { "Sin", "Cos" },
            _ => null,
        };
        if (names == null)
        {
            detail = "not-import";
            return false;
        }

        // V0 is the floating argument slot, so at least operand 10 must exist.
        if (call.OpCode != OpCode.Call || call.Operands.Count < 11)
        {
            detail = $"shape:op={call.OpCode} count={call.Operands.Count}";
            return false;
        }

        var single = importName is "modff" or "sincosf";
        var valueType = single
            ? method.AppContext.SystemTypes.SystemSingleType
            : method.AppContext.SystemTypes.SystemDoubleType;
        var x = call.Operands[10];
        var outSlots = names.Length == 1
            ? new[] { call.Operands[2] }                       // modf: iptr is x0
            : new[] { call.Operands[2], call.Operands[3] };    // sincos: x0/x1

        var results = new (MethodAnalysisContext Method, LocalVariable Result)[names.Length];
        var stores = new Instruction[names.Length];
        for (var i = 0; i < names.Length; i++)
        {
            if (ResolveImportMathMethod(method, names[i], valueType) is not { } mathMethod)
            {
                detail = $"math={names[i]}";
                return false;
            }
            var value = new LocalVariable($"out_{names[i]}_{call.Index}",
                new Register(null, $"X{8 + i}"), valueType);
            results[i] = (mathMethod, value);

            if (!TryMakeOutStore(method, outSlots[i], valueType, value, out var store, out var storeDetail))
            {
                detail = $"out{i}={storeDetail}";
                return false;
            }
            stores[i] = store;
        }

        var block = method.ControlFlowGraph!.FindBlockByInstruction(call);
        if (block == null)
            return false;

        var inserted = new List<Instruction>();
        for (var i = 0; i < names.Length; i++)
        {
            var mathCall = new Instruction(-1, OpCode.Call, results[i].Method, results[i].Result, x);
            if (single)
                mathCall.NativeFloatWidthBits = 32;
            inserted.Add(mathCall);
            inserted.Add(stores[i]);
            method.Locals.Add(results[i].Result);
        }
        block.Instructions.InsertRange(block.Instructions.IndexOf(call), inserted);

        if (names.Length == 1)
        {
            // modf returns x - trunc(x): the fractional part is what remains.
            call.OpCode = OpCode.Subtract;
            call.SetOperands(call.Operands[1], x, results[0].Result);
            call.NativeFloatWidthBits = single ? 32 : 64;
        }
        else
        {
            // sincos returns void; its lifted X0 result slot has no value. The
            // out stores above carry the real outputs, so the call drops away.
            call.OpCode = OpCode.Nop;
        }

        detail = $"x={Describe(x, method)}";
        return true;
    }

    // The managed method for a named libm import in this app's corlib: System.Math
    // for doubles, System.MathF then UnityEngine.Mathf for floats. The corlib is
    // found by assembly name the way IlGenerator's ResolveSystemType does it, with
    // the double type's own declaring assembly as fallback for unusual layouts.
    // Exact-width signatures only - a float import without a float member stays a
    // named call rather than silently widening to double.
    private static MethodAnalysisContext? ResolveImportMathMethod(MethodAnalysisContext context,
        string name, TypeAnalysisContext numberType)
    {
        var systemTypes = context.AppContext.SystemTypes;
        var single = numberType == systemTypes.SystemSingleType;
        var assemblies = new[]
            {
                context.AppContext.AssembliesByName.GetValueOrDefault("mscorlib"),
                systemTypes.SystemDoubleType.DeclaringAssembly,
                context.AppContext.AssembliesByName.GetValueOrDefault("netstandard"),
            }.OfType<AssemblyAnalysisContext>()
            .Distinct();
        var types = assemblies
            .Select(a => a.GetTypeByFullName(single ? "System.MathF" : "System.Math"))
            .Where(t => t != null)
            .ToList();
        if (single)
            types.Add(context.AppContext.AssembliesByName.GetValueOrDefault("UnityEngine.CoreModule")
                ?.GetTypeByFullName("UnityEngine.Mathf"));

        foreach (var type in types.OfType<TypeAnalysisContext>())
            if (type.Methods.FirstOrDefault(method => method.IsStatic && method.Name == name
                    && method.Parameters.Count == 1
                    && method.Parameters[0].ParameterType.FullName == numberType.FullName
                    && method.ReturnType.FullName == numberType.FullName) is { } found)
                return found;
        return null;
    }

    // Turns an out-pointer operand into a `Move target, value` store instruction
    // whose emission is a managed store. Anything else keeps the call named.
    private static bool TryMakeOutStore(MethodAnalysisContext method, IOperand pointer,
        TypeAnalysisContext valueType, LocalVariable value, out Instruction store, out string detail)
    {
        store = null!;
        detail = "";
        switch (ResolveOutStoreTarget(pointer, method, []))
        {
            case LocalVariable local:
                if (!CanReceiveScalarStore(local, valueType, method))
                {
                    detail = Describe(local, method);
                    return false;
                }
                store = new Instruction(-1, OpCode.Move, local, value);
                return true;
            case FieldReference field when !InteriorFieldProvenance(field)
                && field.Field.FieldType.FullName == valueType.FullName:
                store = new Instruction(-1, OpCode.Move, field, value);
                return true;
            case ArrayAccess { Array.Type: SzArrayTypeAnalysisContext { ElementType: { } element } } access
                when element.FullName == valueType.FullName:
                store = new Instruction(-1, OpCode.Move, access, value);
                return true;
            case MemoryOperand memory:
                store = new Instruction(-1, OpCode.Move, memory, value);
                return true;
            case { } other:
                detail = Describe(other, method);
                return false;
            default:
                detail = Describe(pointer, method);
                return false;
        }
    }

    // Resolves what a pointer operand ultimately addresses: a local through an
    // address-of, a field or array element, a byref-typed local (store through
    // [ptr]), or a stack-region base plus a constant offset (a frame slot).
    // Locals whose definitions disagree or trace to an opaque value stay
    // unresolved - the call then keeps its name diagnostic.
    private static IOperand? ResolveOutStoreTarget(IOperand pointer, MethodAnalysisContext context,
        HashSet<LocalVariable> visiting)
    {
        switch (pointer)
        {
            case AddressOf { Target: LocalVariable local }:
                return local;
            case AddressOf { Target: FieldReference field }:
                return field;
            case AddressOf { Target: ArrayAccess access }:
                return access;
            case AddressOf { Target: MemoryOperand memory }:
                return memory;
            case LocalVariable { Type: ByRefTypeAnalysisContext } byRef:
                return new MemoryOperand(byRef);
            case LocalVariable local:
            {
                if (!visiting.Add(local))
                    return null;
                try
                {
                    var defs = context.ControlFlowGraph!.Instructions
                        .Where(i => ReferenceEquals(i.Destination, local)).ToList();
                    IOperand? resolved = null;
                    foreach (var def in defs)
                    {
                        IOperand? target = def.OpCode switch
                        {
                            OpCode.Move or OpCode.SignExtend32 =>
                                ResolveOutStoreTarget(def.Operands[1], context, visiting),
                            OpCode.Add or OpCode.Subtract when def.Operands[1] is AddressOf
                                    { Target: LocalVariable frame } && def.Operands[2] is Immediate offset =>
                                new MemoryOperand(frame, null,
                                    def.OpCode == OpCode.Subtract
                                        ? -(long)offset.UnsignedValue
                                        : (long)offset.UnsignedValue),
                            _ => null,
                        };
                        if (target == null)
                            return null;
                        if (resolved == null)
                            resolved = target;
                        else if (!target.Equals(resolved))
                            return null;
                    }
                    return resolved;
                }
                finally
                {
                    visiting.Remove(local);
                }
            }
            default:
                return null;
        }
    }

    // Whether a local can receive a direct scalar store of this width without a
    // reinterpret: a matching declared type, or an unclaimed slot that takes the
    // value's type (same contract as CanMaterializeReturn).
    private static bool CanReceiveScalarStore(LocalVariable local, TypeAnalysisContext valueType,
        MethodAnalysisContext context)
    {
        if (local.Type == null)
        {
            local.Type = valueType;
            return true;
        }
        return IlGenerator.EmittedOperandType(local, context)?.FullName == valueType.FullName;
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
