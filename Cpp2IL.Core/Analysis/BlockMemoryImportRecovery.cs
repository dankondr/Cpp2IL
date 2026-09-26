using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Il2CppApiFunctions;
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
/// The rewrite commits only when the destination operand provably denotes a region
/// that cannot hold managed references: cpblk/initblk emit no GC write barriers, so a
/// destination that could carry reference slots must stay an unresolved call and keep
/// its diagnostic rather than silently skip the barriers a managed store would need.
/// The returned dst pointer is preserved as a native int only when the lifted result
/// local is still read.
/// </summary>
public static class BlockMemoryImportRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet is not NewArmV8InstructionSet)
            return;

        var binary = method.AppContext.Binary;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Call || instruction.Operands[0] is not Immediate target)
                continue;

            TryRewriteCall(method, instruction, ResolveImportName(binary, target.UnsignedValue));
        }
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

    // Rewrites an unresolved Call to the matching block op when the ABI shape is raw
    // (operand 2..4 = X0..X2) and the operand proofs below hold. Returns false when any
    // evidence is missing - the call keeps its unresolved diagnostic instead.
    internal static bool TryRewriteCall(MethodAnalysisContext method, Instruction call, string? importName)
    {
        var opcode = importName switch
        {
            "memcpy" => OpCode.MemoryCopy,
            "memset" => OpCode.MemorySet,
            "memmove" => OpCode.MemoryMove,
            _ => OpCode.Invalid,
        };
        if (opcode == OpCode.Invalid)
            return false;

        if (call.OpCode != OpCode.Call
            || call.Operands.Count < 5
            || method.AppContext.InstructionSet.CallingConventionResolver is not { } resolver
            || !resolver.HasRawArgumentLayout(call, method.AppContext))
            return false;

        var destination = call.Operands[2];
        var content = call.Operands[3];
        var count = call.Operands[4];

        // Raw block ops write bytes without write barriers, so the destination's region
        // must provably hold no managed references. memset's fill byte and every size
        // argument need an integral shape; a memcpy/memmove source only has to produce
        // a pointer - reading a managed region through it needs no barrier.
        if (!IsProvablyReferenceFreeRegion(destination, method) || !IsScalarOperand(count, method))
            return false;
        if (opcode == OpCode.MemorySet
                ? !IsScalarOperand(content, method)
                : !IsPointerOperandRepresentable(content, method))
            return false;

        var result = call.Operands[1] as LocalVariable;
        if (result != null && method.ControlFlowGraph!.Instructions
                .Any(consumer => consumer.Sources.Contains(result)))
        {
            // The native functions return dst: materialize it as a native int so the
            // result keeps a pointer value no matter what the destination operand was.
            result.Type = method.AppContext.SystemTypes.SystemIntPtrType;
            call.SetOperands(destination, content, count, result);
        }
        else
            call.SetOperands(destination, content, count);

        call.OpCode = opcode;
        return true;
    }

    /// <summary>
    /// Whether the operand can be loaded as a pointer-shaped stack value (&, *, native
    /// int or an integral address literal). Used for memcpy/memmove sources: reading a
    /// region through cpblk needs no barrier, only representability.
    /// </summary>
    internal static bool IsPointerOperandRepresentable(IOperand operand, MethodAnalysisContext context) =>
        operand is Immediate
        || IlGenerator.EmittedOperandType(operand, context) is { } emitted
            && IlGenerator.IntegralStackWidth(emitted) != 0;

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
    /// slots, so raw byte stores into it cannot bypass GC write barriers. A managed
    /// pointer's element type must be fully reference-free; an unmanaged pointer value,
    /// native handle or absolute address is unmanaged by construction.
    /// </summary>
    internal static bool IsProvablyReferenceFreeRegion(IOperand operand, MethodAnalysisContext context)
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
        }

        return IlGenerator.EmittedOperandType(operand, context) switch
        {
            PointerTypeAnalysisContext pointer => IsReferenceFree(pointer.ElementType),
            ByRefTypeAnalysisContext byRef => IsReferenceFree(byRef.ElementType),
            { } type => IlGenerator.IntegralStackWidth(type) != 0,
            null => false,
        };
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
