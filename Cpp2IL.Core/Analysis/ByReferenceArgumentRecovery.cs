using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Spells struct arguments that the native call passes as an address.
///
/// AAPCS64 B.4 passes a by-value composite wider than 16 bytes as a pointer to a
/// caller-owned copy, so the argument register of such a parameter holds `&amp;slot`,
/// the frame struct the caller filled. The managed call takes the value: the
/// argument becomes what the address names (`&amp;slot` → `slot`, `&amp;obj.f` → `obj.f`,
/// a `T&amp;` local → its referent). A `ref`/`out` parameter takes the address
/// itself; an untyped frame slot passed there is storage of the element type.
///
/// An untyped frame slot is given the parameter's type only when no other frame
/// local starts inside its bytes (those bytes would have a second name), and
/// only when something other than the calls rewritten here writes or addresses
/// it. A slot nothing fills would be read unassigned, so such an argument keeps
/// its address and its diagnostic.
/// </summary>
public static class ByReferenceArgumentRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        if (method.AppContext.InstructionSet.CallingConventionResolver is not { } resolver
            || method.ControlFlowGraph is not { } cfg)
            return;

        var instructions = cfg.Instructions;
        var candidates = new List<(Instruction Call, int Index, TypeAnalysisContext Type, bool ByValue)>();
        foreach (var call in instructions)
        {
            if (!call.IsCall || call.Operands.Count == 0 || call.Operands[0] is not MethodAnalysisContext callee)
                continue;
            var first = (call.OpCode == OpCode.CallVoid ? 1 : 2) + (callee.IsStatic ? 0 : 1);
            for (var i = 0; i < callee.Parameters.Count && first + i < call.Operands.Count; i++)
            {
                var type = callee.Parameters[i].ParameterType;
                if (type is ByRefTypeAnalysisContext { ElementType: { IsValueType: true } element })
                    candidates.Add((call, first + i, element, false));
                else if (resolver.PassesByReference(type))
                    candidates.Add((call, first + i, type, true));
            }
        }
        if (candidates.Count == 0)
            return;

        var argumentPositions = candidates.Select(c => (c.Call, c.Index)).ToHashSet();
        foreach (var (call, index, type, byValue) in candidates)
        {
            var operand = call.Operands[index];
            if (operand is AddressOf { Target: LocalVariable { Type: null } slot }
                && !TypeFrameSlot(slot, type, method, instructions, argumentPositions, needsFill: byValue))
                continue;

            if (!byValue)
                continue;
            if (Referent(operand, type) is { } value
                && !(value is LocalVariable copy && CopiesUnwrittenLocal(copy, method, instructions)))
                call.SetOperand(index, value);
        }
    }

    // What a pointer argument names, when it provably names a T: a local, field or
    // element whose address it is, or the referent of a T& local.
    private static IOperand? Referent(IOperand pointer, TypeAnalysisContext type) => pointer switch
    {
        AddressOf { Target: LocalVariable local } when SameType(local.Type, type) => local,
        AddressOf { Target: FieldReference field } when SameType(field.Field.FieldType, type) => field,
        AddressOf { Target: ArrayAccess { Array.Type: SzArrayTypeAnalysisContext array } access }
            when SameType(array.ElementType, type) => access,
        LocalVariable { Type: ByRefTypeAnalysisContext byRef } local when SameType(byRef.ElementType, type)
            => new MemoryOperand(local),
        _ => null,
    };

    private static bool TypeFrameSlot(LocalVariable slot, TypeAnalysisContext type, MethodAnalysisContext method,
        List<Instruction> instructions, HashSet<(Instruction, int)> argumentPositions, bool needsFill)
    {
        var size = TypeSizes.MinimumUnboxedSize(type, method.AppContext.Binary.PointerSizeBytes);
        if (LocalVariables.TryStackOffset(slot.Register.Name) is not { } start
            || size <= 0
            || method.Locals.Any(other => !ReferenceEquals(other, slot)
                && LocalVariables.TryStackOffset(other.Register.Name) is { } offset
                && offset > start && offset < start + size))
            return false;

        // A by-value copy must be filled by something: a write into the slot, or
        // its address taken anywhere but the argument positions this pass spells.
        // A ref/out argument's own callee may fill it.
        if (needsFill && !instructions.Any(instruction =>
                ReferenceEquals(instruction.Destination, slot)
                || instruction.Destination is { } written and not LocalVariable
                    && LocalVariables.OperandLocals(written).Contains(slot)
                || instruction.Operands.Select((operand, i) => (operand, i)).Any(entry =>
                    entry.operand is AddressOf
                    && !argumentPositions.Contains((instruction, entry.i))
                    && LocalVariables.OperandLocals(entry.operand).Contains(slot))))
            return false;

        slot.Type = type;
        return true;
    }

    // The lift can feed the copy from a frame slot nothing writes: a register
    // copy out of a hidden-return slot whose write it attributes to the call's
    // result local instead. Passing that copy would pass unassigned bytes, so
    // the argument keeps its address and its diagnostic.
    private static bool CopiesUnwrittenLocal(LocalVariable copy, MethodAnalysisContext method,
        List<Instruction> instructions) =>
        instructions.Any(definition => ReferenceEquals(definition.Destination, copy)
            && definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable source] }
            && !source.IsThis && !method.ParameterLocals.Contains(source)
            && !instructions.Any(writer => ReferenceEquals(writer.Destination, source)
                || writer.Destination is { } written and not LocalVariable
                    && LocalVariables.OperandLocals(written).Contains(source)
                || writer.Operands.Any(operand => operand is AddressOf
                    && LocalVariables.OperandLocals(operand).Contains(source))));

    private static bool SameType(TypeAnalysisContext? a, TypeAnalysisContext b)
        => a != null && (ReferenceEquals(a, b) || a.FullName == b.FullName);
}
