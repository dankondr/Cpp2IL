using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Binary-evidence classification for scalar -> System.Object edges
// (castle-recovery#189). A scalar value pushed where a slot requires
// System.Object is honest in exactly two cases:
//   * the value provably is a managed reference - every definition of the
//     operand produced one (a reference-typed field or array load, a cast, a
//     reference-returning call or an allocation), so the slot really holds an
//     object reference;
//   * the binary itself allocated a box - an il2cpp_value_box /
//     il2cpp_vm_object_box helper call (rewritten by the lifter into an ISIL
//     Box) defined the operand.
// Every other scalar -> object edge asks for a conversion the binary never
// performed and must be diagnosed rather than boxed silently.
public static class ScalarObjectEdgeAnalysis
{
    public static bool IsScalarObjectEdge(TypeAnalysisContext? from, TypeAnalysisContext? to) =>
        from is { IsValueType: true }
        && to is { FullName: "System.Object" }
        && to is not PointerTypeAnalysisContext and not ByRefTypeAnalysisContext
        and not BooleanClaimVetoedSlotTypeAnalysisContext;

    // Whether the operand's definition chain proves the value arrives boxed:
    // every definition of the local is an ISIL Box (a lifter-rewritten
    // il2cpp_value_box/il2cpp_vm_object_box call) or a direct call to a
    // box-allocation helper. Single-source Moves chase the value's provenance.
    public static bool OperandProvesBox(IOperand? operand, MethodAnalysisContext context) =>
        operand is LocalVariable local && LocalProvesBox(local, context, []);

    private static bool LocalProvesBox(LocalVariable local, MethodAnalysisContext context,
        HashSet<LocalVariable> visited)
    {
        if (!visited.Add(local))
            return true;
        var found = false;
        foreach (var definition in context.ControlFlowGraph!.Instructions
                     .Where(i => ReferenceEquals(i.Destination, local)))
        {
            found = true;
            var proven = definition.OpCode switch
            {
                OpCode.Box => true,
                OpCode.Call or OpCode.CallVoid => definition.Operands.Count > 0
                    && definition.Operands[0] is MethodAnalysisContext callee
                    && callee.Name is "il2cpp_value_box" or "il2cpp_vm_object_box",
                OpCode.Move => definition.Operands.Count > 1
                    && definition.Operands[1] is LocalVariable source
                    && !ReferenceEquals(source, local)
                    && LocalProvesBox(source, context, visited),
                _ => false
            };
            if (!proven)
                return false;
        }
        return found;
    }

    // Resolves the operand form that carries the managed reference the slot
    // really holds, when the operand's definitions prove one. Only
    // side-effect-free producers can be replayed: reference-typed field and
    // array loads, casts and reference-typed locals; a call or allocation
    // result lives in its own local and cannot be re-emitted here. A local
    // resolves only when every one of its definitions moves the same proven
    // source - a register that mixes lifetimes has no single honest spelling.
    public static IOperand? TryResolveReferenceValue(IOperand? operand, MethodAnalysisContext context,
        HashSet<LocalVariable>? visited = null)
    {
        switch (operand)
        {
            case FieldReference { Field.FieldType: { IsValueType: false } }:
            case SelectedFieldReference { FieldType: { IsValueType: false } }:
            case ArrayElementFieldReference { Field.FieldType: { IsValueType: false } }:
            case ArrayAccess { Array.Type: SzArrayTypeAnalysisContext { ElementType: { IsValueType: false } } }:
            case ReferenceCast:
                return operand;
            case LocalVariable { Type: { IsValueType: false } }:
                return operand;
            case LocalVariable local:
                visited ??= [];
                if (!visited.Add(local))
                    return null;
                IOperand? proven = null;
                var found = false;
                foreach (var definition in context.ControlFlowGraph!.Instructions
                             .Where(i => ReferenceEquals(i.Destination, local)))
                {
                    if (definition is not { OpCode: OpCode.Move, Operands.Count: > 1 })
                        return null;
                    var candidate = TryResolveReferenceValue(definition.Operands[1], context, visited);
                    if (candidate == null || (proven != null && !ReferenceEquals(candidate, proven)))
                        return null;
                    proven = candidate;
                    found = true;
                }
                return found ? proven : null;
            default:
                return null;
        }
    }
}
