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

    // Whether the operand's definition chain proves the binary allocated the
    // box the slot asks for. `operationProvesBox` marks operations that can
    // only execute on a boxed receiver (a value-typed GetType call).
    public static bool ObjectBoxEdgeProven(IOperand? operand, MethodAnalysisContext? context,
        bool operationProvesBox = false) =>
        operationProvesBox
        || (context != null && OperandProvesBox(operand, context));

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

    // A local tagged System.Object by the lifter is often not a reference at
    // all: object is the fallback tag for a register whose real type analysis
    // lost, and the register's own definitions still prove what it carried.
    // When every definition provably produces the same value type - a move of
    // a typed operand, an integer operation's stack result, a comparison flag,
    // a phi whose inputs unify - the slot's honest type is that scalar, and
    // the object contract attached to it is only Cpp2IL's own typing. A
    // register that mixes scalar and reference lifetimes (one definition feeds
    // an object field, another an int) cannot be retyped to a single honest
    // slot and stays object. Returns the shared proven value type, or null.
    public static TypeAnalysisContext? ProvenScalarSlotType(LocalVariable local,
        MethodAnalysisContext context)
    {
        // Emission asks this once per store site; the answer only depends on
        // the register's definitions, so it is cached on the method context.
        var cache = context.GetExtraData<Dictionary<LocalVariable, TypeAnalysisContext?>>("ProvenScalarSlotTypes");
        if (cache == null)
        {
            cache = [];
            context.PutExtraData("ProvenScalarSlotTypes", cache);
        }
        if (cache.TryGetValue(local, out var cached))
            return cached;
        var slotType = ProvenScalarSlotType(local, context, []);
        var proven = slotType is { } resolved && ScalarSlotTypeUsable(resolved, context)
            ? resolved
            : null;
        cache[local] = proven;
        return proven;
    }

    private static TypeAnalysisContext? ProvenScalarSlotType(LocalVariable local,
        MethodAnalysisContext context, HashSet<LocalVariable> visited)
    {
        if (!visited.Add(local))
            return null;
        if (context.ControlFlowGraph is not { } graph)
            return null;
        TypeAnalysisContext? proven = null;
        var found = false;
        foreach (var definition in graph.Instructions
                     .Where(i => ReferenceEquals(i.Destination, local)))
        {
            var produced = ProducedScalarType(definition, context, visited);
            if (produced == null)
                return null;
            proven = proven == null ? produced : MergeScalarTypes(proven, produced, context);
            if (proven == null)
                return null;
            found = true;
        }
        return found ? proven : null;
    }

    // The stack type one producing instruction provably leaves in the
    // destination: moves and phis carry their sources' proven types, integer
    // operations always produce the shared operand width the emission resolves
    // (Int32 when nothing names a width), comparisons an i4 flag, sign
    // extension an i8 and a call its declared return when that is a value
    // type. Producers of references, managed pointers or memory - and any
    // operation whose value cannot be spelled as a single scalar - prove
    // nothing and veto the slot.
    private static TypeAnalysisContext? ProducedScalarType(Instruction definition,
        MethodAnalysisContext context, HashSet<LocalVariable> visited)
    {
        var systemTypes = context.AppContext.SystemTypes;
        switch (definition.OpCode)
        {
            case OpCode.Move:
                return definition.Operands.Count > 1
                    ? ProvenOperandType(definition.Operands[1], context, visited)
                    : null;
            case OpCode.Phi:
            {
                TypeAnalysisContext? joined = null;
                foreach (var source in definition.Operands.Skip(1))
                {
                    var sourceType = ProvenOperandType(source, context, visited);
                    if (sourceType == null)
                        return null;
                    joined = joined == null ? sourceType : MergeScalarTypes(joined, sourceType, context);
                    if (joined == null)
                        return null;
                }
                return joined;
            }
            case OpCode.Add:
            case OpCode.Subtract:
            case OpCode.Multiply:
            case OpCode.Divide:
            case OpCode.Modulo:
            case OpCode.ShiftLeft:
            case OpCode.ShiftRight:
            case OpCode.And:
            case OpCode.Or:
            case OpCode.Xor:
            {
                // Mirrors BinaryOperandType: the widest integral operand wins,
                // a float operand wins outright, a pointer/byref source makes
                // the operation native-int, and bare literals fall back to
                // their natural width - the same Int32 the emit path uses when
                // nothing else pins the operation down.
                TypeAnalysisContext? widest = null;
                var widestWidth = 0;
                TypeAnalysisContext? floatType = null;
                TypeAnalysisContext? literalType = null;
                var literalWidth = 0;
                foreach (var operand in definition.Operands.Skip(1))
                {
                    var operandType = ProvenOperandType(operand, context, visited);
                    if (operandType is { IsEnumType: true })
                        operandType = operandType.DefaultEnumUnderlyingType ?? operandType;
                    var width = operandType == null ? 0 : IlGenerator.IntegralStackWidth(operandType);
                    if (width < 0)
                        return systemTypes.SystemIntPtrType;
                    if (operandType?.FullName is "System.Single" or "System.Double")
                    {
                        if (floatType?.FullName != "System.Double")
                            floatType = operandType;
                        continue;
                    }
                    // Literals only name the width when no operand does - the
                    // same literal-scan BinaryOperandType runs as a fallback.
                    if (operand is Immediate)
                    {
                        if (width > literalWidth)
                        {
                            literalType = operandType;
                            literalWidth = width;
                        }
                        continue;
                    }
                    if (width > widestWidth)
                    {
                        widest = operandType;
                        widestWidth = width;
                    }
                }
                return floatType ?? widest ?? literalType ?? systemTypes.SystemInt32Type;
            }
            case OpCode.Not:
            case OpCode.Negate:
                return definition.Operands.Count > 1
                    ? ProvenOperandType(definition.Operands[1], context, visited)
                        ?? systemTypes.SystemInt32Type
                    : null;
            case OpCode.CheckEqual:
            case OpCode.CheckNotEqual:
            case OpCode.CheckGreater:
            case OpCode.CheckGreaterOrEqual:
            case OpCode.CheckLess:
            case OpCode.CheckLessOrEqual:
                return systemTypes.SystemInt32Type;
            case OpCode.SignExtend32:
                return systemTypes.SystemInt64Type;
            case OpCode.Call or OpCode.IndirectCall:
                return definition.Operands.Count > 1
                    && definition.Operands[0] is MethodAnalysisContext callee
                    && callee.ReturnType is { IsValueType: true } returnType
                    ? returnType
                    : null;
            default:
                return null;
        }
    }

    // The value type one operand provably pushes: a literal its natural width,
    // a concretely typed operand its emitted type, and an object-tagged or
    // untyped local whatever its own definitions prove. Managed pointers,
    // memory dereferences and everything else prove nothing.
    private static TypeAnalysisContext? ProvenOperandType(IOperand operand,
        MethodAnalysisContext context, HashSet<LocalVariable> visited) =>
        operand switch
        {
            Immediate literal => literal.Value is >= int.MinValue and <= int.MaxValue
                ? context.AppContext.SystemTypes.SystemInt32Type
                : context.AppContext.SystemTypes.SystemInt64Type,
            // A native handle (klass, method/field info, storage, rgctx) is an
            // opaque pseudo-reference spelled as a native int: it proves no
            // scalar for the slot - the object edge keeps its conversion.
            LocalVariable source => source.Type is { } sourceType
                    && IlGenerator.IsNativeHandleType(sourceType)
                ? null
                : source.Type is { } concreteSourceType
                    && concreteSourceType.FullName is not ("System.Object" or "System.Void")
                ? IlGenerator.EmittedOperandType(source, context) is { IsValueType: true } emitted
                    ? emitted
                    : null
                : ProvenScalarSlotType(source, context, visited),
            AddressOf => null,
            MemoryOperand => null,
            TypeAnalysisContext constant when IlGenerator.IsNativeHandleType(constant) => null,
            _ => IlGenerator.EmittedOperandType(operand, context) is { IsValueType: true } emitted
                ? emitted
                : null,
        };

    // Two proven scalar spellings unify to the wider one: integral widths to
    // the wider width, any native-int to IntPtr and a float to the wider
    // float. Anything that does not share a scalar kind cannot unify.
    private static TypeAnalysisContext? MergeScalarTypes(TypeAnalysisContext first,
        TypeAnalysisContext second, MethodAnalysisContext context)
    {
        if (first.FullName == second.FullName)
            return first;
        if (first is { IsEnumType: true })
            first = first.DefaultEnumUnderlyingType ?? first;
        if (second is { IsEnumType: true })
            second = second.DefaultEnumUnderlyingType ?? second;
        if (first.FullName == second.FullName)
            return first;
        var systemTypes = context.AppContext.SystemTypes;
        if (IlGenerator.IntegralStackWidth(first) < 0 || IlGenerator.IntegralStackWidth(second) < 0)
            return systemTypes.SystemIntPtrType;
        var firstFloat = first.FullName is "System.Single" or "System.Double";
        var secondFloat = second.FullName is "System.Single" or "System.Double";
        if (firstFloat || secondFloat)
            return firstFloat && secondFloat
                ? (first.FullName == "System.Double" ? first : second)
                : systemTypes.SystemDoubleType;
        var firstWidth = IlGenerator.IntegralStackWidth(first);
        var secondWidth = IlGenerator.IntegralStackWidth(second);
        if (firstWidth > 0 && secondWidth > 0)
            return firstWidth >= secondWidth ? first : second;
        return null;
    }

    // The retyped slot must itself be a type the emitter can name: a type
    // token must exist for the .locals declaration and every stloc/ldloc, and
    // a non-corlib value type must also be visible to the method that owns
    // the local.
    private static bool ScalarSlotTypeUsable(TypeAnalysisContext type, MethodAnalysisContext context) =>
        IlGenerator.CanEmitTypeToken(type)
        && !IlGenerator.IsByRefLike(type)
        && (type.Namespace == "System" || type is { IsEnumType: true }
            || context.DeclaringType == null
            || InaccessibleCalleeRecovery.IsVisibleType(type, context.DeclaringType));
}
