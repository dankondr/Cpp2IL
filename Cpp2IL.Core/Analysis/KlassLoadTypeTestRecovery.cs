using System.Collections.Generic;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Recovery cluster: unmanaged loads of the object header's klass word (+0)
/// reaching an exact-type test.
///
/// `Move v, [obj]` reads the object's klass pointer. A `CheckEqual`/`CheckNotEqual`
/// comparing it against a provable type value - an inline `typeof(T)` operand, a
/// type-global local (`Move v, typeof(T)`), or another object's klass load - is
/// `obj.GetType() == typeof(T)` (respectively `a.GetType() == b.GetType()`).
/// The klass value never had a managed spelling, so folding the load into the
/// compare is the only honest recovery: the compare operand is rewritten to the
/// `[obj]` memory operand and the `Move`'s definition is left for dead-code
/// elimination.
///
/// A base whose definition is an address computation (Add/Subtract/shift chain,
/// `Move x, &slot`, Unbox) is an interior pointer, not an object reference: its
/// `+0` word reads the slot's pointer, not a klass - those sites keep the
/// diagnostic, as does every klass read with any non-type-test consumer (the
/// value is then needed as a runtime pointer, which has no managed equivalent).
/// </summary>
public static class KlassLoadTypeTestRecovery
{
    public static void Run(MethodAnalysisContext method) => Run(method.ControlFlowGraph!);

    public static void Run(ISILControlFlowGraph cfg)
    {
        var (definitions, _) = InterfaceDispatchRecovery.BuildMaps(cfg);

        var changed = false;
        foreach (var block in cfg.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                if (instruction is not { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands.Count: 3 })
                    continue;

                var left = ResolveSide(instruction.Operands[1], definitions);
                var right = ResolveSide(instruction.Operands[2], definitions);

                if (IsKlassLoad(left, definitions) && IsTypeValue(right)
                    || IsKlassLoad(right, definitions) && IsTypeValue(left)
                    || IsKlassLoad(left, definitions) && IsKlassLoad(right, definitions))
                {
                    instruction.SetOperand(1, left);
                    instruction.SetOperand(2, right);
                    changed = true;
                }
            }
        }

        if (changed)
            DeadCodeEliminator.Run(cfg);
    }

    private static bool IsTypeValue(IOperand operand) => operand is TypeAnalysisContext;

    /// <summary>
    /// Whether the operand is a `+0` load on a provable managed-object base, i.e.
    /// a klass pointer read (`obj.klass` / `obj.GetType()`).
    /// </summary>
    private static bool IsKlassLoad(IOperand operand, Dictionary<LocalVariable, Instruction> definitions) =>
        IsObjectHeaderKlassLoad(operand, definitions, out _);

    /// <summary>
    /// Whether the operand is a `+0` load on a managed-object base: the base is a
    /// local whose type is a plain reference type (not a runtime structure, not a
    /// pointer/byref, not an array) and whose definition - when one exists - is a
    /// value-producing instruction rather than an address computation. The last
    /// check rejects interior/aliased pointers typed as the slot's content type:
    /// their `+0` word reads the slot, not a klass.
    /// </summary>
    internal static bool IsObjectHeaderKlassLoad(IOperand operand,
        IReadOnlyDictionary<LocalVariable, Instruction> definitions, out LocalVariable local)
    {
        local = null!;
        if (operand is not MemoryOperand { Index: null, Addend: 0, Scale: 0, Base: LocalVariable baseLocal }
            || !IsManagedObjectType(baseLocal.Type))
            return false;

        local = baseLocal;
        return IsObjectValue(baseLocal, definitions);
    }

    private static bool IsManagedObjectType(TypeAnalysisContext? type) =>
        type is { IsValueType: false }
            and not RuntimeClassTypeAnalysisContext and not RuntimeMethodInfoAnalysisContext
            and not RuntimeFieldInfoAnalysisContext and not StaticFieldStorageTypeAnalysisContext
            and not RgctxTableTypeAnalysisContext and not MethodRgctxTableTypeAnalysisContext
            and not GenericParameterTypeAnalysisContext and not SentinelTypeAnalysisContext
            and not BooleanClaimVetoedSlotTypeAnalysisContext and not ByRefTypeAnalysisContext
            and not PointerTypeAnalysisContext and not PinnedTypeAnalysisContext
            and not CustomModifierTypeAnalysisContext and not ArrayTypeAnalysisContext
            and not SzArrayTypeAnalysisContext;

    private static bool IsObjectValue(LocalVariable local, IReadOnlyDictionary<LocalVariable, Instruction> definitions)
    {
        if (!definitions.TryGetValue(local, out var definition))
            return true; // parameter or never-defined register local - holds a value

        return definition.OpCode switch
        {
            // value-producing instructions; a Move from an AddressOf is an address
            OpCode.Move => definition.Operands.Count == 2 && definition.Operands[1] is not AddressOf,
            OpCode.Call or OpCode.IndirectCall or OpCode.Newobj or OpCode.NewArr
                or OpCode.Box or OpCode.Phi => true,
            _ => false,
        };
    }

    private static IOperand ResolveSide(IOperand operand, Dictionary<LocalVariable, Instruction> definitions)
    {
        if (operand is not LocalVariable local
            || InterfaceDispatchRecovery.ChaseCopies(definitions, local) is not
                { OpCode: OpCode.Move, Operands: [_, var source] })
            return operand;

        return source;
    }
}
