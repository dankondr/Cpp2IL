using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Recovers explicit managed casts only where the native CFG already proves the same cast.
public static class ReferenceCastRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        foreach (var block in method.ControlFlowGraph!.Blocks)
        foreach (var instruction in block.Instructions)
        {
            if (instruction is not { OpCode: OpCode.Move, Operands: [FieldReference field, LocalVariable value] }
                || !field.Field.FieldType.IsDelegate
                || ReferenceEquals(value.Type, field.Field.FieldType)
                || block.Instructions.TakeWhile(i => i != instruction).Any(i => i.OpCode != OpCode.Nop)
                || !HasExactTypeGuard(block, value, field.Field.FieldType))
                continue;

            instruction.SetOperand(1, new ReferenceCast(value, field.Field.FieldType));
        }
    }

    internal static bool HasExactTypeGuard(Block useBlock, LocalVariable value, TypeAnalysisContext type)
    {
        var classGuard = useBlock.Predecessors.SingleOrDefault(block => IsExactClassGuard(block, useBlock, value, type));
        if (classGuard == null)
            return false;

        if (useBlock.Predecessors.Count == 1)
            return true;

        if (useBlock.Predecessors.Count != 2 || classGuard.Predecessors.Count != 1)
            return false;

        var nullGuard = classGuard.Predecessors[0];
        var instructions = nullGuard.Instructions.Where(i => i.OpCode != OpCode.Nop).ToArray();
        return ReferenceEquals(useBlock.Predecessors.Single(block => block != classGuard), nullGuard)
            && nullGuard.Successors.Count == 2
            && nullGuard.Successors.Contains(classGuard)
            && nullGuard.Successors.Contains(useBlock)
            && instructions.Length >= 2
            && instructions[^2] is
                { OpCode: OpCode.CheckEqual, Operands: [LocalVariable condition, var checkedValue, Immediate { Value: 0 }] }
            && instructions[^1] is
                { OpCode: OpCode.ConditionalJump, Operands: [var target, var branchCondition] }
            && ReferenceEquals(checkedValue, value)
            && ReferenceEquals(target, useBlock)
            && ReferenceEquals(branchCondition, condition);
    }

    private static bool IsExactClassGuard(Block guard, Block useBlock, LocalVariable value, TypeAnalysisContext type)
    {
        var instructions = guard.Instructions.Where(i => i.OpCode != OpCode.Nop).ToArray();
        if (guard.Successors.Count != 2 || !guard.Successors.Contains(useBlock)
            || instructions is not
            [
                { OpCode: OpCode.CheckNotEqual, Operands: [LocalVariable condition,
                    MemoryOperand { Base: var instance, Index: null, Addend: 0, Scale: 0 }, var checkedType] },
                { OpCode: OpCode.ConditionalJump, Operands: [Block failure, var branchCondition] }
            ]
            || !ReferenceEquals(instance, value)
            || !ReferenceEquals(checkedType, type)
            || !ReferenceEquals(branchCondition, condition)
            || ReferenceEquals(failure, useBlock)
            || !guard.Successors.Contains(failure))
            return false;

        var failureInstructions = failure.Instructions.Where(i => i.OpCode != OpCode.Nop).ToArray();
        return failureInstructions.Length is 1 or 2
            && failureInstructions[0] is
                { OpCode: OpCode.Throw, Operands: [TypeAnalysisContext { FullName: "System.InvalidCastException" }] }
            && (failureInstructions.Length == 1 || failureInstructions[1].OpCode == OpCode.Return);
    }
}
