using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Remove null and bounds checks which are explicit in il2cpp but implicit in IL
public static class InjectedCheckRemover
{
    public static void Run(MethodAnalysisContext method) => Run(method.ControlFlowGraph!);

    public static void Run(ISILControlFlowGraph cfg)
    {
        var defOf = BuildDefMap(cfg);
        var removedAny = false;

        foreach (var block in cfg.Blocks)
        {
            if (block.BlockType != BlockType.TwoWay || block.Instructions.Count == 0)
                continue;

            var terminator = block.Instructions[^1];

            if (terminator.OpCode != OpCode.ConditionalJump)
                continue;

            if (terminator.Operands[0] is not Block target || GetInjectedThrowType(target) is not { } thrownType)
                continue;

            if (terminator.Operands[1] is not LocalVariable condition
                || !defOf.TryGetValue(condition, out var definition)
                || !IsInjectedCheck(definition, thrownType))
                continue;

            terminator.OpCode = OpCode.Nop;
            terminator.SetOperands();

            block.Successors.Remove(target);
            target.Predecessors.Remove(block);
            block.CalculateBlockType();
            removedAny = true;
        }

        if (!removedAny)
            return;

        // delete any throw blocks
        cfg.RemoveUnreachableBlocks();
        DeadCodeEliminator.Run(cfg);
    }

    private static bool IsInjectedCheck(Instruction definition, string thrownType) =>
        thrownType switch
        {
            "System.NullReferenceException" => definition is { OpCode: OpCode.CheckEqual } && definition.Operands[2] is Immediate { Value: 0 },
            "System.IndexOutOfRangeException" => definition.OpCode is >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual,
            _ => false
        };

    internal static bool HasEquivalentImplicitFailure(MethodAnalysisContext method, Block throwBlock, string thrownType,
        ISet<Block> recoveredHelpers)
    {
        if (throwBlock.Instructions.LastOrDefault() is not { IsCall: true }
            || throwBlock.Instructions.Take(throwBlock.Instructions.Count - 1)
                .Any(instruction => instruction.OpCode is not (OpCode.Nop or OpCode.Phi)))
            return false;

        var cfg = method.ControlFlowGraph!;
        var definitions = BuildDefMap(cfg);
        var guards = 0;
        var terminalPredecessors = 0;
        var checkedReference = false;
        var checkedArray = false;
        var checkedElement = false;

        foreach (var predecessor in throwBlock.Predecessors)
        {
            if (predecessor.Instructions.LastOrDefault()?.OpCode == OpCode.Throw
                && recoveredHelpers.Contains(predecessor))
            {
                terminalPredecessors++;
                continue;
            }
            if (predecessor.Instructions.LastOrDefault() is { IsCall: true, Operands: [Immediate helperTarget, ..] }
                && NonReturningHelperRecovery.IsProven(method.AppContext, helperTarget.UnsignedValue))
            {
                terminalPredecessors++;
                continue;
            }

            if (predecessor is not { BlockType: BlockType.TwoWay, Successors.Count: 2 }
                || predecessor.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump, Operands: [Block branchTarget, LocalVariable condition] }
                || !ReferenceEquals(branchTarget, throwBlock)
                || !definitions.TryGetValue(condition, out var check)
                || !IsInjectedCheck(check, thrownType))
                return false;

            var survivor = predecessor.Successors.First(successor => !ReferenceEquals(successor, throwBlock));
            if (!HasImplicitFailure(survivor, check, thrownType, definitions, method.AppContext.Binary.PointerSizeBytes))
                return false;
            if (thrownType == "System.NullReferenceException" && NullCheckedValue(check, definitions) is { } checkedValue)
            {
                var isElement = IsArrayElementValue(checkedValue, definitions, method.AppContext.Binary.PointerSizeBytes);
                var isArray = IsArrayValue(checkedValue, definitions);
                checkedElement |= isElement;
                checkedArray |= isArray;
                checkedReference |= !isElement && !isArray && checkedValue is LocalVariable;
            }
            guards++;
        }

        return thrownType switch
        {
            "System.NullReferenceException" => guards == 3 && checkedReference && checkedArray && checkedElement,
            "System.IndexOutOfRangeException" => guards == 1 && terminalPredecessors != 0,
            _ => false
        };
    }

    private static bool HasImplicitFailure(Block block, Instruction check, string thrownType,
        Dictionary<LocalVariable, Instruction> definitions, int pointerSize)
    {
        if (check.Operands.Count < 3)
            return false;

        if (thrownType == "System.NullReferenceException"
            && NullCheckedValue(check, definitions) is { } reference)
            return FirstEffectDereferences(block, reference, definitions);

        if (thrownType == "System.IndexOutOfRangeException"
            && ZeroLengthArray(check, definitions, pointerSize) is { } array)
            return FirstEffectReadsElementZero(block, array, definitions, pointerSize);

        return false;
    }

    private static IOperand? NullCheckedValue(Instruction check, Dictionary<LocalVariable, Instruction> definitions)
    {
        if (check.OpCode is not (OpCode.CheckEqual or OpCode.CheckNotEqual))
            return null;
        if (check.Operands[1] is Immediate { Value: 0 })
            return ResolveValue(check.Operands[2], definitions);
        return check.Operands[2] is Immediate { Value: 0 } ? ResolveValue(check.Operands[1], definitions) : null;
    }

    private static LocalVariable? ZeroLengthArray(Instruction check, Dictionary<LocalVariable, Instruction> definitions, int pointerSize)
    {
        if (check.OpCode is not (OpCode.CheckEqual or OpCode.CheckNotEqual))
            return null;
        var value = check.Operands[1] is Immediate { Value: 0 } ? check.Operands[2]
            : check.Operands[2] is Immediate { Value: 0 } ? check.Operands[1] : null;
        if (value is not LocalVariable length || !definitions.TryGetValue(length, out var definition)
            || definition is not { OpCode: OpCode.Move, Operands: [_, var source] })
            return null;
        return source switch
        {
            ArrayLength { Array: var array } => ResolveLocal(array, definitions),
            MemoryOperand { Base: LocalVariable array, Index: null, Scale: 0, Addend: var offset }
                when offset == 3L * pointerSize => ResolveLocal(array, definitions),
            _ => null
        };
    }

    private static bool FirstEffectDereferences(Block block, IOperand reference,
        Dictionary<LocalVariable, Instruction> definitions)
        => FirstEffect(block, instruction =>
        {
            if (instruction.IsCall)
            {
                if (instruction.Operands[0] is not MethodAnalysisContext { IsStatic: false })
                    return false;
                var receiver = instruction.OpCode == OpCode.Call ? 2 : 1;
                return instruction.Operands.Count > receiver
                    && Equivalent(ResolveValue(instruction.Operands[receiver], definitions), reference, definitions);
            }
            return instruction.Sources.Any(source => Dereferences(source, reference, definitions));
        });

    private static bool FirstEffectReadsElementZero(Block block, LocalVariable array,
        Dictionary<LocalVariable, Instruction> definitions, int pointerSize)
        => FirstEffect(block, instruction => instruction.Sources.Any(source => source switch
        {
            ArrayAccess { Array: var candidate, Index: Immediate { Value: 0 } } =>
                ReferenceEquals(ResolveLocal(candidate, definitions), array),
            MemoryOperand { Base: LocalVariable candidate, Index: null, Scale: 0, Addend: var offset }
                when offset == 4L * pointerSize => ReferenceEquals(ResolveLocal(candidate, definitions), array),
            _ => false
        }));

    private static bool FirstEffect(Block start, Func<Instruction, bool> matches)
    {
        var block = start;
        for (var depth = 0; depth < 4; depth++)
        {
            foreach (var instruction in block.Instructions)
            {
                if (matches(instruction))
                    return true;
                if (instruction.IsCall || instruction.OpCode is OpCode.Return or OpCode.Throw or OpCode.ConditionalJump or OpCode.IndirectJump)
                    return false;
            }
            if (block.Successors is not [{ Predecessors.Count: 1 } next])
                return false;
            block = next;
        }
        return false;
    }

    private static bool Dereferences(IOperand operand, IOperand reference,
        Dictionary<LocalVariable, Instruction> definitions) => operand switch
    {
        MemoryOperand { Base: LocalVariable candidate } => Equivalent(ResolveValue(candidate, definitions), reference, definitions),
        ArrayLength { Array: var candidate } => Equivalent(ResolveValue(candidate, definitions), reference, definitions),
        ArrayAccess { Array: var candidate } => Equivalent(ResolveValue(candidate, definitions), reference, definitions),
        _ => false
    };

    private static bool Equivalent(IOperand? left, IOperand? right, Dictionary<LocalVariable, Instruction> definitions)
    {
        left = left == null ? null : ResolveValue(left, definitions);
        right = right == null ? null : ResolveValue(right, definitions);
        return (left, right) switch
        {
            (LocalVariable a, LocalVariable b) => ReferenceEquals(a, b),
            (Immediate a, Immediate b) => a.Value == b.Value,
            (ArrayAccess a, ArrayAccess b) => Equivalent(a.Array, b.Array, definitions)
                                                  && Equivalent(a.Index, b.Index, definitions),
            _ => false
        };
    }

    private static IOperand ResolveValue(IOperand operand, Dictionary<LocalVariable, Instruction> definitions)
        => ResolveLocal(operand, definitions) ?? operand;

    private static bool IsArrayValue(IOperand value, Dictionary<LocalVariable, Instruction> definitions)
    {
        if (value is not LocalVariable local)
            return false;
        if (local.Type is SzArrayTypeAnalysisContext)
            return true;
        return definitions.TryGetValue(local, out var definition)
            && definition.IsCall
            && definition.Operands[0] is MethodAnalysisContext { ReturnType: SzArrayTypeAnalysisContext };
    }

    private static bool IsArrayElementValue(IOperand value, Dictionary<LocalVariable, Instruction> definitions, int pointerSize)
    {
        if (value is ArrayAccess)
            return true;
        return value is LocalVariable local
            && definitions.TryGetValue(local, out var definition)
            && definition is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: LocalVariable array, Index: null, Scale: 0, Addend: var offset }] }
            && offset == 4L * pointerSize
            && IsArrayValue(array, definitions);
    }

    private static LocalVariable? ResolveLocal(IOperand operand, Dictionary<LocalVariable, Instruction> definitions)
    {
        var local = operand as LocalVariable;
        var seen = new HashSet<LocalVariable>();
        while (local != null && seen.Add(local) && definitions.TryGetValue(local, out var definition)
            && definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable source] })
            local = source;
        return local;
    }

    // The full name of the exception if this block does nothing but throw an injected check's exception, else null.
    private static string? GetInjectedThrowType(Block block)
    {
        string? thrown = null;

        foreach (var instruction in block.Instructions)
        {
            switch (instruction.OpCode)
            {
                case OpCode.Nop or OpCode.Interrupt:
                case OpCode.Return when thrown != null:
                    continue;

                case OpCode.Throw when thrown == null
                    && instruction.Operands is [TypeAnalysisContext { FullName: "System.NullReferenceException" or "System.IndexOutOfRangeException" } exception]:
                    thrown = exception.FullName;
                    continue;

                default:
                    return null;
            }
        }

        return thrown;
    }

    private static Dictionary<LocalVariable, Instruction> BuildDefMap(ISILControlFlowGraph cfg)
    {
        var defs = new Dictionary<LocalVariable, Instruction>();

        foreach (var instruction in cfg.Instructions)
            if (instruction.Destination is LocalVariable local)
                defs[local] = instruction;

        return defs;
    }
}
