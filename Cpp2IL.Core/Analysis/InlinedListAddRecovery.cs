using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>Collapses IL2CPP's inlined List&lt;T&gt;.Add fast path back to the public Add call.</summary>
internal static class InlinedListAddRecovery
{
    private static readonly HashSet<string> InternalFields = ["_items", "_size", "_version"];

    internal static int Run(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph;
        if (cfg == null)
            return 0;

        var recovered = 0;
        while (TryRecoverOne(cfg))
        {
            recovered++;
            cfg.RemoveUnreachableBlocks();
        }
        return recovered;
    }

    private static bool TryRecoverOne(ISILControlFlowGraph cfg)
    {
        foreach (var slowBlock in cfg.Blocks.ToArray())
        foreach (var call in slowBlock.Instructions)
        {
            if (call.OpCode != OpCode.CallVoid || call.Operands.Count < 3
                || call.Operands[0] is not MethodAnalysisContext { Name: "AddWithResize" } callee
                || !IsList(callee.DeclaringType))
                continue;

            var start = FindInlineFastPathStart(slowBlock, cfg.EntryBlock);
            if (start == null)
                continue;

            foreach (var successor in start.Successors)
                successor.Predecessors.Remove(start);
            start.Successors.Clear();
            start.Instructions.Clear();
            start.Instructions.Add(new Instruction(call.Index, OpCode.Jump, slowBlock));
            start.Successors.Add(slowBlock);
            if (!slowBlock.Predecessors.Contains(start))
                slowBlock.Predecessors.Add(start);
            start.CalculateBlockType();
            return true;
        }
        return false;
    }

    private static Block? FindInlineFastPathStart(Block slowBlock, Block entry)
    {
        Block? start = null;
        var current = slowBlock.Predecessors.Count == 1 ? slowBlock.Predecessors[0] : null;
        var visited = new HashSet<Block>();
        while (current != null && current != entry && visited.Add(current))
        {
            if (current.Instructions.Any(TouchesInternalListField))
                start = current;
            if (current.Instructions.Any(instruction => instruction.IsCall)
                || current.Predecessors.Count != 1)
                break;
            current = current.Predecessors[0];
        }
        return start;
    }

    private static bool TouchesInternalListField(Instruction instruction) =>
        instruction.Operands.SelectMany(Fields).Any(field =>
            InternalFields.Contains(field.Field.Name) && IsList(field.Field.DeclaringType));

    private static bool IsList(TypeAnalysisContext? type) =>
        type?.DefaultFullName.StartsWith("System.Collections.Generic.List`1") == true
        || type is GenericInstanceTypeAnalysisContext { GenericType.DefaultFullName: "System.Collections.Generic.List`1" };

    private static IEnumerable<FieldReference> Fields(IOperand operand)
    {
        if (operand is FieldReference field)
            yield return field;
        else if (operand is AddressOf { Target: FieldReference addressed })
            yield return addressed;
        else if (operand is SelectedFieldReference selected)
            foreach (var choice in selected.Choices)
                yield return choice.Field;
    }
}
