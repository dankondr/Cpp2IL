using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>Collapses IL2CPP's inlined List&lt;T&gt;.Clear body back to the public Clear call.</summary>
internal static class InlinedListClearRecovery
{
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
        foreach (var block in cfg.Blocks.ToArray())
        {
            var sizeStoreIndex = block.Instructions.FindIndex(instruction => instruction is
            {
                OpCode: OpCode.Move,
                Operands: [FieldReference { Field.Name: "_size" } size, Immediate { Value: 0 }]
            } && IsList(size.Field.DeclaringType));
            if (sizeStoreIndex < 0
                || block.Instructions[sizeStoreIndex].Operands[0] is not FieldReference sizeField
                || !block.Instructions.Any(instruction => instruction.Operands.OfType<FieldReference>().Any(field =>
                    ReferenceEquals(field.Local, sizeField.Local) && field.Field.Name == "_version"))
                || FindMerge(block) is not { } merge)
                continue;

            var listType = sizeField.Field.DeclaringType;
            var listDefinition = listType is GenericInstanceTypeAnalysisContext instanceType
                ? instanceType.GenericType
                : listType;
            var clear = listDefinition.Methods.FirstOrDefault(candidate => candidate.Name == "Clear"
                && !candidate.IsStatic && candidate.Parameters.Count == 0
                && (candidate.Attributes & MethodAttributes.MemberAccessMask) == MethodAttributes.Public);
            if (clear == null)
                continue;

            var evidence = ReceiverType(block.Instructions.Take(sizeStoreIndex), sizeField.Local)
                ?? sizeField.Local.Type;
            var target = evidence is GenericInstanceTypeAnalysisContext instance
                ? new ConcreteGenericMethodAnalysisContext(clear, instance.GenericArguments, [])
                : clear;
            var firstInternal = block.Instructions.FindIndex(instruction =>
                instruction.Operands.OfType<FieldReference>().Any(field =>
                    ReferenceEquals(field.Local, sizeField.Local) && field.Field.Name is "_size" or "_version"));
            if (firstInternal < 0)
                continue;

            block.Instructions.RemoveRange(firstInternal, block.Instructions.Count - firstInternal);
            block.Instructions.Add(new Instruction(sizeStoreIndex, OpCode.CallVoid, target, sizeField.Local));
            foreach (var successor in block.Successors)
                successor.Predecessors.Remove(block);
            block.Successors.Clear();
            block.Successors.Add(merge);
            if (!merge.Predecessors.Contains(block))
                merge.Predecessors.Add(block);
            block.CalculateBlockType();
            return true;
        }
        return false;
    }

    private static TypeAnalysisContext? ReceiverType(IEnumerable<Instruction> prefix, LocalVariable receiver)
    {
        foreach (var instruction in prefix.Reverse())
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable destination, FieldReference source] }
                && ReferenceEquals(destination, receiver) && IsList(source.Field.FieldType))
                return source.Field.FieldType;
        return null;
    }

    private static Block? FindMerge(Block start)
    {
        if (start.Successors.Count == 1)
            return start.Successors[0];
        if (start.Successors.Count != 2)
            return null;
        foreach (var candidate in start.Successors)
        {
            var other = start.Successors.First(successor => !ReferenceEquals(successor, candidate));
            var current = other;
            var visited = new HashSet<Block>();
            for (var depth = 0; depth < 4 && visited.Add(current); depth++)
            {
                if (ReferenceEquals(current, candidate))
                    return candidate;
                if (current.Successors.Count != 1)
                    break;
                current = current.Successors[0];
            }
        }

        // Clear at the end of a method has two equivalent terminal tails: return directly when
        // the list is empty, or Array.Clear and then return. The public Clear call replaces both.
        return start.Successors
            .Where(successor => successor.Instructions.Any(instruction => instruction.OpCode == OpCode.Return))
            .OrderBy(successor => successor.Instructions.Count(instruction => instruction.IsCall))
            .FirstOrDefault();
    }

    private static bool IsList(TypeAnalysisContext? type) =>
        type?.DefaultFullName.StartsWith("System.Collections.Generic.List`1") == true
        || type is GenericInstanceTypeAnalysisContext { GenericType.DefaultFullName: "System.Collections.Generic.List`1" };
}
