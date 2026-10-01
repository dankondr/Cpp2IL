using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A struct in a frame slot is several frame cells to the lifter: the slot itself and one cell
/// per other word the compiler stores separately. When the struct's address is passed to a call
/// (<c>MoveNext(&amp;enumerator)</c>), SSA versions the slot but not those cells, so a reload of a
/// cell after the call reads the copy stored before it: every <c>foreach</c> over a
/// <c>List&lt;T&gt;</c> read the enumerator's initial Current in the loop. A cell whose value is a
/// copy of that struct's own field at the cell's offset is the field's storage, so its reads
/// become reads of the field. Runs in SSA after types are known, before copies are forwarded.
/// </summary>
internal static class FrameStructFieldReads
{
    public static void Run(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var definitions = cfg.Instructions
            .Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!)
            .Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        // Only a struct whose address escapes can change behind the cells' backs.
        var addressed = cfg.Instructions.SelectMany(i => i.Operands)
            .Select(o => o is AddressOf { Target: LocalVariable target } ? target : null)
            .Where(l => l != null).ToHashSet();
        if (addressed.Count == 0)
            return;

        foreach (var instruction in cfg.Instructions)
        for (var i = 0; i < instruction.Operands.Count; i++)
        {
            if (instruction.Operands[i] is not LocalVariable cell || ReferenceEquals(instruction.Destination, cell) && i == 0
                || FieldOf(cell, []) is not { } field)
                continue;
            instruction.SetOperand(i, new FieldReference(field.Field, field.Local, field.Offset, field.Containers, field.AccessSize));
        }
        return;

        FieldReference? FieldOf(LocalVariable cell, HashSet<LocalVariable> visiting)
        {
            if (FrameOffset(cell) is not { } cellOffset || !visiting.Add(cell)
                || !definitions.TryGetValue(cell, out var definition))
                return null;
            switch (definition)
            {
                case { OpCode: OpCode.Move, Operands: [_, LocalVariable copied] }
                    when definitions.TryGetValue(copied, out var read)
                         && read is { OpCode: OpCode.Move, Operands: [_, FieldReference { Local: { Type.IsValueType: true } owner } field] }
                         && addressed.Contains(owner) && FrameOffset(owner) is { } ownerOffset
                         && cellOffset - ownerOffset == field.Offset && field.Offset > 0:
                    return field;
                case { OpCode: OpCode.Phi } phi:
                    var sources = phi.Operands.Skip(1).Select(s => s is LocalVariable source ? FieldOf(source, visiting) : null).ToList();
                    return sources.Count > 0 && sources.All(s => s != null && s.Field == sources[0]!.Field
                                                             && ReferenceEquals(s.Local, sources[0]!.Local))
                        ? sources[0] : null;
                default:
                    return null;
            }
        }
    }

    // The byte offset of a frame cell, from StackAnalyzer's `stack_N` / `stack_-N` names.
    private static long? FrameOffset(LocalVariable local)
    {
        var name = local.Register.Name;
        if (name == null || !name.StartsWith("stack_"))
            return null;
        var text = name["stack_".Length..];
        var negative = text.StartsWith('-');
        return long.TryParse(negative ? text[1..] : text, NumberStyles.HexNumber, null, out var value)
            ? negative ? -value : value
            : null;
    }
}
