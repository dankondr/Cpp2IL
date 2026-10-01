using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using Cpp2IL.Core.Graphs;
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

        // A struct returned in registers is reloaded from its frame slot right before the
        // return: lane 0 reads the slot, which SSA versions across the call that filled it
        // through its address, and each other lane reads a cell inside the slot, which it
        // does not. Lane 0 alone is the value.
        if (method.AppContext?.InstructionSet?.CallingConventionResolver is { } resolver && !method.IsVoid
            && !resolver.ReturnsViaHiddenBuffer(method)
            && resolver.ExtraLanes(method.ReturnType, resolver.ReturnRegister(method)) is { Count: > 0 } lanes)
            foreach (var block in cfg.Blocks)
            {
                if (block.Instructions is not [.., { OpCode: OpCode.Return } ret] || ret.Operands.Count != lanes.Count + 1
                    || Reload(ret.Operands[0], block) is not ({ Type: { } type } slot, var first)
                    || type.FullName != method.ReturnType.FullName || !addressed.Contains(slot)
                    || FrameOffset(slot) is not { } slotOffset)
                    continue;
                var reloads = lanes.Select((lane, k) => Reload(ret.Operands[k + 1], block) is var (cell, at)
                                                        && FrameOffset(cell) == slotOffset + lane.ByteOffset ? at : -1).ToList();
                var from = reloads.Append(first).Min();
                if (from >= 0 && block.Instructions.Skip(from).TakeWhile(i => i != ret)
                        .All(i => i.OpCode is OpCode.Nop || i is { OpCode: OpCode.Move, Operands: [LocalVariable, _] }))
                    ret.SetOperands(ret.Operands[0]);
            }
        return;

        // The frame local an operand reads at the end of `block`, and where it is read:
        // the local itself, or a copy of it made in that block.
        (LocalVariable Local, int Index)? Reload(IOperand operand, Block block)
        {
            if (operand is not LocalVariable local)
                return null;
            if (FrameOffset(local) != null)
                return (local, block.Instructions.Count - 1);
            return definitions.TryGetValue(local, out var copy) && copy is { OpCode: OpCode.Move, Operands: [_, LocalVariable source] }
                                                                && FrameOffset(source) != null && block.Instructions.IndexOf(copy) is >= 0 and var index
                ? (source, index)
                : null;
        }

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
    internal static long? FrameOffset(LocalVariable local)
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
