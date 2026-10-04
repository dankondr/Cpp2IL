using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Witnesses that a frame span is one whole copy of a single source value.
///
/// The native lift splits a wide composite copy into one frame cell per register
/// word, filling each cell from the source's bytes (`ldp`/`stp` pairs), or calls
/// memcpy for the whole span. Dead code then collects every fill that nothing
/// else reads, so the copy is proven while the moves still exist and the proof
/// is kept for the passes that run after call resolution.
///
/// The recorded proof: a contiguous run of same-version frame cells whose single
/// definitions all read consecutive bytes of one base, covering `Bytes` bytes of
/// the value `Source` names - or one memcpy whose destination is the span. No
/// other instruction may write the run's cells or take their addresses, no
/// instruction may mutate or address the source, and every fill must dominate
/// every use of a taken address; under those, `&amp;cell` and the value at
/// `Source` are interchangeable for the whole body. When a later pass proves the
/// span is a by-value argument's caller-side copy, the argument spells the
/// source value - never the head cell, whose sibling words live under other
/// names.
/// </summary>
internal static class CopiedFrameSpanRecovery
{
    /// <summary>
    /// A frame span's proven whole-copy source: `Source` is the operand the span
    /// images (a local, field or memory referent), `Bytes` the number of
    /// contiguous bytes proven written from it.
    /// </summary>
    internal readonly record struct SpanCopy(IOperand Source, long Bytes);

    public static void Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not { } cfg)
            return;
        // A set (possibly empty) map means the witness ran; null means it never did.
        method.CopiedSpans ??= new();
        var instructions = cfg.Instructions;
        var definitions = SingleMoveDefinitions(instructions);
        // A local defined by a phi names the storage whichever edge ran. A
        // copy's cells may sit under phi-merged locals when the source copy
        // was performed on more than one path and merged.
        var phis = instructions
            .Where(i => i is { OpCode: OpCode.Phi, Destination: LocalVariable })
            .GroupBy(i => (LocalVariable)i.Destination!)
            .ToDictionary(g => g.Key, g => g.First());
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;

        // instruction -> (block, position in block), for the fill/use ordering check
        var placement = new Dictionary<Instruction, (Block Block, int Position)>();
        foreach (var block in cfg.Blocks)
            for (var i = 0; i < block.Instructions.Count; i++)
                placement[block.Instructions[i]] = (block, i);

        // Frame cells grouped by (SSA version, offset); a copy's cells are one
        // SSA generation, so a cohort shares the head's version.
        var cells = new Dictionary<(int Version, int Offset), LocalVariable>();
        foreach (var local in method.Locals)
            if (LocalVariables.TryStackOffset(local.Register.Name) is { } offset)
                cells.TryAdd((local.Register.Version, offset), local);
        var cellKeys = cells.Keys.ToList();

        // A span matters only where an address names it: `&cell` operands, and
        // memcpy destinations whose source a later pass may read.
        var heads = new HashSet<LocalVariable>();
        var copyCalls = new Dictionary<LocalVariable, (Instruction Call, IOperand Source, long Bytes)>();
        foreach (var instruction in instructions)
        {
            foreach (var operand in instruction.Operands)
                if (operand is AddressOf { Target: LocalVariable target })
                    heads.Add(target);
            if (BlockCopyCall(instruction, method, out var count)
                && ChaseCopyDestination(instruction.Operands[2], definitions) is AddressOf
                    { Target: LocalVariable destination })
            {
                heads.Add(destination);
                if (ChaseSource(instruction.Operands[3], definitions) is { } copySource)
                    copyCalls[destination] = (instruction, copySource, count);
            }
        }

        foreach (var head in heads)
        {
            if (LocalVariables.TryStackOffset(head.Register.Name) is not { } start)
                continue;

            List<Instruction> fills;
            List<LocalVariable> run;
            IOperand? source;
            long extent;
            if (copyCalls.TryGetValue(head, out var copyCall))
            {
                fills = [copyCall.Call];
                run = [head];
                source = copyCall.Source;
                extent = copyCall.Bytes;
            }
            else
            {
                // Per-word fills: a contiguous run of same-version cells, each
                // defined once by a move of the source's next bytes.
                fills = [];
                run = [];
                source = null;
                IOperand? spanBase = null;
                extent = 0;
                for (var offset = start; ;)
                {
                    if (!cells.TryGetValue((head.Register.Version, offset), out var cell)
                        || !definitions.TryGetValue(cell, out var fill)
                        || fill is not { OpCode: OpCode.Move, Operands: [_, var src] }
                        || ReadOf(src, definitions, phis, pointerSize) is not { } read
                        || read.Addend != offset - start
                        || read.Bytes <= 0
                        || (spanBase != null && !ReferenceEquals(read.Pointer, spanBase)))
                        break;
                    spanBase ??= read.Pointer;
                    if (source == null)
                    {
                        if (ChaseSource(read.Pointer, definitions) is not { } chased)
                            break;
                        source = chased;
                    }
                    fills.Add(fill);
                    run.Add(cell);
                    extent = offset - start + read.Bytes;
                    var next = cellKeys
                        .Where(k => k.Version == head.Register.Version && k.Offset > offset)
                        .Select(k => (int?)k.Offset).Min();
                    if (next is not { } following)
                        break;
                    offset = following;
                }
                if (extent <= 0 || source == null)
                    continue;
            }

            if (!FillIsExclusive(fills, run, head, instructions, placement, method)
                || !SourceIsStable(source, fills, instructions))
                continue;

            method.CopiedSpans[head] = new(source, extent);
        }
    }

    // The locals each defined by exactly one `Move local, source`. A cell that
    // gains a second definition is a different SSA generation of storage and is
    // never part of a frozen copy.
    private static Dictionary<LocalVariable, Instruction> SingleMoveDefinitions(List<Instruction> instructions)
        => instructions
            .Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!)
            .Where(g => g.Count() == 1 && g.Single() is { OpCode: OpCode.Move, Operands.Count: >= 2 })
            .ToDictionary(g => g.Key, g => g.Single());

    // The storage a fill's source reads: `[base + k]` names `base`, the field
    // `local.f@k` names `local`, and a local names whatever its own move copied.
    // `Bytes` is the fill's own width - the width of the value the move takes -
    // never wider than the read that produced it.
    private static (IOperand Pointer, long Addend, int Bytes)? ReadOf(IOperand operand,
        Dictionary<LocalVariable, Instruction> definitions,
        Dictionary<LocalVariable, Instruction> phis, int pointerSize)
    {
        var fillWidth = operand switch
        {
            LocalVariable local => LocalVariables.RegisterCoverageBytes(local.Register.Name, pointerSize),
            MemoryOperand memory => memory.AccessSize,
            FieldReference field => field.AccessSize,
            _ => 0,
        };
        if (fillWidth <= 0)
            return null;

        return TryRead(operand, definitions, phis, new HashSet<LocalVariable>()) is { } read
            ? (read.Pointer, read.Addend, read.Bytes > 0 ? Math.Min(fillWidth, read.Bytes) : fillWidth)
            : null;
    }

    // The terminal a read chases down to: `[pointer + k]` or `pointer.f@k`,
    // where pointer is a local without a move definition (a parameter, a call
    // result). A local with a phi definition names the same storage only when
    // every edge converges on the same (pointer, addend) - as when the two
    // sides of a branch each copied the same source into a merged frame cell.
    private static (IOperand Pointer, long Addend, int Bytes)? TryRead(IOperand operand,
        Dictionary<LocalVariable, Instruction> definitions,
        Dictionary<LocalVariable, Instruction> phis, HashSet<LocalVariable> seen)
    {
        var src = operand;
        var depth = 0;
        while (src is LocalVariable local)
        {
            if (depth++ > 64 || !seen.Add(local))
                return null;
            if (definitions.TryGetValue(local, out var def))
            {
                if (def is not { OpCode: OpCode.Move, Operands: [_, var next] })
                    return null;
                src = next;
                continue;
            }
            if (!phis.TryGetValue(local, out var phi))
                return null;
            var edges = phi.Operands.Skip(1).ToList();
            if (edges.Count is 0 or > 8)
                return null;
            (IOperand Pointer, long Addend, int Bytes)? merged = null;
            foreach (var edge in edges)
            {
                if (TryRead(edge, definitions, phis, new HashSet<LocalVariable>(seen)) is not { } read
                    || (merged is { } same
                        && (!ReferenceEquals(same.Pointer, read.Pointer) || same.Addend != read.Addend)))
                    return null;
                merged = merged is { } m ? (m.Pointer, m.Addend, Math.Min(m.Bytes, read.Bytes)) : read;
            }
            return merged;
        }
        var (pointer, addend, readBytes) = src switch
        {
            MemoryOperand { Index: null, Scale: 0, Base: { } memoryBase } memory =>
                (memoryBase, memory.Addend, memory.AccessSize),
            FieldReference field => ((IOperand)field.Local, (long)field.Offset, field.AccessSize),
            _ => (null, 0L, 0),
        };
        return pointer == null ? null : (pointer, addend, readBytes);
    }

    // What a value operand names once the address-copy moves are folded away: a
    // local defined only by `Move` from another local names that local's
    // storage, and `&x` names `x` itself. A local with a computed or loaded
    // definition is not a stable spelling - its definition may die with its
    // uses - so the chase stops there.
    private static IOperand? ChaseSource(IOperand operand, Dictionary<LocalVariable, Instruction> definitions)
    {
        var current = operand;
        var seen = new HashSet<LocalVariable>();
        while (current is LocalVariable local && seen.Add(local))
        {
            if (!definitions.TryGetValue(local, out var def))
                return local;
            if (def is not { OpCode: OpCode.Move, Operands: [_, var src] })
                return null;
            current = src;
        }
        return current is AddressOf { Target: { } target } ? target : null;
    }

    // Chase a memcpy destination (`x0`) through the moves that formed it to the
    // `&cell` it spells.
    private static IOperand? ChaseCopyDestination(IOperand operand,
        Dictionary<LocalVariable, Instruction> definitions)
    {
        var current = operand;
        var seen = new HashSet<LocalVariable>();
        while (current is LocalVariable local && seen.Add(local))
        {
            if (!definitions.TryGetValue(local, out var def)
                || def is not { OpCode: OpCode.Move, Operands: [_, var src] })
                return null;
            current = src;
        }
        return current;
    }

    // A Call lifted with the raw ABI layout whose target resolves to a block-copy
    // import: operands 2..4 are the X0..X2 argument slots (destination, source,
    // byte count) - the same layout NameImports rewrites later.
    private static bool BlockCopyCall(Instruction instruction, MethodAnalysisContext method, out long count)
    {
        count = 0;
        if (instruction is not { OpCode: OpCode.Call, Operands.Count: >= 5 }
            || instruction.Operands[0] is not Immediate { UnsignedValue: { } target }
            || instruction.Operands[4] is not Immediate { Value: > 0 } immediate
            || BlockMemoryImportRecovery.ResolveImportName(method.AppContext.Binary, target)
                is not ("memcpy" or "memmove"))
            return false;
        count = immediate.Value;
        return true;
    }

    // The copy is faithful only while its cells and its source are frozen: no
    // other write or address-of touches the run's non-head cells, `&head` may
    // appear only as a whole operand of a call, return, or a move that forwards
    // it, a local forwarded from `&head` may feed calls, returns and reads but
    // never a write, and every fill must dominate every use of the address.
    private static bool FillIsExclusive(List<Instruction> fills, List<LocalVariable> run,
        LocalVariable head, List<Instruction> instructions,
        Dictionary<Instruction, (Block Block, int Position)> placement, MethodAnalysisContext method)
    {
        var fillSet = fills.ToHashSet();
        var runSet = run.ToHashSet();
        var uses = new List<Instruction>();

        foreach (var instruction in instructions)
        {
            if (fillSet.Contains(instruction))
                continue;
            var destinationLocals = instruction.Destination is { } destination
                ? LocalVariables.OperandLocals(destination).ToHashSet()
                : [];
            foreach (var operand in instruction.Operands)
            {
                if (operand is AddressOf { Target: LocalVariable target })
                {
                    if (runSet.Contains(target))
                    {
                        if (!ReferenceEquals(target, head) || destinationLocals.Contains(head))
                            return false;
                        switch (instruction.OpCode)
                        {
                            case OpCode.Call or OpCode.CallVoid or OpCode.IndirectCall
                                or OpCode.Return:
                                uses.Add(instruction); // reads the span through the pointer
                                break;
                            case OpCode.Move:
                                // `Move d, &head` only captures the address - a read
                                // through it later is what must observe the fills. A
                                // move to memory lets the pointer escape; order it too.
                                if (instruction.Destination is not LocalVariable)
                                    uses.Add(instruction);
                                break;
                            default:
                                return false;
                        }
                    }
                }
                else
                {
                    foreach (var nested in NestedAddresses(operand))
                        if (nested.Target is LocalVariable nestedLocal && runSet.Contains(nestedLocal))
                            return false;
                }
            }
            if (runSet.Any(destinationLocals.Contains))
                return false;
        }

        // Forwarded pointer locals (`Move d, &head`, or a move of another
        // forward) may hand the address to calls, returns and memory reads, but
        // never to a write or an operand that respells it.
        var forwarded = new HashSet<LocalVariable>();
        var forwardedToProcess = new List<LocalVariable>();
        var forwardingDefs = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in instructions)
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable d, AddressOf { Target: LocalVariable t }] }
                && ReferenceEquals(t, head) && forwarded.Add(d))
            {
                forwardingDefs[d] = instruction;
                forwardedToProcess.Add(d);
            }
        while (forwardedToProcess.Count > 0)
        {
            var local = forwardedToProcess[^1];
            forwardedToProcess.RemoveAt(forwardedToProcess.Count - 1);
            var ownDef = forwardingDefs.GetValueOrDefault(local);
            foreach (var user in instructions)
            {
                if (fillSet.Contains(user) || user == ownDef)
                    continue;
                if (user.Destination is { } written && LocalVariables.OperandLocals(written).Contains(local))
                    return false;
                foreach (var operand in user.Operands.Skip(1))
                {
                    if (!LocalVariables.OperandLocals(operand).Contains(local))
                        continue;
                    var allowed = operand switch
                    {
                        // another forward, a phi or a call/return argument, or a
                        // read through the pointer - the copy's own bytes
                        LocalVariable => user.OpCode == OpCode.Move || user.IsCall
                            || user.OpCode == OpCode.Return || user.OpCode == OpCode.Phi,
                        MemoryOperand or FieldReference or ArrayAccess or ArrayLength => true,
                        _ => false,
                    };
                    if (!allowed)
                        return false;
                    // A forwarded local feeding anything but another respell is a
                    // read through the pointer: the fills must precede it.
                    if (!(operand is LocalVariable && user.OpCode is OpCode.Move or OpCode.Phi))
                        uses.Add(user);
                    // Moves and phis respell the pointer under a new name -
                    // follow it; everything else reads through it.
                    if (operand is LocalVariable
                        && user is { OpCode: OpCode.Move or OpCode.Phi, Destination: LocalVariable next }
                        && forwarded.Add(next))
                    {
                        forwardingDefs[next] = user;
                        forwardedToProcess.Add(next);
                    }
                }
            }
        }

        foreach (var fill in fills)
            foreach (var use in uses)
                if (!ExecutesBefore(fill, use, placement, method))
                    return false;
        return true;
    }

    private static bool ExecutesBefore(Instruction fill, Instruction use,
        Dictionary<Instruction, (Block Block, int Position)> placement, MethodAnalysisContext method)
    {
        if (!placement.TryGetValue(fill, out var f) || !placement.TryGetValue(use, out var u))
            return false;
        return f.Block == u.Block
            ? f.Position < u.Position
            : method.DominatorInfo?.Dominates(f.Block, u.Block) == true;
    }

    // The source operand's storage must stay frozen for the copy to image it: no
    // instruction writes the locals it reaches, and no instruction takes their
    // addresses. The fills are exempt - they read the source.
    private static bool SourceIsStable(IOperand source, List<Instruction> fills, List<Instruction> instructions)
    {
        var fillSet = fills.ToHashSet();
        var sourceLocals = LocalVariables.OperandLocals(source).ToHashSet();
        foreach (var instruction in instructions)
        {
            if (fillSet.Contains(instruction))
                continue;
            if (instruction.Destination is { } destination
                && LocalVariables.OperandLocals(destination).Any(sourceLocals.Contains))
                return false;
            foreach (var operand in instruction.Operands)
                if (operand is AddressOf { Target: { } target }
                    && LocalVariables.OperandLocals(target).Any(sourceLocals.Contains))
                    return false;
        }
        return true;
    }

    // Every `AddressOf` inside an operand, however deep. A nested one is a
    // pointer respelled for a write (`[reg + &cell]`), never an argument
    // position.
    private static IEnumerable<AddressOf> NestedAddresses(IOperand operand)
    {
        switch (operand)
        {
            case AddressOf { Target: not LocalVariable } address:
                foreach (var nested in NestedAddresses(address.Target))
                    yield return nested;
                break;
            case MemoryOperand memory:
                if (memory.Base is { } memoryBase)
                    foreach (var nested in NestedAddresses(memoryBase))
                        yield return nested;
                if (memory.Index is { } memoryIndex)
                    foreach (var nested in NestedAddresses(memoryIndex))
                        yield return nested;
                break;
            case ArrayAccess { Index: { } index }:
                foreach (var nested in NestedAddresses(index))
                    yield return nested;
                break;
            case ArrayElementFieldReference { Index: { } index }:
                foreach (var nested in NestedAddresses(index))
                    yield return nested;
                break;
            case ReferenceCast { Value: { } value }:
                foreach (var nested in NestedAddresses(value))
                    yield return nested;
                break;
        }
    }
}
