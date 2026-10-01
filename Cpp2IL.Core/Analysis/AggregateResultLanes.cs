using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// A value wider than one register arrives (or enters) with each lane in its own
/// register: a homogeneous float aggregate returns in V0..V(n-1), a 9-16 byte
/// composite in an X register pair. The call's destination names lane 0; the other
/// lanes ride as <see cref="Instruction.ImplicitDefinitions"/> so SSA gives reads
/// the call's version instead of the method-entry value.
///
/// This pass projects each lane local onto the field its bytes hold - the store of
/// V1 after `Transform.get_position` reads `result.y`, not an undefined register -
/// and treats aggregate parameters the same way at method entry: V1 there is
/// literally the parameter's lane 1. A lane is only projected when the callee's
/// return type (or the parameter's declared type) proves the aggregate and a field
/// of exactly the lane's width sits at the lane's offset; anything else keeps its
/// diagnostic, including registers a call resolved after SSA renaming could have
/// defined - those are checked per use through dominators, so a pre-call read of
/// the same register still reads the entry value.
/// </summary>
internal static class AggregateResultLanes
{
    public static bool Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph;
        var resolver = method.AppContext?.InstructionSet?.CallingConventionResolver;
        if (graph == null || resolver == null)
            return false;

        var pointerSize = method.AppContext!.Binary.PointerSizeBytes;
        var localsByRegister = new Dictionary<Register, LocalVariable>();
        foreach (var local in method.Locals)
            localsByRegister.TryAdd(local.Register, local);

        // A lane local's provenance: the field its bytes hold. A versioned implicit
        // def reaches every use of its local (SSA proved it); a def attached after
        // SSA renaming is only the reaching def on paths the call dominates, so
        // late defs are resolved per use.
        var provenLanes = new Dictionary<LocalVariable, FieldReference>();
        var splitLanes = new Dictionary<LocalVariable, (FieldReference Low, FieldReference High)>();
        var lateLanes = new Dictionary<int, List<(Instruction Call, FieldReference Projection)>>();

        foreach (var call in graph.Instructions)
        {
            if (call.OpCode != OpCode.Call || call.ImplicitDefinitions.Count == 0
                || call.Operands[0] is not MethodAnalysisContext callee
                || call.Destination is not LocalVariable result)
                continue;

            var concrete = Concrete(call, callee, method);
            var resultType = IlGenerator.EffectiveCallReturnType(concrete);
            var lanes = resolver.ExtraLanes(resultType, resolver.ReturnRegister(concrete));
            if (lanes.Count == 0)
                continue;

            foreach (var definition in call.ImplicitDefinitions)
            {
                var lane = lanes.FirstOrDefault(candidate => candidate.Register.Name == definition.Name);
                if (lane.Register.Name == null
                    || !localsByRegister.TryGetValue(definition, out var laneLocal))
                    continue;
                var projection = LaneField(resultType, result, lane, pointerSize);
                if (projection == null)
                {
                    if (definition.Version > 0 && SplitLane(resultType, result, lane, pointerSize) is { } split)
                        splitLanes[laneLocal] = split;
                    continue;
                }
                // The lane register holds this field's bytes alone, so the lane
                // local's honest type is the field's. A whole-aggregate type on
                // a lane register is a smear (a copy, a phi merge or the call's
                // own produced type filling the fill-only inference): a scalar
                // consumer cannot spell it and fails with an unspellable
                // VectorN operand. Fill the untyped case and unsmear exactly
                // the aggregate - anything else proven earlier stays.
                if (laneLocal.Type == null || laneLocal.Type.FullName == resultType.FullName)
                    laneLocal.Type = projection.Field.FieldType;
                if (definition.Version > 0)
                    provenLanes[laneLocal] = projection;
                else
                {
                    if (!lateLanes.TryGetValue(definition.Number, out var list))
                        lateLanes[definition.Number] = list = [];
                    list.Add((call, projection));
                }
            }
        }

        // Aggregate parameters: at method entry the parameter's lanes literally sit
        // in their registers, so an entry-version read of a lane register is a field
        // of the parameter - unless a call resolved after SSA defined the lane on
        // the path to that read (decided per use by dominance).
        var entryLanes = new Dictionary<LocalVariable, FieldReference>();
        var operandOffset = method.IsStatic ? 0 : 1;
        var created = false;
        for (var i = 0; i < method.Parameters.Count; i++)
        {
            var operandIndex = i + operandOffset;
            if (operandIndex >= method.ParameterOperands.Count
                || method.ParameterOperands[operandIndex] is not Register paramRegister)
                continue;

            var lanes = resolver.ExtraLanes(method.Parameters[i].ParameterType, paramRegister);
            if (lanes.Count == 0)
                continue;

            // A lane read at method-entry version can only be the parameter's lane;
            // without one there is nothing to project and the parameter needs no
            // local at all.
            var laneLocals = lanes
                .Select(lane => (Lane: lane, Local: localsByRegister.TryGetValue(lane.Register, out var candidate)
                    && candidate.Register.Version == -1 ? candidate : null))
                .Where(pair => pair.Local != null)
                .ToList();
            if (laneLocals.Count == 0)
                continue;

            // The parameter's lane-0 register can go unread and leave no local - a
            // method that only stores V1 of `Vector3 v` still proves the field read,
            // so the parameter gets the local CreateAll would have made for it.
            if (!localsByRegister.TryGetValue(paramRegister, out var paramLocal))
            {
                paramLocal = new LocalVariable(method.Parameters[i].ParameterName,
                    paramRegister, method.Parameters[i].ParameterType);
                method.Locals.Add(paramLocal);
                method.ParameterLocals.Add(paramLocal);
                localsByRegister[paramRegister] = paramLocal;
                created = true;
            }

            foreach (var (lane, laneLocal) in laneLocals)
            {
                var projection = LaneField(method.Parameters[i].ParameterType, paramLocal, lane, pointerSize);
                if (projection == null)
                {
                    if (SplitLane(method.Parameters[i].ParameterType, paramLocal, lane, pointerSize) is { } split)
                        splitLanes.TryAdd(laneLocal!, split);
                    continue;
                }
                if (laneLocal!.Type == null
                    || laneLocal.Type.FullName == method.Parameters[i].ParameterType.FullName)
                    laneLocal.Type = projection.Field.FieldType;
                entryLanes.TryAdd(laneLocal!, projection);
            }
        }

        // The method's own aggregate return comes back the same way: the lifter
        // puts each lane on the Return's operands, and the value is rebuilt from
        // the fields its bytes hold - before the projection loop below so the
        // operands still name their registers.
        var changed = RebuildAggregateReturns(method, resolver, pointerSize);
        changed |= BuildPackedStructValues(method, pointerSize);
        changed |= ProjectScalarReturns(method, resolver, pointerSize);
        changed |= DropLaneStoresOfWholeStores(method, resolver, pointerSize);
        changed |= ProjectSplitLanes(method, splitLanes);

        if (provenLanes.Count == 0 && lateLanes.Count == 0 && entryLanes.Count == 0)
            return created || changed;

        // Dominance for late-def and entry-lane per-use resolution - built here when
        // analysis did not already compute it (synthetic callers).
        var dominators = lateLanes.Count > 0
            ? method.DominatorInfo ?? new DominatorInfo(graph)
            : null;

        // The lane field a use of `local` reads: the proven call's lane everywhere,
        // otherwise the nearest lane call dominating this use, otherwise the
        // parameter lane the entry value holds.
        FieldReference? ProjectionFor(LocalVariable local, int useIndex, Block useBlock)
        {
            if (provenLanes.TryGetValue(local, out var proven))
                return proven;

            if (local.Register.Version == -1)
            {
                if (lateLanes.TryGetValue(local.Register.Number, out var candidates))
                {
                    // In the use's own block the reaching lane call is the last one
                    // before the use; otherwise the last lane call in the nearest
                    // dominator block that contains one.
                    for (var scanBlock = (Block?)useBlock; scanBlock != null;
                         scanBlock = dominators!.ImmediateDominators.GetValueOrDefault(scanBlock))
                    {
                        var limit = scanBlock == useBlock ? useIndex : scanBlock.Instructions.Count;
                        for (var i = limit - 1; i >= 0; i--)
                        {
                            var earlier = scanBlock.Instructions[i];
                            var candidate = candidates.FirstOrDefault(c => ReferenceEquals(c.Call, earlier));
                            if (candidate.Call != null)
                                return candidate.Projection;
                        }
                    }
                }

                if (entryLanes.TryGetValue(local, out var entry))
                    return entry;
            }

            return null;
        }

        foreach (var block in graph.Blocks)
        {
            for (var instructionIndex = 0; instructionIndex < block.Instructions.Count; instructionIndex++)
            {
                var instruction = block.Instructions[instructionIndex];
                for (var operandIndex = 0; operandIndex < instruction.Operands.Count; operandIndex++)
                {
                    FieldReference? projection;
                    switch (instruction.Operands[operandIndex])
                    {
                        case LocalVariable local
                            when (projection = ProjectionFor(local, instructionIndex, block)) != null:
                            instruction.SetOperand(operandIndex, Clone(projection));
                            changed = true;
                            break;
                        case AddressOf { Target: LocalVariable addressed }
                            when (projection = ProjectionFor(addressed, instructionIndex, block)) != null:
                            instruction.SetOperand(operandIndex, new AddressOf(Clone(projection)));
                            changed = true;
                            break;
                        case MemoryOperand memory:
                            var touched = false;
                            if (memory.Base is LocalVariable baseLocal
                                && (projection = ProjectionFor(baseLocal, instructionIndex, block)) != null)
                            {
                                memory.Base = Clone(projection);
                                touched = true;
                            }
                            if (memory.Index is LocalVariable indexLocal
                                && (projection = ProjectionFor(indexLocal, instructionIndex, block)) != null)
                            {
                                memory.Index = Clone(projection);
                                touched = true;
                            }
                            if (touched)
                            {
                                instruction.SetOperand(operandIndex, memory);
                                changed = true;
                            }
                            break;
                    }
                }
            }
        }

        // A memory-width read of a whole aggregate local names only the field its
        // bytes cover - `STR S0` of a Vector3 result stores `.x`, not the value.
        changed |= NarrowWholeAggregateReads(method, pointerSize);

        return changed || created;
    }

    // A multi-register result leaves the method in its lanes: the lifter puts
    // each lane register on the Return's operands (lane 0 first, then the extra
    // lanes in order). Rebuild the value as a local of the return type with each
    // lane stored into the field its bytes hold - the same exact-width rule as
    // call-side projection - so `SCVTF S0,W19; SCVTF S1,W0; RET` of a Vector2
    // method returns `new Vector2(x, y)` instead of one Int32 lane plus a
    // conversion failure. A Return whose operands no longer name the lane
    // registers, or whose fields cannot all be proven, keeps its operands for
    // the default-fill note.
    private static bool RebuildAggregateReturns(MethodAnalysisContext method,
        BaseCallingConventionResolver resolver, int pointerSize)
    {
        if (method.IsVoid || resolver.ReturnsViaHiddenBuffer(method))
            return false;

        var firstLane = resolver.ReturnRegister(method);
        var lanes = resolver.ExtraLanes(method.ReturnType, firstLane);
        // A composite of at most eight bytes has no extra lane: its one register is the
        // whole value, rebuilt here only when it was packed from two 32-bit halves.
        var firstWidth = lanes.Count > 0 ? lanes[0].ByteOffset
            : IsWholePackedPair(method.ReturnType, pointerSize) ? 8 : 0;
        if (firstWidth == 0)
            return false;
        var definitions = SingleDefinitions(method);

        var changed = false;
        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            for (var index = 0; index < block.Instructions.Count; index++)
            {
                var instruction = block.Instructions[index];
                if (instruction.OpCode != OpCode.Return
                    || instruction.Operands.Count != lanes.Count + 1
                    || LaneOperand(instruction.Operands[0], firstLane.Name) is not { } lane0)
                    continue;

                // Each operand must still name the register of the lane at its
                // position - lane 0 covering [0, lanes[0].ByteOffset).
                var sources = new List<(IOperand Operand, int Offset, int Width)>
                    { (lane0, 0, firstWidth) };
                var proven = true;
                for (var laneIndex = 0; laneIndex < lanes.Count; laneIndex++)
                {
                    if (LaneOperand(instruction.Operands[laneIndex + 1], lanes[laneIndex].Register.Name)
                            is not { } source)
                    {
                        proven = false;
                        break;
                    }
                    sources.Add((source, lanes[laneIndex].ByteOffset, lanes[laneIndex].AccessSize));
                }
                if (!proven)
                    continue;

                // Lane 0 holding a call's whole result of the return type, with every other
                // lane that call's own lane register, is the value passed through unchanged,
                // however its fields straddle the lanes (`Nullable<DateTime>`, `UniTask`).
                if (lanes.Count > 0 && lane0 is LocalVariable { Type: { } wholeType } whole
                    && wholeType.FullName == method.ReturnType.FullName
                    && method.ControlFlowGraph.Instructions.FirstOrDefault(i => ReferenceEquals(i.Destination, whole)) is
                        { OpCode: OpCode.Call } call
                    && CallResultType(call, method)?.FullName == wholeType.FullName
                    && sources.Skip(1).All(source => source.Operand is LocalVariable { Register: { Version: > 0 } register }
                                                     && call.ImplicitDefinitions.Contains(register)))
                {
                    instruction.SetOperands(whole);
                    changed = true;
                    continue;
                }

                // The same for a parameter of the return type still in its entry registers:
                // `I4 Identity(I4 v) => v` is a bare `ret`.
                if (lanes.Count > 0 && EntryParameterPassedThrough(method, resolver, sources.Select(s => s.Operand).ToList(),
                        definitions) is { } parameter)
                {
                    instruction.SetOperands(parameter);
                    changed = true;
                    continue;
                }

                var stores = new List<(FieldReference Target, IOperand Value)>();
                var prelude = new List<Instruction>();
                var result = new LocalVariable($"aggregateResult_{instruction.Index}",
                    new Register(null, $"ARET_{instruction.Index}"), method.ReturnType);
                foreach (var (operand, offset, width) in sources)
                {
                    if (MetadataResolver.FindInstanceFieldPathAtOffset(method.ReturnType, offset, width)
                            is { } path
                        && TypeSizes.MinimumUnboxedSize(path.Field.FieldType, pointerSize) == width)
                        stores.Add((new FieldReference(path.Field, result, offset, path.Containers, width),
                            LaneValue(operand, width, pointerSize)));
                    // An eight-byte lane can hold two 32-bit fields packed by the method.
                    else if (width == 8
                             && PackedHalves(operand, method.ReturnType, offset, result, definitions, method, prelude,
                                 pointerSize) is { } halves)
                        stores.AddRange(halves);
                    else
                    {
                        proven = false;
                        break;
                    }
                }
                if (!proven)
                    continue;

                method.Locals.Add(result);
                var built = BuildInstructions(method, instruction.Index, prelude, stores);
                block.Instructions.InsertRange(index, built);
                instruction.SetOperands(result);
                index += built.Count;
                changed = true;
            }
        }

        return changed;
    }

    // A method returning one scalar can hand back lane 0 of an aggregate call result as is:
    // `float X(Transform t) => t.position.x` is `b Transform.get_position`, and the caller's S0
    // is the callee's `x`. The value returned is that lane's field, not the whole aggregate.
    private static bool ProjectScalarReturns(MethodAnalysisContext method, BaseCallingConventionResolver resolver,
        int pointerSize)
    {
        if (method.IsVoid || resolver.ExtraLanes(method.ReturnType, resolver.ReturnRegister(method)).Count > 0)
            return false;
        var changed = false;
        var instructions = method.ControlFlowGraph!.Instructions;
        foreach (var ret in instructions.Where(i => i.OpCode == OpCode.Return))
        {
            if (ret.Operands is not [LocalVariable result]
                || instructions.FirstOrDefault(i => ReferenceEquals(i.Destination, result)) is not
                    { OpCode: OpCode.Call, Operands: [MethodAnalysisContext callee, ..] } call
                || resolver.ReturnRegister(Concrete(call, callee, method)) is var laneZero
                   && laneZero.Name != resolver.ReturnRegister(method).Name
                || CallResultType(call, method) is not { IsValueType: true } aggregate
                || resolver.ExtraLanes(aggregate, laneZero) is not { Count: > 0 } lanes
                || MetadataResolver.FindInstanceFieldPathAtOffset(aggregate, 0, lanes[0].ByteOffset) is not { } path
                || path.Field.FieldType.FullName != method.ReturnType.FullName
                || TypeSizes.MinimumUnboxedSize(path.Field.FieldType, pointerSize) != lanes[0].ByteOffset
                || instructions.Any(i => i != ret && i != call && DeadCodeEliminator.UsedLocals(i).Contains(result)))
                continue;
            result.Type = aggregate;
            ret.SetOperand(0, new FieldReference(path.Field, result, 0, path.Containers, lanes[0].ByteOffset));
            changed = true;
        }
        return changed;
    }

    // `stp x0, x1, [x19, #0x60]` after a call returning a 16-byte struct lifts to a store of the
    // whole result (lane 0's local carries the struct) and a raw store of X1 eight bytes further.
    // Once the first store writes the whole value, the lane stores rewrite bytes it already wrote
    // with the same call's other lanes: they are part of it, not values of their own.
    private static bool DropLaneStoresOfWholeStores(MethodAnalysisContext method, BaseCallingConventionResolver resolver,
        int pointerSize)
    {
        var changed = false;
        var calls = method.ControlFlowGraph!.Instructions
            .Where(i => i is { OpCode: OpCode.Call, Destination: LocalVariable, Operands: [MethodAnalysisContext, ..] }
                        && i.ImplicitDefinitions.Count > 0)
            .ToDictionary(i => (LocalVariable)i.Destination!);
        if (calls.Count == 0)
            return false;
        // The lane often reaches the store through a register copy (`mov x8, x1; stp x0, x8, [x19]`).
        var copies = method.ControlFlowGraph.Instructions
            .Where(i => i is { OpCode: OpCode.Move, Operands: [LocalVariable, LocalVariable] })
            .GroupBy(i => (LocalVariable)i.Operands[0])
            .Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => (LocalVariable)g.Single().Operands[1]);
        LocalVariable Copied(LocalVariable local)
        {
            for (var depth = 0; depth < 4 && copies.TryGetValue(local, out var source); depth++)
                local = source;
            return local;
        }

        foreach (var block in method.ControlFlowGraph.Blocks)
        for (var index = 0; index < block.Instructions.Count; index++)
        {
            if (block.Instructions[index] is not { OpCode: OpCode.Move, Operands: [var target, LocalVariable { Type: { } wholeType } whole] } store
                || !calls.TryGetValue(whole, out var call))
                continue;
            var concrete = Concrete(call, (MethodAnalysisContext)call.Operands[0], method);
            // Lanes that are each one field are projected onto those fields instead (`res.y`).
            if (IlGenerator.EffectiveCallReturnType(concrete).FullName != wholeType.FullName
                || resolver.ExtraLanes(wholeType, resolver.ReturnRegister(concrete)) is not { Count: > 0 } lanes
                || lanes.All(lane => LaneField(wholeType, whole, lane, pointerSize) != null))
                continue;
            // The store must write the whole value: a field of the result's own type, or a raw cell
            // the lane stores below are relative to.
            var (holder, offset) = target switch
            {
                FieldReference { Local: { } fieldHolder, Field.FieldType: var fieldType } field
                    when fieldType.FullName == wholeType.FullName => (fieldHolder, field.Offset),
                MemoryOperand { Base: LocalVariable memoryBase, Index: null } memory => (memoryBase, memory.Addend),
                _ => ((LocalVariable?)null, 0L),
            };
            if (holder == null)
                continue;

            var laneStores = new List<Instruction>();
            for (var next = index + 1; next < block.Instructions.Count && laneStores.Count < lanes.Count; next++)
            {
                var candidate = block.Instructions[next];
                var lane = lanes[laneStores.Count];
                if (candidate is { OpCode: OpCode.Move, Operands: [MemoryOperand { Base: LocalVariable laneBase, Index: null } laneCell, LocalVariable laneValue] }
                    && ReferenceEquals(laneBase, holder) && laneCell.Addend == offset + lane.ByteOffset
                    && Copied(laneValue).Register is { Version: > 0 } laneRegister && laneRegister.Name == lane.Register.Name
                    && call.ImplicitDefinitions.Contains(laneRegister))
                    laneStores.Add(candidate);
                else if (candidate is not ({ OpCode: OpCode.Nop } or { OpCode: OpCode.Move, Operands: [LocalVariable, _] }))
                    break;
            }
            if (laneStores.Count != lanes.Count)
                continue;

            foreach (var laneStore in laneStores)
            {
                laneStore.OpCode = OpCode.Nop;
                laneStore.SetOperands();
            }
            var width = lanes[^1].ByteOffset + lanes[^1].AccessSize;
            store.NativeMemoryAccessSize = width;
            if (target is MemoryOperand cell)
                store.SetOperand(0, new MemoryOperand(cell.Base, cell.Index, cell.Addend, cell.Scale, width));
            changed = true;
        }
        return changed;
    }

    // A composite of two 32-bit integer fields fills one X register, and clang builds it there
    // from the halves: `mov w8, w0; orr x0, x8, x1, lsl #32` is `new I2 { A = a, B = b }` (the
    // low half zero-extended first; a pre-scaled high half shifts further, `b * 2` is
    // `lsl #33`), a constant pair is one wide literal. Lifted, that is an integer Or no struct
    // slot can take - a field store, a local or phi of the struct type. Rebuild the value as a
    // local of the slot's type with each half stored into its field; the return lanes are
    // rebuilt the same way above. Anything that is not such a pair keeps its diagnostic.
    private static bool BuildPackedStructValues(MethodAnalysisContext method, int pointerSize)
    {
        var graph = method.ControlFlowGraph!;
        var definitions = SingleDefinitions(method);
        var edits = new List<(Instruction Consumer, int OperandIndex, Block At, Instruction? Before,
            LocalVariable Value, List<Instruction> Built)>();
        foreach (var block in graph.Blocks)
        foreach (var instruction in block.Instructions)
        {
            if (instruction.OpCode is not (OpCode.Move or OpCode.Phi))
                continue;
            var slot = instruction.Operands[0] switch
            {
                LocalVariable { Type: { } localType } => localType,
                FieldReference field when instruction.OpCode == OpCode.Move => field.Field.FieldType,
                _ => null,
            };
            if (slot == null || !IsWholePackedPair(slot, pointerSize))
                continue;
            for (var operandIndex = 1; operandIndex < instruction.Operands.Count; operandIndex++)
            {
                var operand = instruction.Operands[operandIndex];
                if (operand is LocalVariable { Type: { } operandType } && operandType.FullName == slot.FullName
                    && !(definitions.TryGetValue((LocalVariable)operand, out var producer) && producer.OpCode == OpCode.Or))
                    continue;
                var prelude = new List<Instruction>();
                var value = new LocalVariable($"packedValue{method.Locals.Count + edits.Count}",
                    new Register(null, $"PACKED{method.Locals.Count + edits.Count}"), slot);
                // A word alone is a pair with a zero high half only where the slot's type is
                // metadata (a field), not a register local's inferred type.
                if (PackedHalves(operand, slot, 0, value, definitions, method, prelude, pointerSize,
                        allowLoneWord: instruction.Operands[0] is FieldReference) is not { } halves)
                    continue;
                var built = BuildInstructions(method, instruction.Index, prelude, halves);
                // A phi input is built on its edge, at the end of the predecessor it comes from.
                edits.Add(instruction.OpCode == OpCode.Phi
                    ? (instruction, operandIndex, block.Predecessors[operandIndex - 1], null, value, built)
                    : (instruction, operandIndex, block, instruction, value, built));
            }
        }

        foreach (var (consumer, operandIndex, at, before, value, built) in edits)
        {
            method.Locals.Add(value);
            if (before != null)
                at.Instructions.InsertRange(at.Instructions.IndexOf(before), built);
            else
                SsaForm.InsertBeforeTerminator(at, built);
            consumer.SetOperand(operandIndex, value);
        }
        return edits.Count > 0;
    }

    // A value type with two 4-byte integer fields at `offset` and `offset + 4`.
    private static bool IsPackedPair(TypeAnalysisContext type, int offset, int pointerSize)
        => type is { IsValueType: true } && IlGenerator.IntegralStackWidth(type) == 0
           && HalfField(type, offset, pointerSize) != null && HalfField(type, offset + 4, pointerSize) != null;

    // An eight-byte value type that is exactly such a pair: one X register holds all of it.
    private static bool IsWholePackedPair(TypeAnalysisContext type, int pointerSize)
        => IsPackedPair(type, 0, pointerSize) && TypeSizes.MinimumUnboxedSize(type, pointerSize) == 8;

    private static (FieldAnalysisContext Field, IReadOnlyList<FieldAnalysisContext> Containers)? HalfField(
        TypeAnalysisContext type, int offset, int pointerSize)
        => MetadataResolver.FindInstanceFieldPathAtOffset(type, offset, 4) is { } path
           && TypeSizes.MinimumUnboxedSize(path.Field.FieldType, pointerSize) == 4
           && IlGenerator.IntegralStackWidth(path.Field.FieldType) == 4
            ? path
            : null;

    // The two field stores of an eight-byte region of `type` at `offset` whose value is a pair
    // of 32-bit halves - `lo | hi << 32`, `hi << 32`, a zero-extended word alone (when the
    // caller allows it), or a literal proven for all eight bytes - or null. A high half
    // shifted past 32 bits gets its own 32-bit shift in `prelude`.
    private static List<(FieldReference Target, IOperand Value)>? PackedHalves(IOperand value,
        TypeAnalysisContext type, int offset, LocalVariable holder,
        Dictionary<LocalVariable, Instruction> definitions, MethodAnalysisContext method,
        List<Instruction> prelude, int pointerSize, bool allowLoneWord = true)
    {
        if (!IsPackedPair(type, offset, pointerSize))
            return null;

        value = Copied(value, definitions);
        IOperand? low = null, high = null;
        if (value is Immediate { EffectiveProvenBytes: 8 } wide)
            (low, high) = (new Immediate((int)wide.Value, 4), new Immediate((int)(wide.Value >> 32), 4));
        else if (value is LocalVariable local && definitions.TryGetValue(local, out var definition)
                 && definition.NativeIntegerWidthBits != 32)
        {
            if (definition is { OpCode: OpCode.Or, Operands: [_, var left, var right] })
            {
                if (HighHalf(right, definitions, method, prelude) is { } rightHigh
                    && IsZeroExtendedWord(left, definitions, method, []))
                    (low, high) = (left, rightHigh);
                else if (HighHalf(left, definitions, method, prelude) is { } leftHigh
                         && IsZeroExtendedWord(right, definitions, method, []))
                    (low, high) = (right, leftHigh);
            }
            else if (definition.OpCode == OpCode.ShiftLeft
                     && HighHalf(local, definitions, method, prelude) is { } shifted)
                (low, high) = (new Immediate(0, 4), shifted);
        }
        if (low == null && allowLoneWord && value is LocalVariable && IsZeroExtendedWord(value, definitions, method, []))
            (low, high) = (value, new Immediate(0, 4));
        if (low == null || high == null || !IsWordValue(low) || !IsWordValue(high))
            return null;

        var (lowField, lowContainers) = HalfField(type, offset, pointerSize)!.Value;
        var (highField, highContainers) = HalfField(type, offset + 4, pointerSize)!.Value;
        return
        [
            (new FieldReference(lowField, holder, offset, lowContainers, 4), low),
            (new FieldReference(highField, holder, offset + 4, highContainers, 4), high),
        ];
    }

    // The 32-bit value a 64-bit `x << n` (32 <= n < 64) puts in the upper half: `x` itself, or
    // `x << (n - 32)` computed as a 32-bit shift.
    private static IOperand? HighHalf(IOperand operand, Dictionary<LocalVariable, Instruction> definitions,
        MethodAnalysisContext method, List<Instruction> prelude)
    {
        if (Copied(operand, definitions) is not LocalVariable local
            || !definitions.TryGetValue(local, out var shift)
            || shift is not { OpCode: OpCode.ShiftLeft, Operands: [_, var shifted, Immediate { Value: >= 32 and < 64 } count] }
            || shift.NativeIntegerWidthBits == 32
            || !IsWordValue(shifted))
            return null;
        if (count.Value == 32)
            return shifted;
        var scaled = new LocalVariable($"packedHigh{method.Locals.Count + prelude.Count}",
            new Register(null, $"PACKEDHIGH{method.Locals.Count + prelude.Count}"),
            method.AppContext.SystemTypes.SystemInt32Type);
        prelude.Add(new Instruction(shift.Index, OpCode.ShiftLeft, scaled, shifted, new Immediate(count.Value - 32))
            { NativeIntegerWidthBits = 32 });
        return scaled;
    }

    // A value IL can store into a 4-byte integer field as is.
    private static bool IsWordValue(IOperand operand)
        => operand is Immediate || operand is LocalVariable { Type: { } type } && IlGenerator.IntegralStackWidth(type) == 4;

    // Whether the upper 32 bits of the register holding `operand` are zero, so `operand` fills
    // only the low half of a pair: a 32-bit literal, a load of at most four bytes, a 32-bit
    // operation (recorded as a W-register write, or typed as a 4-byte integer - the lift does
    // not record the width of every W-register op), a 32-bit parameter or call result (clang
    // zero-extends those with a `mov wN, wM` the lift forwards away) - directly or through
    // copies and phis. A 64-bit shift or Or is itself a packed value, never a half.
    private static bool IsZeroExtendedWord(IOperand operand, Dictionary<LocalVariable, Instruction> definitions,
        MethodAnalysisContext method, HashSet<LocalVariable> visiting)
    {
        switch (operand)
        {
            case Immediate immediate:
                return immediate.ProvenBytes == 4 || immediate.Value is >= 0 and <= uint.MaxValue;
            case LocalVariable local:
                if (!visiting.Add(local))
                    return true;
                if (!definitions.TryGetValue(local, out var definition))
                    return method.ParameterLocals.Contains(local) && IsWordType(local.Type, method);
                return definition switch
                {
                    { NativeIntegerWidthBits: { } bits } => bits == 32,
                    { OpCode: OpCode.Move, NativeMemoryAccessSize: { } loaded } => loaded is >= 1 and <= 4,
                    { OpCode: OpCode.Move, Operands: [_, var source] }
                        => IsZeroExtendedWord(source, definitions, method, visiting),
                    { OpCode: OpCode.Phi } => definition.Operands.Skip(1)
                        .All(input => IsZeroExtendedWord(input, definitions, method, visiting)),
                    { OpCode: OpCode.Call, Operands: [MethodAnalysisContext callee, ..] }
                        => IsWordType(callee.ReturnType, method),
                    { OpCode: OpCode.Or or OpCode.ShiftLeft or OpCode.Call or OpCode.CallVoid } => false,
                    _ => IsWordType(local.Type, method),
                };
            default:
                return false;
        }
    }

    private static bool IsWordType(TypeAnalysisContext? type, MethodAnalysisContext method)
        => IlGenerator.IntegralStackWidth(type) == 4
           && TypeSizes.MinimumUnboxedSize(type!, method.AppContext.Binary.PointerSizeBytes) == 4;

    // A register copy chain (`mov x1, x8`) leads to the value it copies.
    private static IOperand Copied(IOperand operand, Dictionary<LocalVariable, Instruction> definitions)
    {
        for (var depth = 0; depth < 8 && operand is LocalVariable local
                            && definitions.TryGetValue(local, out var copy)
                            && copy is { OpCode: OpCode.Move, NativeMemoryAccessSize: null, Operands: [_, LocalVariable or Immediate] }; depth++)
            operand = copy.Operands[1];
        return operand;
    }

    private static List<Instruction> BuildInstructions(MethodAnalysisContext method, int index,
        List<Instruction> prelude, List<(FieldReference Target, IOperand Value)> stores)
    {
        foreach (var scaled in prelude)
            method.Locals.Add((LocalVariable)scaled.Destination!);
        return prelude.Concat(stores.Select(store => new Instruction(index, OpCode.Move, store.Target, store.Value)
            { NativeMemoryAccessSize = store.Target.AccessSize })).ToList();
    }

    private static Dictionary<LocalVariable, Instruction> SingleDefinitions(MethodAnalysisContext method)
        => method.ControlFlowGraph!.Instructions
            .Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!)
            .Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());

    // The parameter of the return type whose entry registers every return lane still holds
    // (through register copies), or null.
    private static LocalVariable? EntryParameterPassedThrough(MethodAnalysisContext method,
        BaseCallingConventionResolver resolver, List<IOperand> laneValues, Dictionary<LocalVariable, Instruction> definitions)
    {
        if (Copied(laneValues[0], definitions) is not LocalVariable { Register.Version: -1 } parameter
            || !method.ParameterLocals.Contains(parameter)
            || parameter.Type?.FullName != method.ReturnType.FullName)
            return null;
        var parameterLanes = resolver.ExtraLanes(parameter.Type, parameter.Register);
        if (parameterLanes.Count != laneValues.Count - 1
            || method.ControlFlowGraph!.Instructions.Any(i => i.ImplicitDefinitions.Any(d => parameterLanes.Any(l => l.Register.Name == d.Name))))
            return null;
        for (var k = 0; k < parameterLanes.Count; k++)
            if (Copied(laneValues[k + 1], definitions) is not LocalVariable { Register: { Version: -1 } register }
                || register.Name != parameterLanes[k].Register.Name)
                return null;
        return parameter;
    }

    private static MethodAnalysisContext Concrete(Instruction call, MethodAnalysisContext callee, MethodAnalysisContext method)
        => !callee.IsStatic && call.Operands.Count > 2
            ? IlGenerator.RetargetToReceiverInstantiation(callee,
                IlGenerator.SharedGenericEvidenceType(call.Operands[2], method))
            : callee;

    private static TypeAnalysisContext? CallResultType(Instruction call, MethodAnalysisContext method)
        => call.Operands[0] is MethodAnalysisContext callee
            ? IlGenerator.EffectiveCallReturnType(Concrete(call, callee, method))
            : null;

    private static IOperand? LaneOperand(IOperand operand, string? registerName) => operand switch
    {
        Register register when register.Name == registerName => register,
        LocalVariable { Register.Name: var name } local when name == registerName => local,
        _ => null
    };

    // The lane operand emits exactly its width: a local typed wider than the lane
    // (the whole-call-result local sits in lane 0 of a passthrough return) narrows
    // to the field covering the lane's bytes, the same rule as for reads.
    private static IOperand LaneValue(IOperand operand, int width, int pointerSize)
        => operand is LocalVariable { Type: { } type } local
           && TypeSizes.MinimumUnboxedSize(type, pointerSize) > width
           && MetadataResolver.FindInstanceFieldPathAtOffset(type, 0, width) is { } path
           && TypeSizes.MinimumUnboxedSize(path.Field.FieldType, pointerSize) == width
            ? new FieldReference(path.Field, local, 0, path.Containers, width)
            : operand;

    private static FieldReference Clone(FieldReference projection)
        => new(projection.Field, projection.Local, projection.Offset, projection.Containers,
            projection.AccessSize);

    // An eight-byte lane holding two 32-bit fields is no one field, but each read of it takes
    // one: `SumArg(I4 v) => v.A + v.B + v.C + v.D` reads X1 as `w1` (`v.C`) and as
    // `lsr x9, x1, #32` (`v.D`). Any other read of the lane stays as it is.
    private static (FieldReference Low, FieldReference High)? SplitLane(TypeAnalysisContext aggregateType,
        LocalVariable local, BaseCallingConventionResolver.AggregateLane lane, int pointerSize)
    {
        if (lane.AccessSize != 8 || !IsPackedPair(aggregateType, lane.ByteOffset, pointerSize))
            return null;
        var (low, lowContainers) = HalfField(aggregateType, lane.ByteOffset, pointerSize)!.Value;
        var (high, highContainers) = HalfField(aggregateType, lane.ByteOffset + 4, pointerSize)!.Value;
        return (new FieldReference(low, local, lane.ByteOffset, lowContainers, 4),
            new FieldReference(high, local, lane.ByteOffset + 4, highContainers, 4));
    }

    private static bool ProjectSplitLanes(MethodAnalysisContext method,
        Dictionary<LocalVariable, (FieldReference Low, FieldReference High)> splitLanes)
    {
        if (splitLanes.Count == 0)
            return false;
        var definitions = SingleDefinitions(method);
        (FieldReference Low, FieldReference High)? LaneOf(IOperand operand)
            => Copied(operand, definitions) is LocalVariable local && splitLanes.TryGetValue(local, out var lane)
                ? lane
                : null;

        var changed = false;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction is { OpCode: OpCode.ShiftRight, Operands: [LocalVariable destination, var shifted, Immediate { Value: 32 }] }
                && instruction.NativeIntegerWidthBits != 32
                && LaneOf(shifted) is { } lane
                && (destination.Type == null || IsWordType(destination.Type, method)))
            {
                instruction.OpCode = OpCode.Move;
                instruction.SetOperands(destination, Clone(lane.High));
                destination.Type ??= lane.High.Field.FieldType;
                changed = true;
                continue;
            }

            for (var index = 1; index < instruction.Operands.Count; index++)
            {
                if (LaneOf(instruction.Operands[index]) is not { } split || !ReadsLowWord(instruction, index, method))
                    continue;
                instruction.SetOperand(index, Clone(split.Low));
                changed = true;
            }
        }
        return changed;
    }

    // Whether only the low 32 bits of the operand at `index` decide what the instruction does:
    // a W-register op, a 32-bit argument, or a 32-bit add, subtract, multiply or negate (no
    // 64-bit carry-propagating op has a meaning on two packed fields, so one typed as a 4-byte
    // integer is the W-register op the lift did not record the width of).
    private static bool ReadsLowWord(Instruction instruction, int index, MethodAnalysisContext method)
    {
        if (instruction.NativeIntegerWidthBits == 32)
            return instruction.OpCode is not (OpCode.Move or OpCode.Phi);
        switch (instruction.OpCode)
        {
            case OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Negate:
                return instruction.Destination is LocalVariable { Type: var resultType } && IsWordType(resultType, method);
            case OpCode.Call or OpCode.CallVoid when instruction.Operands[0] is MethodAnalysisContext callee:
                var parameter = index - (instruction.OpCode == OpCode.Call ? 2 : 1) - (callee.IsStatic ? 0 : 1);
                return parameter >= 0 && parameter < callee.Parameters.Count
                       && IsWordType(callee.Parameters[parameter].ParameterType, method);
            default:
                return false;
        }
    }

    // The lane's bytes are a field of the aggregate: a member at exactly the lane's
    // offset covering exactly the lane's width, nested when the layout nests it.
    // Anything wider, narrower or unaligned stays unprojected.
    private static FieldReference? LaneField(TypeAnalysisContext aggregateType, LocalVariable local,
        BaseCallingConventionResolver.AggregateLane lane, int pointerSize)
    {
        if (MetadataResolver.FindInstanceFieldPathAtOffset(aggregateType, lane.ByteOffset, lane.AccessSize)
                is not { } path
            || TypeSizes.MinimumUnboxedSize(path.Field.FieldType, pointerSize) != lane.AccessSize)
            return null;

        return new FieldReference(path.Field, local, lane.ByteOffset, path.Containers, lane.AccessSize);
    }

    private static bool NarrowWholeAggregateReads(MethodAnalysisContext method, int pointerSize)
    {
        var changed = false;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.NativeMemoryAccessSize is not { } width || width <= 0)
                continue;

            for (var operandIndex = 1; operandIndex < instruction.Operands.Count; operandIndex++)
            {
                if (instruction.Operands[operandIndex] is not LocalVariable { Type: { } type } local
                    || !type.IsValueType
                    || TypeSizes.MinimumUnboxedSize(type, pointerSize) <= width
                    || MetadataResolver.FindInstanceFieldPathAtOffset(type, 0, width) is not { } path
                    || TypeSizes.MinimumUnboxedSize(path.Field.FieldType, pointerSize) != width)
                    continue;

                instruction.SetOperand(operandIndex,
                    new FieldReference(path.Field, local, 0, path.Containers, width));
                changed = true;
            }
        }

        return changed;
    }
}
