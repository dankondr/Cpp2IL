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
                    continue;
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
                    continue;
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
        changed |= ProjectScalarReturns(method, resolver, pointerSize);
        changed |= DropLaneStoresOfWholeStores(method, resolver, pointerSize);

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
        if (lanes.Count == 0)
            return false;

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
                    { (lane0, 0, lanes[0].ByteOffset) };
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
                if (lane0 is LocalVariable { Type: { } wholeType } whole
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

                var fields = new List<(FieldAnalysisContext Field, int Offset,
                    IReadOnlyList<FieldAnalysisContext> Containers, int Width)>();
                foreach (var (_, offset, width) in sources)
                {
                    if (MetadataResolver.FindInstanceFieldPathAtOffset(method.ReturnType, offset, width)
                            is not { } path
                        || TypeSizes.MinimumUnboxedSize(path.Field.FieldType, pointerSize) != width)
                    {
                        proven = false;
                        break;
                    }
                    fields.Add((path.Field, offset, path.Containers, width));
                }
                if (!proven)
                    continue;

                var result = new LocalVariable($"aggregateResult_{instruction.Index}",
                    new Register(null, $"ARET_{instruction.Index}"), method.ReturnType);
                method.Locals.Add(result);

                for (var i = 0; i < sources.Count; i++)
                {
                    var (operand, offset, width) = sources[i];
                    var (field, _, containers, _) = fields[i];
                    block.Instructions.Insert(index + i, new Instruction(instruction.Index, OpCode.Move,
                        new FieldReference(field, result, offset, containers, width),
                        LaneValue(operand, width, pointerSize))
                    {
                        NativeMemoryAccessSize = width
                    });
                }

                instruction.SetOperands(result);
                index += sources.Count;
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
                    && laneValue.Register is { Version: > 0 } laneRegister && laneRegister.Name == lane.Register.Name
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
