using System;
using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;

namespace Cpp2IL.Core.Analysis;

internal static class ExceptionRegionRecovery
{
    private sealed class Unit(Instruction? source, List<CilInstruction> code, int order)
    {
        internal readonly Instruction? Source = source;
        internal List<CilInstruction> Code = code;
        internal readonly int Order = order;
        internal readonly HashSet<Unit> Next = [];
        internal readonly HashSet<Unit> Previous = [];
        internal Unit? Fallthrough;
    }

    private sealed class Region(Unit entry, HashSet<Unit> units, List<Unit> cleanups,
        List<CilInstruction> handler, List<NativeExceptionRegionProof.Result> proofs)
    {
        internal readonly Unit Entry = entry;
        internal readonly HashSet<Unit> Units = units;
        internal readonly List<Unit> Cleanups = cleanups;
        internal readonly List<CilInstruction> Handler = handler;
        internal readonly List<NativeExceptionRegionProof.Result> Proofs = proofs;
        internal readonly CilInstruction Anchor = new(CilOpCodes.Nop);
        internal readonly CilInstruction Start = new(CilOpCodes.Nop);
        internal readonly CilInstruction End = new(CilOpCodes.Nop);
        internal Region? Parent;
        internal NativeExceptionRegionProof.CatchResult? Catch;
        internal Unit? Merge;
    }

    internal static void Apply(MethodAnalysisContext context, MethodDefinition definition,
        Dictionary<Instruction, List<CilInstruction>> instructionMap,
        Dictionary<NativeExceptionRegionProof.CatchResult, List<CilInstruction>>? catches = null)
    {
        if (context.ExceptionRegionInstructions == null || context.LandingPadRegions.Count == 0)
            return;
        var proofs = new NativeExceptionRegionProof(context).Find();
        if (proofs.Count == 0 && catches is not { Count: > 0 } || definition.CilMethodBody!.ExceptionHandlers.Count != 0)
            return;
        var body = definition.CilMethodBody;
        var original = body.Instructions.ToList();
        var originals = new HashSet<CilInstruction>(original, ReferenceEqualityComparer.Instance);
        var starts = instructionMap.Where(p => p.Value.Count > 0 && originals.Contains(p.Value[0]))
            .ToDictionary(p => p.Value[0], p => p.Key, (IEqualityComparer<CilInstruction>)ReferenceEqualityComparer.Instance);
        var units = new List<Unit>();
        foreach (var instruction in original)
        {
            if (units.Count == 0 || starts.ContainsKey(instruction))
                units.Add(new Unit(starts.GetValueOrDefault(instruction), [], units.Count));
            units[^1].Code.Add(instruction);
        }
        if (units.Count == 0) return;
        var owner = units.SelectMany(u => u.Code.Select(i => (i, u))).ToDictionary(p => p.i, p => p.u, (IEqualityComparer<CilInstruction>)ReferenceEqualityComparer.Instance);
        for (var n = 0; n < units.Count; n++)
        {
            var unit = units[n];
            var pendingInstructions = new Stack<int>();
            var reachableInstructions = new HashSet<int>();
            pendingInstructions.Push(0);
            while (pendingInstructions.TryPop(out var index))
            {
                if (index == unit.Code.Count)
                {
                    if (n + 1 < units.Count)
                    {
                        unit.Fallthrough = units[n + 1];
                        unit.Next.Add(unit.Fallthrough);
                    }
                    continue;
                }
                if (!reachableInstructions.Add(index)) continue;
                var instruction = unit.Code[index];
                if (instruction.Operand is CilInstructionLabel { Instruction: { } target }
                    && owner.TryGetValue(target, out var next))
                {
                    if (next != unit) unit.Next.Add(next);
                    else pendingInstructions.Push(unit.Code.FindIndex(i => ReferenceEquals(i, target)));
                }
                else if (instruction.Operand is IList<ICilLabel>)
                    return; // switch-edge rewriting is not proven here yet
                if (instruction.OpCode.FlowControl is not (CilFlowControl.Branch or CilFlowControl.Return or CilFlowControl.Throw))
                    pendingInstructions.Push(index + 1);
            }
            // The flat emitter can append an unreachable CFG bridge after a throw.
            // It is not an edge out of the throwing instruction's protected region.
            unit.Code = unit.Code.Where((_, index) => reachableInstructions.Contains(index)).ToList();
            foreach (var next in unit.Next) next.Previous.Add(unit);
        }
        var dominators = Dominators(units);
        var nativeCalls = context.ExceptionRegionInstructions.Where(i => (i.IsCall || i.OpCode == OpCode.IndirectCall)
            && i.Operands[0] is not MethodAnalysisContext { UnderlyingPointer: 0 }).Select(i => i.NativeAddress).ToHashSet();
        bool NativeCall(Unit u) => u.Source is { } i && (i.IsCall || i.OpCode is OpCode.IndirectCall or OpCode.Throw)
            && (context.UnderlyingPointer == 0 || nativeCalls.Contains(i.NativeAddress));
        var regions = new List<Region>();
        var candidates = proofs.SelectMany(p => p.CleanupCalls.Select(c => (Calls: c, Proof: p)))
            .GroupBy(p => string.Join(",", p.Calls.Order())).ToList();
        foreach (var candidate in candidates)
        {
            var sites = candidate.SelectMany(p => p.Proof.Sites).Distinct().ToList();
            var cleanups = units.Where(u => u.Source != null && candidate.First().Calls.Contains(u.Source.NativeAddress)).ToList();
            if (cleanups.Count == 0
                || cleanups.Any(u => u.Source!.OpCode != OpCode.CallVoid || !instructionMap.ContainsKey(u.Source)))
                continue;
            var handler = instructionMap[cleanups[0].Source!];
            if (handler.Count == 0 || handler.Count(i => i.OpCode.FlowControl == CilFlowControl.Call) != 1
                || handler.Any(i => i.OpCode.FlowControl is CilFlowControl.Branch or CilFlowControl.ConditionalBranch
                    or CilFlowControl.Return or CilFlowControl.Throw)
                || cleanups.Any(u => !Equivalent(handler, instructionMap[u.Source!])
                    || u.Source!.Operands[0] is not MethodAnalysisContext callee
                    || instructionMap[u.Source].Single(i => i.OpCode.FlowControl == CilFlowControl.Call).Operand
                        is not IMethodDescriptor emittedCallee
                    || emittedCallee.FullName != callee.ToMethodDescriptor().FullName))
                continue;
            var allSeeds = units.Where(u => u.Source != null && dominators.ContainsKey(u) && sites.Any(s =>
                u.Source.NativeAddress >= s.Start && u.Source.NativeAddress < s.End)).ToList();
            if (allSeeds.Count == 0) continue;
            bool ProtectedCall(Unit u) => u.Source is { } i && (i.IsCall || i.OpCode is OpCode.IndirectCall or OpCode.Throw)
                && sites.Any(s => i.NativeAddress >= s.Start && i.NativeAddress < s.End);
            var seedGroups = allSeeds.GroupBy(seed => dominators[seed]
                .Where(u => NativeCall(u) && !ProtectedCall(u) && !cleanups.Contains(u))
                .OrderByDescending(u => dominators[u].Count).FirstOrDefault()).ToList();
            var planned = new List<Region>();
            foreach (var seeds in seedGroups)
            {
                var common = new HashSet<Unit>(dominators[seeds.First()]);
                foreach (var seed in seeds.Skip(1)) common.IntersectWith(dominators[seed]);
                var entry = common.OrderByDescending(u => dominators[u].Count).FirstOrDefault();
                if (entry == null || cleanups.Contains(entry)) continue;
                // The lifted normal copy can name a temporary introduced just before cleanup.
                // Such a temporary does not exist on an exceptional exit. Only established
                // storage (defined before try entry) is safe to load from the finally body.
                var handlerLocals = handler.Where(i => i.OpCode.Code is CilCode.Ldloc or CilCode.Ldloc_S
                        or CilCode.Ldloca or CilCode.Ldloca_S).Select(i => i.Operand).OfType<CilLocalVariable>();
                if (handlerLocals.Any(local => !dominators[entry].Any(u => u != entry && u.Code.Any(i =>
                        i.OpCode.Code is CilCode.Stloc or CilCode.Stloc_S && ReferenceEquals(i.Operand, local)))))
                    continue;
                var protectedUnits = new HashSet<Unit>();
                var pending = new Stack<Unit>();
                pending.Push(entry);
                while (pending.TryPop(out var unit))
                {
                    if (cleanups.Contains(unit) || !protectedUnits.Add(unit)) continue;
                    foreach (var next in unit.Next) pending.Push(next);
                }
                if (!seeds.All(protectedUnits.Contains)
                    || protectedUnits.Any(u => u.Code.Any(i => i.OpCode.Code == CilCode.Ret))
                    || protectedUnits.Any(u => u != entry && u.Previous.Any(p => !protectedUnits.Contains(p)))
                    || protectedUnits.Any(u => NativeCall(u)
                        && !sites.Any(s => u.Source!.NativeAddress >= s.Start && u.Source.NativeAddress < s.End)))
                    continue;
                var exits = cleanups.Where(c => protectedUnits.Any(u => u.Next.Contains(c))).ToList();
                if (exits.Count == 0) continue;
                planned.Add(new Region(entry, protectedUnits, exits, handler, candidate.Select(p => p.Proof).Distinct().ToList()));
            }
            // A shared normal copy can be erased only when every way of reaching it
            // exits one of these finally clauses.
            if (planned.SelectMany(r => r.Cleanups).Distinct().Any(c => c.Previous.Any(previous =>
                    !planned.Any(r => r.Units.Contains(previous))))) continue;
            regions.AddRange(planned);
        }
        foreach (var (proof, handler) in catches ?? [])
        {
            var merge = units.FirstOrDefault(u => u.Source?.NativeAddress == proof.MergeAddress);
            var seeds = units.Where(u => u.Source != null && dominators.ContainsKey(u) && proof.Sites.Any(s =>
                u.Source.NativeAddress >= s.Start && u.Source.NativeAddress < s.End)).ToList();
            if (merge == null || seeds.Count == 0 || handler.Count == 0) continue;
            var common = new HashSet<Unit>(dominators[seeds[0]]);
            foreach (var seed in seeds.Skip(1)) common.IntersectWith(dominators[seed]);
            var entry = common.OrderByDescending(u => dominators[u].Count).FirstOrDefault();
            if (entry == null || entry == merge) continue;
            var protectedUnits = new HashSet<Unit>();
            var pending = new Stack<Unit>();
            pending.Push(entry);
            while (pending.TryPop(out var unit))
            {
                if (unit == merge || !protectedUnits.Add(unit)) continue;
                foreach (var next in unit.Next) pending.Push(next);
            }
            if (!seeds.All(protectedUnits.Contains)
                || protectedUnits.Any(u => u.Code.Any(i => i.OpCode.Code == CilCode.Ret))
                || protectedUnits.Any(u => u != entry && u.Previous.Any(p => !protectedUnits.Contains(p)))
                || protectedUnits.Any(u => NativeCall(u) && !proof.Sites.Any(s =>
                    u.Source!.NativeAddress >= s.Start && u.Source.NativeAddress < s.End))) continue;
            regions.Add(new Region(entry, protectedUnits, [], handler, []) { Catch = proof, Merge = merge });
        }
        if (regions.Count == 0) return;
        // Only properly nested/disjoint sets can become legal CLI regions.
        if (regions.Any(a => regions.Any(b => a != b && a.Units.Overlaps(b.Units)
                && !a.Units.IsProperSubsetOf(b.Units) && !b.Units.IsProperSubsetOf(a.Units))))
            return;
        foreach (var proof in proofs.Where(p => p.CleanupCalls.Count > 1))
        foreach (var seed in units.Where(u => u.Source != null && proof.Sites.Any(s =>
                     u.Source.NativeAddress >= s.Start && u.Source.NativeAddress < s.End)))
        {
            var sequence = proof.CleanupCalls.Select(c => regions.FirstOrDefault(r => r.Units.Contains(seed)
                && r.Cleanups.Any(u => c.Contains(u.Source!.NativeAddress)))).ToList();
            if (sequence.All(r => r != null) && sequence.Zip(sequence.Skip(1)).Any(pair =>
                    !pair.First!.Units.IsProperSubsetOf(pair.Second!.Units))) return;
        }
        foreach (var region in regions)
            region.Parent = regions.Where(r => region.Units.IsProperSubsetOf(r.Units))
                .OrderBy(r => r.Units.Count).FirstOrDefault();
        var membership = units.ToDictionary(u => u, u => regions.Where(r => r.Units.Contains(u))
            .OrderBy(r => r.Units.Count).ToList());
        // A catch can leave only to its parent scope; joining another try requires
        // a separate entry proof, which this straight-line catch recognizer lacks.
        if (regions.Any(r => r.Catch != null && !membership[r.Merge!].SequenceEqual(
                membership[r.Entry].Where(parent => parent != r)))) return;
        // Validate all entries before changing instructions. A branch can enter only at
        // the proven region entry, through an anchor immediately before its try start.
        foreach (var unit in units)
        foreach (var next in unit.Next)
            if (membership[next].Except(membership[unit]).Any(r => next != r.Entry)) return;
        foreach (var unit in units)
        foreach (var instruction in unit.Code)
            if (instruction.Operand is CilInstructionLabel { Instruction: { } target }
                && owner.TryGetValue(target, out var next) && membership[unit].Except(membership[next]).Any()
                && instruction.OpCode.FlowControl != CilFlowControl.Branch
                && instruction.OpCode.Code is not (CilCode.Brtrue or CilCode.Brtrue_S or CilCode.Brfalse or CilCode.Brfalse_S))
                return;

        var output = new List<CilInstruction>();
        var clauses = new List<CilExceptionHandler>();
        var removed = new HashSet<CilInstruction>(ReferenceEqualityComparer.Instance);
        foreach (var region in regions)
        foreach (var cleanup in region.Cleanups)
        {
            var emitted = instructionMap[cleanup.Source!];
            foreach (var instruction in emitted.Skip(1)) removed.Add(instruction);
        }
        // Preserve each original fall-through edge explicitly before moving any block.
        // The generated ISIL instructions are stack-balanced at these boundaries.
        foreach (var unit in units)
            if (unit.Fallthrough != null)
                unit.Code.Add(new CilInstruction(CilOpCodes.Br, new CilInstructionLabel(unit.Fallthrough.Code[0])));

        foreach (var unit in units)
        {
            var replacements = new List<CilInstruction>();
            foreach (var instruction in unit.Code)
            {
                if (removed.Contains(instruction)) continue;
                replacements.Add(instruction);
                if (instruction.Operand is not CilInstructionLabel { Instruction: { } target }
                    || !owner.TryGetValue(target, out var next) || next == unit) continue;
                var entered = membership[next].Except(membership[unit]).OrderByDescending(r => r.Units.Count).ToList();
                var exited = membership[unit].Except(membership[next]).Any();
                var destination = entered.Count > 0 ? entered[0].Anchor : target;
                if (!exited)
                {
                    instruction.Operand = new CilInstructionLabel(destination);
                    continue;
                }
                if (instruction.OpCode.FlowControl == CilFlowControl.Branch)
                {
                    instruction.OpCode = CilOpCodes.Leave;
                    instruction.Operand = new CilInstructionLabel(destination);
                }
                else if (instruction.OpCode.Code is CilCode.Brtrue or CilCode.Brtrue_S or CilCode.Brfalse or CilCode.Brfalse_S)
                {
                    var skip = new CilInstruction(CilOpCodes.Nop);
                    instruction.OpCode = instruction.OpCode.Code is CilCode.Brtrue or CilCode.Brtrue_S ? CilOpCodes.Brfalse : CilOpCodes.Brtrue;
                    instruction.Operand = new CilInstructionLabel(skip);
                    replacements.Add(new CilInstruction(CilOpCodes.Leave, new CilInstructionLabel(destination)));
                    replacements.Add(skip);
                }

            }
            unit.Code.Clear();
            unit.Code.AddRange(replacements);
        }
        // Clone the cleanup before erasing its normal-path copy.
        var handlers = regions.ToDictionary(r => r, r => r.Handler.Select(i => new CilInstruction(i.OpCode, i.Operand)).ToList());
        foreach (var cleanup in regions.SelectMany(r => r.Cleanups).Distinct())
        {
            var first = instructionMap[cleanup.Source!][0];
            first.OpCode = CilOpCodes.Nop;
            first.Operand = null;
        }
        EmitLevel(null, units);
        body.Instructions.Clear();
        foreach (var instruction in output) body.Instructions.Add(instruction);
        foreach (var clause in clauses) body.ExceptionHandlers.Add(clause);
        foreach (var pad in proofs.Where(p => p.CleanupCalls.All(c => regions.Any(r => r.Proofs.Contains(p)
                         && r.Cleanups.Any(u => c.Contains(u.Source!.NativeAddress))))
                     && units.Where(u => u.Source != null && dominators.ContainsKey(u) && p.Sites.Any(s =>
                         u.Source.NativeAddress >= s.Start && u.Source.NativeAddress < s.End))
                         .All(u => regions.Any(r => r.Proofs.Contains(p) && r.Units.Contains(u))))
                     .SelectMany(p => p.Pads).Concat(regions.Where(r => r.Catch != null).SelectMany(r => r.Catch!.Pads)).Distinct())
        {
            // One pad can serve several ranges. Proving one incoming range must not
            // hide another range whose throwing calls remain outside every clause.
            if (context.UnwindInfo!.CallSites.Where(s => s.LandingPad == pad).Any(s => units.Any(u =>
                    NativeCall(u) && dominators.ContainsKey(u) && u.Source!.NativeAddress >= s.Start
                    && u.Source.NativeAddress < s.End && !regions.Any(r => r.Units.Contains(u))))) continue;
            context.AnalysisWarnings.Remove($"Exception landing pad at 0x{pad:X} has no proven region shape; its handler code is dropped");
        }
        return;

        void EmitLevel(Region? parent, IEnumerable<Unit> members)
        {
            var children = regions.Where(r => r.Parent == parent).ToList();
            var emittedChildren = new HashSet<Region>();
            // Keep a real method terminator last. An unreachable EH end marker must
            // not trigger the flat emitter's synthetic fall-off return diagnostic.
            var lastReturn = parent == null ? units.LastOrDefault(u => membership[u].Count == 0
                && u.Code[^1].OpCode.FlowControl is CilFlowControl.Return or CilFlowControl.Throw) : null;
            foreach (var unit in members.OrderBy(u => parent?.Entry == u ? -1 : u == lastReturn ? int.MaxValue : u.Order))
            {
                var child = children.FirstOrDefault(r => r.Units.Contains(unit));
                if (child == null) { output.AddRange(unit.Code); continue; }
                if (!emittedChildren.Add(child)) continue;
                output.Add(child.Anchor);
                // The entry must physically follow the external anchor. Other blocks have
                // explicit branches, so their old physical order does not define execution.
                output.Add(child.Start);
                EmitLevel(child, child.Units);
                var handlerCode = handlers[child];
                var handlerStart = handlerCode[0];
                output.AddRange(handlerCode);
                output.Add(child.Catch == null ? new CilInstruction(CilOpCodes.Endfinally)
                    : new CilInstruction(CilOpCodes.Leave, new CilInstructionLabel(child.Merge!.Code[0])));
                output.Add(child.End);
                clauses.Add(new CilExceptionHandler
                {
                    HandlerType = child.Catch == null ? CilExceptionHandlerType.Finally : CilExceptionHandlerType.Exception,
                    ExceptionType = child.Catch?.Type.ToTypeSignature().ToTypeDefOrRef(),
                    TryStart = new CilInstructionLabel(child.Start),
                    TryEnd = new CilInstructionLabel(handlerStart),
                    HandlerStart = new CilInstructionLabel(handlerStart),
                    HandlerEnd = new CilInstructionLabel(child.End)
                });
            }
        }
    }

    private static bool Equivalent(List<CilInstruction> a, List<CilInstruction> b) => a.Count == b.Count
        && a.Zip(b).All(p => p.First.OpCode == p.Second.OpCode && (p.First.Operand is IMethodDescriptor aMethod && p.Second.Operand is IMethodDescriptor bMethod
                ? aMethod.FullName == bMethod.FullName : Equals(p.First.Operand, p.Second.Operand)));

    private static Dictionary<Unit, HashSet<Unit>> Dominators(List<Unit> units)
    {
        var reachable = new HashSet<Unit>();
        var pending = new Stack<Unit>();
        pending.Push(units[0]);
        while (pending.TryPop(out var unit))
            if (reachable.Add(unit)) foreach (var next in unit.Next) pending.Push(next);
        var result = reachable.ToDictionary(u => u, u => u == units[0] ? new HashSet<Unit> { u } : new HashSet<Unit>(reachable));
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var unit in reachable.Where(u => u != units[0]))
            {
                var parents = unit.Previous.Where(reachable.Contains).ToList();
                var common = parents.Count == 0 ? [] : new HashSet<Unit>(result[parents[0]]);
                foreach (var parent in parents.Skip(1)) common.IntersectWith(result[parent]);
                common.Add(unit);
                if (!result[unit].SetEquals(common)) { result[unit] = common; changed = true; }
            }
        }
        return result;
    }
}
