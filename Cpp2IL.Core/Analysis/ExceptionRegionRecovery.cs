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
                foreach (var label in Targets(instruction))
                {
                    if (label is not CilInstructionLabel { Instruction: { } target } || !owner.TryGetValue(target, out var next)) return;
                    if (next != unit) unit.Next.Add(next);
                    else pendingInstructions.Push(unit.Code.FindIndex(i => ReferenceEquals(i, target)));
                }
                if (instruction.OpCode.FlowControl is not (CilFlowControl.Branch or CilFlowControl.Return or CilFlowControl.Throw))
                    pendingInstructions.Push(index + 1);
            }
            // The flat emitter can append an unreachable CFG bridge after a throw.
            // It is not an edge out of the throwing instruction's protected region.
            unit.Code = unit.Code.Where((_, index) => reachableInstructions.Contains(index)).ToList();
            foreach (var next in unit.Next) next.Previous.Add(unit);
        }
        var dominators = Dominators(units);
        var assigned = AssignedOnEntry(units, dominators);
        var nativeCalls = context.ExceptionRegionInstructions.Where(i => (i.IsCall || i.OpCode == OpCode.IndirectCall)
            && i.Operands[0] is not MethodAnalysisContext { UnderlyingPointer: 0 }).Select(i => i.NativeAddress).ToHashSet();
        bool NativeCall(Unit u) => u.Source is { } i && (i.IsCall || i.OpCode is OpCode.IndirectCall or OpCode.Throw)
            && (context.UnderlyingPointer == 0 || nativeCalls.Contains(i.NativeAddress));
        var regions = new List<Region>();
        // Effects with the same protected call sites belong to one finally body.
        // A genuinely nested cleanup also protects the inner cleanup call, so its
        // site set differs and it remains a separate enclosing region.
        var effects = proofs.SelectMany(p => p.CleanupCalls.Select(c => (Calls: c, Proof: p)))
            .GroupBy(p => string.Join(",", p.Calls.Order())).Select(g => new
            {
                Calls = g.First().Calls,
                Proofs = g.Select(p => p.Proof).Distinct().ToList(),
                Sites = g.SelectMany(p => p.Proof.Sites).Distinct().OrderBy(s => s.Start).ThenBy(s => s.End).ToList()
            }).ToList();
        var candidates = effects.GroupBy(e => string.Join(",", e.Sites.Select(s => $"{s.Start}:{s.End}:{s.LandingPad}")));
        foreach (var candidate in candidates)
        {
            var sites = candidate.First().Sites;
            var candidateProofs = candidate.SelectMany(e => e.Proofs).Distinct().ToList();
            var order = candidateProofs[0].CleanupCalls;
            var sequence = candidate.OrderBy(e => order.FindIndex(c => c.SequenceEqual(e.Calls))).ToList();
            if (sequence.Any(e => !order.Any(c => c.SequenceEqual(e.Calls)))
                || candidateProofs.Any(p => !p.CleanupCalls.Where(c => sequence.Any(e => c.SequenceEqual(e.Calls)))
                    .Select(c => string.Join(",", c)).SequenceEqual(sequence.Select(e => string.Join(",", e.Calls))))) continue;
            var copies = new List<List<Unit>>();
            foreach (var first in units.Where(u => u.Source != null && sequence[0].Calls.Contains(u.Source.NativeAddress)))
            {
                var copy = new List<Unit> { first };
                var current = first;
                var valid = true;
                foreach (var effect in sequence.Skip(1))
                {
                    do
                    {
                        if (current.Next.Count != 1) { valid = false; break; }
                        current = current.Next.Single();
                        if (copy.Contains(current) || current.Previous.Any(p => dominators.ContainsKey(p) && p != copy[^1])) { valid = false; break; }
                        copy.Add(current);
                        if (current.Source != null && effect.Calls.Contains(current.Source.NativeAddress)) break;
                        if (current.Source is not { OpCode: OpCode.Nop or OpCode.Jump }
                            && current.Source is not { OpCode: OpCode.Move, Destination: LocalVariable })
                        { valid = false; break; }
                    } while (true);
                    if (!valid) break;
                }
                if (valid) copies.Add(copy);
            }
            if (copies.Count == 0) continue;
            List<CilInstruction>? Handler(List<Unit> copy)
            {
                var result = new List<CilInstruction>();
                foreach (var unit in copy)
                {
                    if (unit.Source is not { } source || !instructionMap.TryGetValue(source, out var emitted)) return null;
                    if (source.OpCode is OpCode.Jump or OpCode.Nop) continue;
                    if (emitted.Any(i => i.OpCode.FlowControl is CilFlowControl.Branch or CilFlowControl.ConditionalBranch
                        or CilFlowControl.Return or CilFlowControl.Throw)) return null;
                    var calls = emitted.Where(i => i.OpCode.FlowControl == CilFlowControl.Call).ToList();
                    if (source.OpCode == OpCode.CallVoid)
                    {
                        if (calls.Count != 1 || source.Operands[0] is not MethodAnalysisContext callee
                            || calls[0].Operand is not IMethodDescriptor target
                            || target.FullName != callee.ToMethodDescriptor().FullName) return null;
                    }
                    else if (calls.Count != 0) return null;
                    result.AddRange(emitted);
                }
                return result;
            }
            var handler = Handler(copies[0]);
            if (handler is not { Count: > 0 } || copies.Any(c => Handler(c) is not { } other || !Equivalent(handler, other))) continue;
            var cleanups = copies.SelectMany(c => c).Distinct().ToList();
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
                // Different incoming branches may establish the same local. Require
                // assignment on every path, not one store dominating all paths.
                if (!HandlerLocalsAssigned(handler, assigned[entry])) continue;
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
                    || protectedUnits.Any(u => u != entry && u.Previous.Any(p => dominators.ContainsKey(p) && !protectedUnits.Contains(p)))
                    || protectedUnits.Any(u => NativeCall(u)
                        && !sites.Any(s => u.Source!.NativeAddress >= s.Start && u.Source.NativeAddress < s.End)))
                    continue;
                var exits = copies.Where(c => protectedUnits.Any(u => u.Next.Contains(c[0]))).SelectMany(c => c).Distinct().ToList();
                if (exits.Count == 0) continue;
                planned.Add(new Region(entry, protectedUnits, exits, handler, candidateProofs));
            }
            // A shared normal copy can be erased only when every way of reaching it
            // exits one of these finally clauses.
            if (planned.SelectMany(r => r.Cleanups).Distinct().Any(c => c.Previous.Any(previous => dominators.ContainsKey(previous)
                    && !planned.Any(r => r.Units.Contains(previous) || r.Cleanups.Contains(previous))))) continue;
            regions.AddRange(planned);
        }
        foreach (var (proof, handler) in catches ?? [])
        {
            Unit? merge;
            if (proof.Return is { } returned && instructionMap.TryGetValue(returned, out var continuation))
            {
                merge = new Unit(returned, continuation, units.Count);
                units.Add(merge);
            }
            else merge = units.FirstOrDefault(u => u.Source?.NativeAddress == proof.MergeAddress);
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
                // A normal SetResult/return can lie beyond the native try. Leave to
                // that existing unit without adding its call to the protected range.
                if (unit == merge || unit.Code.Any(i => i.OpCode.Code == CilCode.Ret)
                    || NativeCall(unit) && !proof.Sites.Any(s => unit.Source!.NativeAddress >= s.Start && unit.Source.NativeAddress < s.End)
                    || !protectedUnits.Add(unit)) continue;
                foreach (var next in unit.Next) pending.Push(next);
            }
            if (!seeds.All(protectedUnits.Contains)
                || protectedUnits.Any(u => u.Code.Any(i => i.OpCode.Code == CilCode.Ret))
                || protectedUnits.Any(u => u != entry && u.Previous.Any(p => dominators.ContainsKey(p) && !protectedUnits.Contains(p)))
                || protectedUnits.Any(u => NativeCall(u) && !proof.Sites.Any(s =>
                    u.Source!.NativeAddress >= s.Start && u.Source.NativeAddress < s.End)))
            {
                // Disjoint native ranges need not share one CLI try. Each emitted
                // unit is stack-balanced and has one legal entry; copying this
                // returning handler preserves the exceptional edge at every site.
                // ponytail: one clause per unit in this fallback; coalesce only if
                // clause count becomes a measured cost.
                if (seeds.Any(u => u == merge || u.Code.Any(i => i.OpCode.Code == CilCode.Ret))) continue;
                foreach (var seed in seeds)
                    regions.Add(new Region(seed, [seed], [], handler, []) { Catch = proof, Merge = merge });
                continue;
            }
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
                    pair.First != pair.Second && !pair.First!.Units.IsProperSubsetOf(pair.Second!.Units))) return;
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
        // Validate reachable entries before changing instructions. Dead incoming edges
        // are redirected to the same legal entry anchor below. A live branch can enter only at
        // the proven region entry, through an anchor immediately before its try start.
        foreach (var unit in units)
        foreach (var next in unit.Next)
            if (dominators.ContainsKey(unit) && membership[next].Except(membership[unit]).Any(r => next != r.Entry)) return;
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
                if (instruction.Operand is IList<ICilLabel> targets)
                {
                    var rewritten = new List<ICilLabel>();
                    var trampolines = new List<CilInstruction>();
                    foreach (var label in targets)
                    {
                        var targetInstruction = ((CilInstructionLabel)label).Instruction!;
                        var targetUnit = owner[targetInstruction];
                        var enteredRegions = membership[targetUnit].Except(membership[unit]).OrderByDescending(r => r.Units.Count).ToList();
                        var targetAddress = enteredRegions.Count > 0 ? enteredRegions[0].Anchor : targetInstruction;
                        if (membership[unit].Except(membership[targetUnit]).Any())
                        {
                            var leave = new CilInstruction(CilOpCodes.Leave, new CilInstructionLabel(targetAddress));
                            rewritten.Add(new CilInstructionLabel(leave));
                            trampolines.Add(leave);
                        }
                        else rewritten.Add(new CilInstructionLabel(targetAddress));
                    }
                    instruction.Operand = rewritten.ToArray();
                    if (trampolines.Count > 0)
                    {
                        var defaultPath = new CilInstruction(CilOpCodes.Nop);
                        replacements.Add(new CilInstruction(CilOpCodes.Br, new CilInstructionLabel(defaultPath)));
                        replacements.AddRange(trampolines);
                        replacements.Add(defaultPath);
                    }
                    continue;
                }
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

    private static IEnumerable<ICilLabel> Targets(CilInstruction instruction) => instruction.Operand switch
    {
        ICilLabel label => [label],
        IList<ICilLabel> labels => labels,
        _ => []
    };

    private static Dictionary<Unit, HashSet<CilLocalVariable>> AssignedOnEntry(List<Unit> units,
        Dictionary<Unit, HashSet<Unit>> dominators)
    {
        var reachable = dominators.Keys.ToList();
        var stores = reachable.ToDictionary(u => u, u => u.Code.Where(i => i.OpCode.Code is CilCode.Stloc or CilCode.Stloc_S)
            .Select(i => i.Operand).OfType<CilLocalVariable>().Where(local => WrittenOnEveryExit(u, local))
            .ToHashSet<CilLocalVariable>(ReferenceEqualityComparer.Instance));
        var all = stores.Values.SelectMany(s => s).ToHashSet<CilLocalVariable>(ReferenceEqualityComparer.Instance);
        var before = reachable.ToDictionary(u => u, u => u == units[0]
            ? new HashSet<CilLocalVariable>(ReferenceEqualityComparer.Instance) : new(all, ReferenceEqualityComparer.Instance));
        var after = reachable.ToDictionary(u => u, u => new HashSet<CilLocalVariable>(before[u].Concat(stores[u]), ReferenceEqualityComparer.Instance));
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var unit in reachable)
            {
                var parents = unit.Previous.Where(dominators.ContainsKey).ToList();
                var assigned = unit == units[0] || parents.Count == 0
                    ? new HashSet<CilLocalVariable>(ReferenceEqualityComparer.Instance) : new(after[parents[0]], ReferenceEqualityComparer.Instance);
                foreach (var parent in parents.Skip(1)) assigned.IntersectWith(after[parent]);
                before[unit] = assigned;
                var output = new HashSet<CilLocalVariable>(assigned, ReferenceEqualityComparer.Instance);
                output.UnionWith(stores[unit]);
                if (!after[unit].SetEquals(output)) { after[unit] = output; changed = true; }
            }
        }
        return before;

        static bool WrittenOnEveryExit(Unit unit, CilLocalVariable local)
        {
            var pending = new Stack<int>();
            var seen = new HashSet<int>();
            pending.Push(0);
            while (pending.TryPop(out var index))
            {
                if (index == unit.Code.Count) { if (unit.Fallthrough != null) return false; continue; }
                if (!seen.Add(index)) continue;
                var instruction = unit.Code[index];
                if (instruction.OpCode.Code is CilCode.Stloc or CilCode.Stloc_S && ReferenceEquals(instruction.Operand, local)) continue;
                foreach (var label in Targets(instruction))
                {
                    if (label is not CilInstructionLabel { Instruction: { } target }) return false;
                    var next = unit.Code.FindIndex(i => ReferenceEquals(i, target));
                    if (next < 0) return false;
                    pending.Push(next);
                }
                if (instruction.OpCode.FlowControl is not (CilFlowControl.Branch or CilFlowControl.Return or CilFlowControl.Throw))
                    pending.Push(index + 1);
            }
            return true;
        }
    }

    private static bool HandlerLocalsAssigned(List<CilInstruction> handler, HashSet<CilLocalVariable> entry)
    {
        var assigned = new HashSet<CilLocalVariable>(entry, ReferenceEqualityComparer.Instance);
        foreach (var instruction in handler)
        {
            if (instruction.Operand is not CilLocalVariable local) continue;
            if (instruction.OpCode.Code is CilCode.Stloc or CilCode.Stloc_S) assigned.Add(local);
            else if (instruction.OpCode.Code is CilCode.Ldloc or CilCode.Ldloc_S or CilCode.Ldloca or CilCode.Ldloca_S
                && !assigned.Contains(local)) return false;
        }
        return true;
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
