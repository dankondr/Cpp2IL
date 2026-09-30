using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Splits landing-pad handler code out of a method's instruction stream using the binary's
/// unwind tables. The unwinder's entry points are the pads of <c>.gcc_except_table</c>; code
/// reachable only from a pad is handler code and must never be lifted as a continuation of
/// the normal path, where registers the unwinder defines (<c>X0</c> = the exception object)
/// would read as undefined and the runtime calls (<c>__cxa_begin_catch</c>,
/// <c>_Unwind_Resume</c>, the rethrow and closure helpers) would read as calls.
///
/// Runs between ISIL conversion and control-flow-graph construction: handler instructions
/// are moved to <see cref="MethodAnalysisContext.LandingPadRegions"/> so the graph sees the
/// normal path alone. Every pad leaves one diagnostic naming its address until its region
/// shape is proven and emitted as a real try clause.
/// </summary>
public static class EhRegionPartition
{
    public static void Partition(MethodAnalysisContext context)
    {
        var isil = context.ConvertedIsil;
        if (isil is null or { Count: 0 })
            return;

        if (context.UnwindInfo == null
            && context.AppContext.Binary.EhFunctions?.TryGetValue(context.UnderlyingPointer, out var info) == true)
            context.UnwindInfo = info;
        var unwind = context.UnwindInfo;
        if (unwind is null || unwind.CallSites.Count == 0)
            return;

        context.ExceptionRegionInstructions = NativeExceptionRegionProof.Snapshot(isil);

        var callSitesByPad = new SortedDictionary<ulong, List<EhCallSiteInfo>>();
        foreach (var site in unwind.CallSites)
        {
            if (!callSitesByPad.TryGetValue(site.LandingPad, out var list))
                callSitesByPad[site.LandingPad] = list = [];
            list.Add(site);
        }

        // A pad's entry is the first instruction lifted from the machine instruction at its
        // address; the rest of that instruction's ISIL follows it by fallthrough.
        var padEntriesInStreamOrder = new List<(ulong Pad, int Entry)>();
        var seenEntries = new HashSet<ulong>();
        for (var i = 0; i < isil.Count; i++)
        {
            var address = isil[i].NativeAddress;
            if (address != 0 && callSitesByPad.ContainsKey(address) && seenEntries.Add(address))
                padEntriesInStreamOrder.Add((address, i));
        }
        var padsWithEntries = new HashSet<ulong>(padEntriesInStreamOrder.Select(p => p.Pad));
        var padEntries = new HashSet<int>(padEntriesInStreamOrder.Select(p => p.Entry));

        // What the normal path reaches, never *falling through* into a pad. Explicit jump
        // targets stay reachable even when they land on a pad address - a machine branch to
        // such an address is normal control flow the compiler shares with the pad, not the
        // unwinder's continuation.
        var normalReachable = new bool[isil.Count];
        Walk(isil, padEntries, [0], i => !normalReachable[i] && (normalReachable[i] = true));

        // Each pad then claims what it alone can reach. A shared tail belongs to the first
        // pad that reaches it; anything a pad reaches that the normal path also reaches is
        // normal code and stays.
        var owner = new int[isil.Count];
        for (var i = 0; i < owner.Length; i++)
            owner[i] = -1;
        foreach (var (pad, entry) in padEntriesInStreamOrder)
        {
            var regionIndex = context.LandingPadRegions.Count;
            Walk(isil, null, [entry], i => owner[i] < 0 && (owner[i] = regionIndex) >= 0);

            var region = new LandingPadRegion { PadAddress = pad };
            region.CallSites.AddRange(callSitesByPad[pad]);
            context.LandingPadRegions.Add(region);
        }

        // Pads whose entry instruction is not in this stream still get a region (their
        // handler content is simply unknown) so the diagnostic count matches the table.
        foreach (var (pad, sites) in callSitesByPad)
        {
            if (padsWithEntries.Contains(pad))
                continue;
            var region = new LandingPadRegion { PadAddress = pad };
            region.CallSites.AddRange(sites);
            context.LandingPadRegions.Add(region);
        }

        var kept = new List<Instruction>(isil.Count);
        for (var i = 0; i < isil.Count; i++)
        {
            if (owner[i] >= 0 && !normalReachable[i])
            {
                context.LandingPadRegions[owner[i]].Instructions.Add(isil[i]);
            }
            else
            {
                isil[i].Index = kept.Count;
                kept.Add(isil[i]);
            }
        }

        if (kept.Count != isil.Count)
        {
            isil.Clear();
            isil.AddRange(kept);
        }

        foreach (var region in context.LandingPadRegions)
            context.AddWarning($"Exception landing pad at 0x{region.PadAddress:X} has no proven region shape; its handler code is dropped");
    }

    /// <summary>
    /// Breadth-first walk over the flat instruction stream with the same successor relation
    /// <see cref="Cpp2IL.Core.Graphs.ISILControlFlowGraph"/> builds: a call, throw or any
    /// ordinary instruction continues to the next instruction; a conditional jump continues
    /// and targets; a (in)direct jump targets only; a return ends.
    /// </summary>
    private static void Walk(List<Instruction> isil, HashSet<int>? fallthroughBarrier, IEnumerable<int> seeds, Func<int, bool> tryMark)
    {
        var queue = new Queue<int>();
        foreach (var seed in seeds)
            if (TrySeed(seed))
                queue.Enqueue(seed);

        while (queue.Count > 0)
        {
            var i = queue.Dequeue();
            var instruction = isil[i];

            switch (instruction.OpCode)
            {
                case OpCode.Return:
                    break;
                case OpCode.Jump:
                case OpCode.IndirectJump:
                    EnqueueTarget(instruction);
                    break;
                case OpCode.ConditionalJump:
                    EnqueueNext(i);
                    EnqueueTarget(instruction);
                    break;
                default:
                    EnqueueNext(i);
                    break;
            }
        }

        return;

        bool TrySeed(int i) => i >= 0 && i < isil.Count && tryMark(i);

        void EnqueueNext(int i)
        {
            var next = i + 1;
            if (next < isil.Count && (fallthroughBarrier == null || !fallthroughBarrier.Contains(next)) && tryMark(next))
                queue.Enqueue(next);
        }

        void EnqueueTarget(Instruction instruction)
        {
            if (instruction.Operands.Count > 0
                && instruction.Operands[0] is Instruction target
                && target.Index >= 0
                && target.Index < isil.Count
                && ReferenceEquals(isil[target.Index], target)
                && tryMark(target.Index))
                queue.Enqueue(target.Index);
        }
    }
}
