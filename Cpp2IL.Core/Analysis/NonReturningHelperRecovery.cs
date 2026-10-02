using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.Elf;

namespace Cpp2IL.Core.Analysis;

internal static class NonReturningHelperRecovery
{
    internal static HashSet<Block> Find(MethodAnalysisContext method)
    {
        var app = method.AppContext;
        return Select(method.ControlFlowGraph!, target => IsProven(app, target));
    }

    internal static bool IsProven(ApplicationAnalysisContext app, ulong target)
    {
        if (app.InstructionSet is not NewArmV8InstructionSet || app.Binary is not ElfFile elf
            || app.MethodsByAddress.ContainsKey(target))
            return false;
        var export = app.Binary.GetVirtualAddressOfExportedFunctionByName("il2cpp_raise_exception");
        if (export == 0)
            return false;
        uint? Read(ulong address)
        {
            var offset = app.Binary.MapVirtualAddressToRaw(address, false);
            return offset < 0 || offset > app.Binary.RawLength - 4 ? null
                : BinaryPrimitives.ReadUInt32LittleEndian(app.Binary.GetRawBinaryContent().Slice((int)offset, 4));
        }
        var raise = MatchRaiseExport(export, elf.GetExportedFunctionSize("il2cpp_raise_exception"), Read);
        return raise != 0
            && app.ProvenNonReturningHelpers.GetOrAdd(target, address => ProvesNoReturn(address, raise, Read))
            && ThrowHelperRecovery.GetThrownException(app, target) != null;
    }

    // The exported API is declared DO_API_NO_RETURN. Match its whole straight-line
    // wrapper, including the hidden MethodInfo argument, before trusting the callee.
    internal static ulong MatchRaiseExport(ulong address, ulong size, Func<ulong, uint?> read)
        => size == 12 && read(address) == 0xf81f0ffe && read(address + 4) == 0xaa1f03e1
            && read(address + 8) is uint call && (call & 0xfc000000) == 0x94000000
            ? BranchTarget(address + 8, call) : 0;

    internal static bool ProvesNoReturn(ulong address, ulong anchor, Func<ulong, uint?> read)
    {
        if (anchor == 0)
            return false;
        return Visit(address, 0, []);
        bool Visit(ulong start, int depth, HashSet<ulong> visiting)
        {
            if (start == anchor)
                return true;
            if (depth >= 5 || !visiting.Add(start))
                return false;
            try
            {
                for (var i = 0; i < 24; i++)
                {
                    var pc = start + (ulong)i * 4;
                    if (read(pc) is not uint word || word == 0)
                        return false;
                    if ((word & 0xfc000000) == 0x14000000)
                        return Visit(BranchTarget(pc, word), depth + 1, visiting);
                    if ((word & 0xfc000000) == 0x94000000)
                    {
                        if (Visit(BranchTarget(pc, word), depth + 1, visiting))
                            return true;
                        continue;
                    }
                    // Any conditional/indirect branch, return, or exception instruction
                    // needs a real multi-path proof; this bounded straight-line rule stops.
                    if ((word & 0xff000000) == 0x54000000
                        || (word & 0x7e000000) is 0x34000000 or 0x36000000
                        || (word & 0xfe000000) == 0xd6000000
                        || (word & 0xff000000) == 0xd4000000)
                        return false;
                }
                return false;
            }
            finally { visiting.Remove(start); }
        }
    }

    // A Throw ends control flow, but the lifted CFG keeps the native fall-through after the
    // noreturn call it came from. Through that impossible edge a throw block shared by many
    // checks feeds a join's phis whatever each register held on the way in - a method-init flag
    // page, a class-init flag - and the join reads them as values. Edges into joins go, with their
    // phi inputs. ponytail: a successor only the throw reaches keeps its dead edge - deleting that
    // code drops a catch-rethrow a raise inside a protected range natively falls into (UniTask's
    // WhenAnyLRPromise); cut it too once exception recovery stops relying on it.
    internal static void CutThrowFallThrough(ISILControlFlowGraph cfg)
    {
        foreach (var block in cfg.Blocks)
        {
            if (block == cfg.EntryBlock || !block.Instructions.Any(i => i.OpCode == OpCode.Throw))
                continue;

            var joins = block.Successors.Where(successor => successor != cfg.ExitBlock
                && successor.Predecessors.Any(predecessor => predecessor != block)).Distinct().ToList();
            if (joins.Count == 0)
                continue;

            foreach (var join in joins)
            {
                while (join.Predecessors.Contains(block))
                    cfg.RemovePredecessor(join, block);
                block.Successors.RemoveAll(successor => successor == join);
            }

            // A branch after the throw would name a block this one no longer reaches.
            foreach (var jump in block.Instructions.Where(i => i.OpCode is OpCode.Jump or OpCode.ConditionalJump
                         && i.Operands[0] is Block target && joins.Contains(target)))
            {
                jump.OpCode = OpCode.Nop;
                jump.SetOperands();
            }

            if (block.Successors.Count == 0)
            {
                block.Successors.Add(cfg.ExitBlock);
                cfg.ExitBlock.Predecessors.Add(block);
            }
            block.CalculateBlockType();
        }
    }

    internal static ulong BranchTarget(ulong pc, uint word)
        => unchecked((ulong)((long)pc + ((int)(word << 6) >> 4)));

    internal static HashSet<Block> Select(ISILControlFlowGraph graph, Func<ulong, bool> proven)
    {
        HashSet<Block> result = [];
        foreach (var block in graph.Blocks)
        {
            // Limit this recovery to the spurious return after a terminal helper.
            // Interior no-return calls need a separate multi-block recovery audit.
            if (block.Successors is not [{ Instructions: [{ OpCode: OpCode.Return }], Predecessors.Count: 1 }])
                continue;
            if (block.Instructions.LastOrDefault() is not { IsCall: true, Operands: [Immediate target, ..] }
                || !proven(target.UnsignedValue))
                continue;
            // Preserve the shared CFG for existing SSA/exception recovery. The native
            // stack analysis alone must not propagate SP along this impossible edge.
            result.Add(block);
        }
        return result;
    }
}
