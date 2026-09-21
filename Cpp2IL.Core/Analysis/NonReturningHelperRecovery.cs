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
        if (app.InstructionSet is not NewArmV8InstructionSet || app.Binary is not ElfFile elf)
            return [];
        var export = app.Binary.GetVirtualAddressOfExportedFunctionByName("il2cpp_raise_exception");
        if (export == 0)
            return [];
        uint? Read(ulong address)
        {
            var offset = app.Binary.MapVirtualAddressToRaw(address, false);
            if (offset < 0 || offset > app.Binary.RawLength - 4)
                return null;
            return BinaryPrimitives.ReadUInt32LittleEndian(app.Binary.GetRawBinaryContent().Slice((int)offset, 4));
        }
        var raise = MatchRaiseExport(export, elf.GetExportedFunctionSize("il2cpp_raise_exception"), Read);
        if (raise == 0)
            return [];
        return Select(method.ControlFlowGraph!, target =>
            !app.MethodsByAddress.ContainsKey(target)
            && app.ProvenNonReturningHelpers.GetOrAdd(target, address => ProvesNoReturn(address, raise, Read))
            && ThrowHelperRecovery.GetThrownException(app, target) != null);
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

    private static ulong BranchTarget(ulong pc, uint word)
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
