using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Extensions;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Converts the control flow graph into and out of minimal SSA form, following the standard
/// Cytron et al. algorithm: phi functions are inserted at the iterated dominance frontiers of
/// each variable's definition sites, and the registers are then renamed (versioned) via a
/// pre-order walk of the dominator tree.
///
/// Variables are <see cref="Register"/>s, identified by <see cref="Register.Number"/>. Version
/// -1 represents the value on entry to the method (parameters / live-in values); real
/// definitions are numbered from 1 upwards.
/// </summary>
public class SsaForm
{
    // Per-register version stack (top = current version in the current dominator-tree path).
    private readonly Dictionary<int, Stack<Register>> _stacks = new();
    // Per-register last-assigned version number.
    private readonly Dictionary<int, int> _counter = new();
    // An unversioned representative register per number, used to build phi nodes and the entry value.
    private readonly Dictionary<int, Register> _repr = new();

    public static void Build(MethodAnalysisContext method)
        => Build(method.ControlFlowGraph!, method.DominatorInfo!);

    public static void Build(ISILControlFlowGraph graph, DominatorInfo dominatorInfo)
    {
        var ssa = new SsaForm();
        SinkHoistedAddressTakes(graph);
        ssa.FindClobberingAddressTakes(graph);

        graph.BuildUseDefLists(ssa._clobbering);

        ssa.CollectRegisters(graph);
        ssa.InsertPhiFunctions(graph, dominatorInfo);
        ssa.Rename(graph.EntryBlock, dominatorInfo);
    }

    // Compilers may calculate &slot before storing the value passed to a native byref call.
    // SSA must bind that address to the stored version, not the stale value that preceded it.
    private static void SinkHoistedAddressTakes(ISILControlFlowGraph graph)
    {
        foreach (var block in graph.Blocks)
        {
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                var addressTake = block.Instructions[i];
                if (addressTake is not { OpCode: OpCode.Move, Operands: [Register pointer, AddressOf { Target: Register slot }] })
                    continue;

                var lastSlotDefinition = -1;
                for (var j = i + 1; j < block.Instructions.Count; j++)
                {
                    var candidate = block.Instructions[j];
                    if (Reads(candidate, pointer)
                        || candidate.Destination is Register pointerDefinition && pointerDefinition.Number == pointer.Number)
                        break;

                    if (candidate.Destination is Register slotDefinition && slotDefinition.Number == slot.Number)
                        lastSlotDefinition = j;
                }

                if (lastSlotDefinition < 0)
                    continue;

                block.Instructions.RemoveAt(i);
                block.Instructions.Insert(lastSlotDefinition, addressTake);
                i = lastSlotDefinition;
            }
        }
    }

    // The address-takes whose slot is read again afterwards, and so have to be treated as definitions.
    private readonly HashSet<Instruction> _clobbering = [];

    private void FindClobberingAddressTakes(ISILControlFlowGraph graph)
    {
        foreach (var block in graph.Blocks)
        {
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                var instruction = block.Instructions[i];

                foreach (var operand in instruction.Operands)
                {
                    // Taking the slot's address only clobbers it if the published pointer can reach
                    // a write. One that stays inside the frame - the exception-handling record that
                    // just lets the landing pad reload the cell, for example - leaves the value alone.
                    if (operand is AddressOf { Target: Register addressed }
                        && IsReadAfter(block, i, addressed)
                        && PointerMayWrite(graph, instruction))
                        _clobbering.Add(instruction);
                }
            }
        }
    }

    // Whether the pointer published by an address-take can reach a write of the cell it
    // addresses. A carrier is a register or frame cell that may hold the pointer; a
    // forward reaching analysis propagates carriers over the control-flow graph - a
    // value-preserving write fed by a carrier makes the destination another carrier,
    // any other write kills it, so a register reassigned before the pointer is used is
    // no longer tracked.
    //
    // A carrier only proves a write when it escapes or is dereferenced for a store: a
    // call operand, a return/throw, the destination of a memory write, or another
    // address-take (&carrier is a pointer to the pointer, too indirect to keep
    // tracking). Copies, arithmetic and spills into other cells produce more carriers;
    // a load through a carrier only reads the cell. A carrier stored through an
    // explicitly sub-pointer width is truncated - it can never be reloaded as a
    // pointer, so a byte/half/word store only writes data.
    //
    // Cells are keyed uniformly: a frame cell's "stack_N"/"stack_-N" register (named by
    // StackAnalyzer's NameForSlot) and a raw stack[N] StackOffset operand in an
    // unreachable pad both hash to the same key. Blocks unreachable from entry -
    // exception landing pads, dispatched by the runtime out of band - are scanned
    // against every carrier seen anywhere, since a pad can be entered at any point
    // where the pointer is live.
    private static bool PointerMayWrite(ISILControlFlowGraph graph, Instruction take)
    {
        if (take.Destination is not Register produced)
            return true; // no register carries the pointer: assume it can be written through

        static int CellKey(int offset) =>
            (offset < 0 ? $"stack_-{-offset:X}" : $"stack_{offset:X}").GetHashCode();

        static int? CarrierKey(IOperand? operand) => operand switch
        {
            Register register => register.Number,
            StackOffset stackOffset => CellKey(stackOffset.Offset),
            _ => null,
        };

        var slotKey = take.Operands
            .OfType<AddressOf>()
            .Select(addressOf => CarrierKey(addressOf.Target))
            .FirstOrDefault(key => key.HasValue);

        // Destinations of other takes of the same cell hold an identical pointer - they
        // are carriers too (kept forever: being pointers is a fact, not a flow state).
        var born = new HashSet<int>();
        foreach (var instruction in graph.Blocks.SelectMany(block => block.Instructions))
        {
            if (!ReferenceEquals(instruction, take)
                && instruction.Operands.Any(o => o is AddressOf addressOf && CarrierKey(addressOf.Target) == slotKey)
                && CarrierKey(instruction.Destination) is { } destKey)
                born.Add(destKey);
        }

        // Scan one block's instructions against a live carrier set, returning true on
        // the first escape. `everSeen` accumulates the union of carriers live at any
        // scanned point, for seeding unreachable blocks afterwards.
        bool ScanBlock(Block block, HashSet<int> carriers, HashSet<int>? everSeen)
        {
            bool IsCarrier(IOperand? operand) =>
                CarrierKey(operand) is { } key && (carriers.Contains(key) || born.Contains(key));

            bool AddressesThroughCarrier(IOperand? operand) =>
                operand is MemoryOperand memory && (IsCarrier(memory.Base) || IsCarrier(memory.Index));

            foreach (var instruction in block.Instructions)
            {
                if (ReferenceEquals(instruction, take))
                    carriers.Add(produced.Number);
                else
                {
                    var readsCarrier = instruction.Sources.Any(IsCarrier);

                    // &carrier escapes into pointer-to-pointer territory this cannot follow;
                    // a store addressed through a carrier writes the cell outright.
                    if (instruction.Operands.Any(o =>
                            o is AddressOf { Target: { } target } && IsCarrier(target))
                        || AddressesThroughCarrier(instruction.Destination))
                        return true;

                    switch (instruction.OpCode)
                    {
                        // Value-preserving shapes make the destination another carrier.
                        case OpCode.Move or OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide
                            or OpCode.Modulo or OpCode.ShiftLeft or OpCode.ShiftRight or OpCode.And or OpCode.Or
                            or OpCode.Xor or OpCode.Not or OpCode.Negate or OpCode.SignExtend32
                            or OpCode.VectorMin or OpCode.VectorMax or OpCode.Phi:
                            // A carrier stored into raw memory escapes tracking - unless the
                            // store is provably narrower than a pointer: a truncated address
                            // can never be reloaded as a carrier, so a byte/half/word store
                            // only writes data.
                            if (readsCarrier
                                && instruction.Destination is not Register and not StackOffset
                                && instruction.Destination is not MemoryOperand { AccessSize: > 0 and < 8 })
                                return true;
                            break;
                        // Reads that cannot produce a pointer: comparisons, branches, padding.
                        case OpCode.CheckEqual or OpCode.CheckGreater or OpCode.CheckLess or OpCode.CheckNotEqual
                            or OpCode.CheckGreaterOrEqual or OpCode.CheckLessOrEqual
                            or OpCode.ConditionalJump or OpCode.Jump
                            or OpCode.Nop or OpCode.Invalid or OpCode.NotImplemented or OpCode.Interrupt:
                            break;
                        // Calls, returns, throws, allocations and block-memory ops hand the
                        // pointer to code the analysis cannot follow. Every operand position
                        // counts - some opcodes keep their escape positions out of `Sources`
                        // (Throw's value, a Call's destination register, Newobj's arguments).
                        default:
                            if (instruction.Operands.Any(o => IsCarrier(o) || AddressesThroughCarrier(o)))
                                return true;
                            break;
                    }

                    // A register or frame cell written from a carrier becomes one; any other
                    // write to it kills the carrier (a load through a carrier reads the
                    // cell's contents, so its bare-source check fails and it dies here too).
                    if (CarrierKey(instruction.Destination) is { } writtenKey)
                    {
                        if (readsCarrier)
                            carriers.Add(writtenKey);
                        else
                            carriers.Remove(writtenKey);
                    }
                }

                everSeen?.UnionWith(carriers);
            }

            return false;
        }

        var reachable = new HashSet<Block>();
        var queue = new Queue<Block>();
        queue.Enqueue(graph.EntryBlock);
        while (queue.Count > 0)
        {
            var current = queue.Dequeue();
            if (!reachable.Add(current))
                continue;
            foreach (var successor in current.Successors)
                queue.Enqueue(successor);
        }

        var outSets = graph.Blocks.ToDictionary(block => block, _ => new HashSet<int>());
        var everSeen = new HashSet<int>(born);
        var pending = new Queue<Block>(reachable);
        while (pending.Count > 0)
        {
            var block = pending.Dequeue();

            var carriers = new HashSet<int>();
            foreach (var predecessor in block.Predecessors)
                if (reachable.Contains(predecessor))
                    carriers.UnionWith(outSets[predecessor]);

            if (ScanBlock(block, carriers, everSeen))
                return true;

            if (!carriers.SetEquals(outSets[block]))
            {
                outSets[block] = carriers;
                foreach (var successor in block.Successors)
                    if (reachable.Contains(successor))
                        pending.Enqueue(successor);
            }
        }

        // Exception pads are unreachable in the graph but can run at any point where
        // the pointer is live; scan each under every carrier seen anywhere.
        foreach (var block in graph.Blocks)
        {
            if (!reachable.Contains(block)
                && ScanBlock(block, new HashSet<int>(everSeen), null))
                return true;
        }

        return false;
    }

    private static bool IsReadAfter(Block block, int index, Register register)
    {
        if (ScanForRead(block, index + 1, register, out var continuePastBlock))
            return true;

        if (!continuePastBlock)
            return false;

        var visited = new HashSet<Block>();
        var queue = new Queue<Block>(block.Successors);

        while (queue.Count > 0)
        {
            var reachable = queue.Dequeue();

            if (!visited.Add(reachable))
                continue;

            if (ScanForRead(reachable, 0, register, out var keepGoing))
                return true;

            if (!keepGoing)
                continue;

            foreach (var successor in reachable.Successors)
                queue.Enqueue(successor);
        }

        return false;
    }

    // Scans a block from an index. Reports whether the register is read, and whether the paths beyond
    // this block are still worth following (they aren't once something has reassigned it).
    private static bool ScanForRead(Block block, int from, Register register, out bool continuePastBlock)
    {
        continuePastBlock = true;

        for (var i = from; i < block.Instructions.Count; i++)
        {
            var instruction = block.Instructions[i];

            if (Reads(instruction, register))
                return true;

            if (instruction.Destination is Register defined && defined.Number == register.Number)
            {
                continuePastBlock = false;
                return false;
            }
        }

        return false;
    }

    // A plain read of the register's value. The address-takes themselves don't count.
    private static bool Reads(Instruction instruction, Register register)
    {
        for (var i = 0; i < instruction.Operands.Count; i++)
        {
            if (i == 0 && instruction.Destination is Register)
                continue;

            var reads = instruction.Operands[i] switch
            {
                Register other => other.Number == register.Number,
                MemoryOperand memory => (memory.Base as Register?)?.Number == register.Number
                    || (memory.Index as Register?)?.Number == register.Number,
                _ => false
            };

            if (reads)
                return true;
        }

        return false;
    }

    private void CollectRegisters(ISILControlFlowGraph graph)
    {
        foreach (var instruction in graph.Instructions)
            foreach (var register in EnumerateRegisters(instruction))
                if (!_repr.ContainsKey(register.Number))
                    _repr[register.Number] = register.Copy();
    }

    private static IEnumerable<Register> EnumerateRegisters(Instruction instruction)
    {
        if (instruction.ImplicitDefinition is { } clobbered)
            yield return clobbered;

        foreach (var operand in instruction.Operands)
        {
            if (operand is Register register)
                yield return register;
            else if (operand is AddressOf { Target: Register addressed })
                yield return addressed;
            else if (operand is MemoryOperand memory)
            {
                if (memory.Base is Register baseRegister)
                    yield return baseRegister;
                if (memory.Index is Register indexRegister)
                    yield return indexRegister;
            }
        }
    }

    private void InsertPhiFunctions(ISILControlFlowGraph graph, DominatorInfo dominance)
    {
        var defSites = GetDefinitionSites(graph);
        var liveIn = ComputeLiveIn(graph);

        foreach (var entry in defSites)
        {
            var regNumber = entry.Key;
            var sites = entry.Value;

            var workList = new Queue<Block>(sites);
            var onWorkList = new HashSet<Block>(sites);
            var hasPhi = new HashSet<Block>();

            while (workList.Count > 0)
            {
                var block = workList.Dequeue();

                if (!dominance.DominanceFrontier.TryGetValue(block, out var frontier))
                    continue;

                foreach (var frontierBlock in frontier)
                {
                    // Pruned SSA: a phi is only worth materializing where the
                    // register is live-in - a join no path can read would emit
                    // dead edge copies (often between differently-typed reuse
                    // versions of the same register).
                    if (!liveIn[frontierBlock].Contains(regNumber))
                        continue;

                    // Only one phi per (block, register).
                    if (!hasPhi.Add(frontierBlock))
                        continue;

                    InsertPhiSkeleton(frontierBlock, regNumber);

                    // Inserting a phi is itself a definition, so propagate to its frontier too.
                    if (onWorkList.Add(frontierBlock))
                        workList.Enqueue(frontierBlock);
                }
            }
        }
    }

    // Unversioned register liveness for phi pruning: a register is live-in at a
    // block when some path from it reaches a read before any re-definition.
    // Upward-exposed uses count bare registers, memory base/index registers and
    // non-clobbering address-take targets (the take binds the live cell);
    // definitions count assignments, implicit clobbers and clobbering takes.
    private Dictionary<Block, HashSet<int>> ComputeLiveIn(ISILControlFlowGraph graph)
    {
        var upwardExposedUse = new Dictionary<Block, HashSet<int>>();
        var defs = new Dictionary<Block, HashSet<int>>();

        foreach (var block in graph.Blocks)
        {
            var use = new HashSet<int>();
            var def = new HashSet<int>();

            foreach (var instruction in block.Instructions)
            {
                foreach (var source in instruction.Sources)
                    foreach (var number in SourceRegisterNumbers(source,
                                 !_clobbering.Contains(instruction)))
                        if (!def.Contains(number))
                            use.Add(number);

                if (instruction.Destination is Register destination)
                    def.Add(destination.Number);

                if (instruction.ImplicitDefinition is { } clobbered)
                    def.Add(clobbered.Number);

                if (_clobbering.Contains(instruction))
                    foreach (var operand in instruction.Operands)
                        if (operand is AddressOf { Target: Register addressed })
                            def.Add(addressed.Number);
            }

            upwardExposedUse[block] = use;
            defs[block] = def;
        }

        var liveIn = graph.Blocks.ToDictionary(block => block, _ => new HashSet<int>());
        var liveOut = graph.Blocks.ToDictionary(block => block, _ => new HashSet<int>());
        var pending = new Queue<Block>(graph.Blocks);

        while (pending.Count > 0)
        {
            var block = pending.Dequeue();

            var outSet = new HashSet<int>();
            foreach (var successor in block.Successors)
                outSet.UnionWith(liveIn[successor]);
            liveOut[block] = outSet;

            var inSet = new HashSet<int>(upwardExposedUse[block]);
            foreach (var number in outSet)
                if (!defs[block].Contains(number))
                    inSet.Add(number);

            if (inSet.SetEquals(liveIn[block]))
                continue;

            liveIn[block] = inSet;
            foreach (var predecessor in block.Predecessors)
                pending.Enqueue(predecessor);
        }

        return liveIn;
    }

    private static IEnumerable<int> SourceRegisterNumbers(IOperand operand, bool includeAddressOfTargets)
    {
        switch (operand)
        {
            case Register register:
                yield return register.Number;
                break;
            case LocalVariable local:
                yield return local.Register.Number;
                break;
            case AddressOf { Target: Register addressed } when includeAddressOfTargets:
                yield return addressed.Number;
                break;
            case MemoryOperand memory:
                if (memory.Base is Register baseRegister)
                    yield return baseRegister.Number;
                if (memory.Index is Register indexRegister)
                    yield return indexRegister.Number;
                break;
        }
    }

    private static Dictionary<int, HashSet<Block>> GetDefinitionSites(ISILControlFlowGraph graph)
    {
        var defSites = new Dictionary<int, HashSet<Block>>();

        foreach (var block in graph.Blocks)
        {
            foreach (var operand in block.Def)
            {
                if (operand is not Register register)
                    continue;

                if (!defSites.TryGetValue(register.Number, out var sites))
                    defSites[register.Number] = sites = [];

                sites.Add(block);
            }
        }

        return defSites;
    }

    /// <summary>
    /// Inserts an unresolved phi node at the top of <paramref name="block"/> with one source slot
    /// per predecessor (positionally aligned to <see cref="Block.Predecessors"/>). The destination
    /// and source placeholders are versioned later during renaming.
    /// </summary>
    private void InsertPhiSkeleton(Block block, int regNumber)
    {
        var register = _repr[regNumber];

        var operands = new List<IOperand>(1 + block.Predecessors.Count) { register }; // destination first
        for (var i = 0; i < block.Predecessors.Count; i++)
            operands.Add(register); // one source per predecessor, filled in during renaming

        block.Instructions.Insert(0, new Instruction(-1, OpCode.Phi, operands));
    }

    private void Rename(Block initialBlock, DominatorInfo dominance)
    {
        var remaining = new Stack<(Stack<Block>, List<int>)>();
        remaining.Push((new Stack<Block>([initialBlock]), []));

        while (remaining.Count > 0)
        {
            var (blocks, parentDefinedRegisters) = remaining.Pop();
            if (blocks.Count == 0)
            {
                // Leaving the block: pop the versions it defined.
                foreach (var regNumber in parentDefinedRegisters)
                    _stacks[regNumber].Pop();

                continue;
            }

            var block = blocks.Pop();
            remaining.Push((blocks, parentDefinedRegisters));

            // Register numbers newly defined in this block, so we can pop their versions on the way out.
            var definedHere = new List<int>();

            foreach (var instruction in block.Instructions)
            {
                // A phi's operands belong to the incoming edges, so they are filled by predecessors;
                // only its destination is renamed here.
                if (instruction.OpCode != OpCode.Phi)
                    RewriteUses(instruction);

                if (instruction.Destination is Register definition)
                    instruction.Destination = NewName(definition, definedHere);

                // Nothing to write the new version back into, but taking it off the stack is the point: reads
                // after this one can't reach back past the call
                if (instruction.ImplicitDefinition is { } clobbered)
                    instruction.ImplicitDefinition = NewName(clobbered, definedHere);

                for (var i = 0; i < instruction.Operands.Count; i++)
                {
                    // Taking a slot's address lets the callee assign it, so the slot stops holding anything that reached this point, UNLESS
                    // nothing reads it afterwards, in which case any write is unobservable and the callee is only reading the value it has now
                    if (instruction.Operands[i] is AddressOf { Target: Register addressed })
                        instruction.SetOperand(i, new AddressOf(_clobbering.Contains(instruction)
                            ? NewName(addressed, definedHere)
                            : CurrentVersion(addressed.Number)));
                }
            }

            // Resolve the phi operands of successors that correspond to this block's outgoing edge.
            foreach (var successor in block.Successors)
            {
                var predIndex = successor.Predecessors.IndexOf(block);
                if (predIndex < 0)
                    continue;

                foreach (var phi in successor.Instructions)
                {
                    if (phi.OpCode != OpCode.Phi)
                        continue;

                    var regNumber = ((Register)phi.Operands[0]).Number;
                    phi.SetOperand(1 + predIndex, CurrentVersion(regNumber));
                }
            }

            // Recurse over the dominator tree.
            dominance.DominanceTree.TryGetValue(block, out var children);
            remaining.Push((new Stack<Block>(children ?? []), definedHere));
        }
    }

    private void RewriteUses(Instruction instruction)
    {
        for (var i = 0; i < instruction.Operands.Count; i++)
        {
            var operand = instruction.Operands[i];

            if (operand is Register register)
            {
                instruction.SetOperand(i, CurrentVersion(register.Number));
            }
            else if (operand is MemoryOperand memory)
            {
                if (memory.Base is Register baseRegister)
                    memory.Base = CurrentVersion(baseRegister.Number);
                if (memory.Index is Register indexRegister)
                    memory.Index = CurrentVersion(indexRegister.Number);

                instruction.SetOperand(i, memory); // MemoryOperand is a struct, write the copy back
            }
        }
    }

    /// <summary>
    /// The version of <paramref name="regNumber"/> currently in scope, or the entry value
    /// (version -1) if it has not been defined on the current path.
    /// </summary>
    private Register CurrentVersion(int regNumber)
    {
        if (_stacks.TryGetValue(regNumber, out var stack) && stack.Count > 0)
            return stack.Peek();

        return _repr.TryGetValue(regNumber, out var register) ? register : new Register(regNumber, null);
    }

    private Register NewName(Register register, List<int> definedHere)
    {
        var regNumber = register.Number;

        var version = _counter.TryGetValue(regNumber, out var current) ? current + 1 : 1;
        _counter[regNumber] = version;

        var versioned = register.Copy(version);

        if (!_stacks.TryGetValue(regNumber, out var stack))
            _stacks[regNumber] = stack = new Stack<Register>();

        stack.Push(versioned);
        definedHere.Add(regNumber);

        return versioned;
    }

    /// <summary>
    /// Destroys SSA form by replacing each phi with copies on the incoming edges. For a phi
    /// <c>dest = phi(s0, s1, ...)</c> a <c>Move dest, s[i]</c> is appended (before the terminator)
    /// to the i-th predecessor. Phi operands are positionally aligned to the predecessor list, so
    /// the i-th source belongs to the i-th predecessor.
    /// </summary>
    public static void Remove(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;

        foreach (var block in cfg.Blocks)
        {
            var phiInstructions = block.Instructions
                .Where(i => i.OpCode == OpCode.Phi)
                .ToList();

            if (phiInstructions.Count == 0)
                continue;

            for (var predIndex = 0; predIndex < block.Predecessors.Count; predIndex++)
            {
                var predecessor = block.Predecessors[predIndex];
                var moves = new List<Instruction>();

                foreach (var phi in phiInstructions)
                {
                    if (1 + predIndex >= phi.Operands.Count)
                        continue;

                    var destination = phi.Operands[0];
                    var source = phi.Operands[1 + predIndex];

                    // Skip redundant self-copies.
                    if (Equals(destination, source))
                        continue;

                    // Native registers can merge unrelated managed references at a
                    // control-flow join (especially normal and exception paths). Such
                    // a bit-pattern phi has no legal managed copy; emitting castclass
                    // makes the normal path throw. Leave that edge at default instead.
                    // Unlike the forwarding passes, this edge is emitted as a real store,
                    // so copies between managed pointers of different element types stay
                    // illegal here (a &U slot cannot receive a &T value).
                    if (destination is LocalVariable destinationLocal
                        && source is LocalVariable sourceLocal
                        && LocalVariables.NoLegalManagedCopy(destinationLocal, sourceLocal))
                        continue;

                    moves.Add(new Instruction(-1, OpCode.Move, destination, source));
                }

                InsertBeforeTerminator(predecessor, moves);
            }

            foreach (var phi in phiInstructions)
            {
                phi.OpCode = OpCode.Nop;
                phi.SetOperands();
            }
        }

        cfg.RemoveNops();
        cfg.RemoveEmptyBlocks();
    }

    /// <summary>
    /// Inserts <paramref name="moves"/> at the end of <paramref name="block"/>, but before any
    /// trailing control-flow instruction, so the copies execute on the outgoing edge.
    /// </summary>
    private static void InsertBeforeTerminator(Block block, List<Instruction> moves)
    {
        if (moves.Count == 0)
            return;

        var insertAt = block.Instructions.Count;

        if (insertAt > 0 && !block.Instructions[insertAt - 1].IsFallThrough)
            insertAt--;

        block.Instructions.InsertRange(insertAt, moves);
    }
}
