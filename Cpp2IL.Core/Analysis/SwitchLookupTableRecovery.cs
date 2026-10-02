using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL;
using LibCpp2IL.Elf;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Inverts LLVM's SwitchToLookupTable lowering: a switch whose non-default cases
/// all produce constants of one type compiles to an unsigned bounds check plus an
/// indexed read of a constant table (<c>ldr wN, [tbl, idx, uxtw #k]</c>) with no
/// per-case branches. In ISIL that survives as a guarded
/// <c>Move result, [table + addend + selector*elementSize]</c>, which emission can
/// only render as an "unmanaged memory load" throw.
///
/// When the load is provably behind an unsigned range check - the block's only
/// non-trampoline predecessor is a conditional branch whose edge reaching the
/// table holds exactly when the selector is in bounds - and the base resolves to
/// a fixed image address whose whole table range is read-only and never
/// relocation-patched (the same proof the lifter's constant-pool fold uses), every
/// element is known at analysis time. The block then becomes a real
/// <see cref="OpCode.Switch"/>: one case block per element writes the proven
/// constant into the result local and continues to the original successor, and
/// the guard's out-of-range successor is the switch's default. Anything not
/// proven keeps its load, and its diagnostic, untouched.
/// </summary>
public static class SwitchLookupTableRecovery
{
    // A bound past this stops resembling a switch lowering and would emit more
    // CIL than the method can justify; LLVM caps the tables it builds similarly.
    private const int MaxTableElements = 512;
    private const int MaxCopyDepth = 8;

    private enum FlagTest
    {
        Less,
        Equal,
    }

    /// <param name="readStaticBytes">Reads the bytes of an address range proven
    /// static and never patched, or returns null when the range cannot be
    /// proven. The default applies the ELF read-only segment rule the ARM64
    /// lifter uses before folding an absolute load to a literal.</param>
    public static int Run(MethodAnalysisContext method, Func<ulong, int, byte[]?>? readStaticBytes = null)
    {
        var cfg = method.ControlFlowGraph;
        if (cfg is null)
            return 0;

        readStaticBytes ??= (va, size) => ReadProvenBytes(method.AppContext.Binary, va, size);

        var definitions = BuildDefinitionMap(cfg);
        var recovered = 0;

        foreach (var block in cfg.Blocks.ToList())
            if (TryRecoverTableLoad(method, cfg, block, definitions, readStaticBytes))
                recovered++;

        return recovered;
    }

    private static bool TryRecoverTableLoad(MethodAnalysisContext method, ISILControlFlowGraph cfg,
        Block table, Dictionary<LocalVariable, List<Instruction>> definitions,
        Func<ulong, int, byte[]?> readStaticBytes)
    {
        // The lookup is the block's last real work before its terminator. Two
        // spellings of the same lowering survive lifting: `Move result, [tbl]
        // ; Jump|Return` when the read feeds a local, and `Return [tbl]` when
        // the method returns the element in place. The return spelling gets a
        // synthesized result local so both emit the same case blocks.
        if (table.Instructions.Count == 0)
            return false;
        var last = table.Instructions[^1];
        Instruction load;
        Instruction terminator;
        LocalVariable result;
        var consumed = 2;
        if (last.OpCode == OpCode.Return
            && last.Operands.Count >= 1
            && last.Operands[0] is MemoryOperand)
        {
            if (method.ReturnType is not { } returnType)
                return false;
            load = last;
            result = new LocalVariable($"switchTable{load.Index}", new Register(null, $"switchTable{load.Index}"), returnType);
            method.Locals.Add(result);
            terminator = new Instruction(-1, OpCode.Return, new List<IOperand> { result });
            consumed = 1;
        }
        else
        {
            if (table.Instructions.Count < 2)
                return false;
            load = table.Instructions[^2];
            terminator = last;
            if (load.OpCode != OpCode.Move
                || load.Operands is not [LocalVariable moveResult, MemoryOperand]
                || terminator.OpCode is not (OpCode.Jump or OpCode.Return))
                return false;
            result = moveResult;
        }

        if (load.Operands[^1] is not MemoryOperand memory
            || memory.Index is not LocalVariable selector
            || memory.Scale is not (> 0 and <= 8)
            || memory.AccessSize != memory.Scale)
            return false;
        var elementSize = memory.Scale;

        // The selector becomes the CIL switch input, which pops an integral
        // value; an i64 or native-int selector converts losslessly once the
        // bound proves it fits.
        if (IlGenerator.IntegralStackWidth(IlGenerator.EmittedOperandType(selector, method)) == 0)
            return false;

        // The constants fill the load's destination slot, which must be one an
        // Immediate literal can honestly carry: integral, floating-point or
        // unmanaged-pointer storage.
        if (!SlotAcceptsTableConstant(IlGenerator.EmittedOperandType(result, method)))
            return false;

        // The block must be reachable only through the bounds check; any other
        // entry is an unguarded read the switch's default edge would misroute.
        var sources = TrampolineSources(table);
        if (sources.Count != 1)
            return false;
        var guard = sources[0];
        if (guard.Instructions.Count == 0
            || guard.Instructions[^1] is not { OpCode: OpCode.ConditionalJump } jump
            || jump.Operands.Count < 2
            || jump.Operands[0] is not Block taken
            || jump.Operands[1] is not LocalVariable condition
            || guard.Successors.Count != 2
            || !guard.Successors.Contains(taken))
            return false;
        var fallThrough = guard.Successors.First(successor => !ReferenceEquals(successor, taken));

        // Which guard edge reaches the table block (through jump-only trampolines)?
        var onTakenEdge = ReachesThroughTrampolines(taken, table);
        var onFallThroughEdge = !onTakenEdge && ReachesThroughTrampolines(fallThrough, table);
        if (onTakenEdge == onFallThroughEdge)
            return false;

        var defaultBlock = SoleReachableWorkBlock(onTakenEdge ? fallThrough : taken);
        if (defaultBlock is null
            || ReferenceEquals(defaultBlock, table)
            || ReferenceEquals(defaultBlock, cfg.EntryBlock)
            || ReferenceEquals(defaultBlock, cfg.ExitBlock))
            return false;

        // The condition must be an unsigned bound on the same selector the
        // table indexes, holding exactly on the edge that reaches the load.
        if (!TryMatchRangeCheck(condition, definitions, out var comparedSelector,
                out var caseCount, out var inRangeOnTrue)
            || onTakenEdge != inRangeOnTrue
            || comparedSelector is null
            || !SameLocal(comparedSelector, selector))
            return false;

        // The table base must be a fixed image address, and every element must
        // come from bytes the binary proves static and never patched.
        if (ResolveConstantAddress(memory.Base, definitions) is not { } baseAddress)
            return false;
        var tableAddress = baseAddress + memory.Addend;
        if (tableAddress < 0)
            return false;
        var bytes = readStaticBytes((ulong)tableAddress, checked(caseCount * elementSize));
        if (bytes is null || bytes.Length < caseCount * elementSize)
            return false;

        var bigEndian = method.AppContext.Binary.IsBigEndian;
        var elements = new long[caseCount];
        for (var i = 0; i < caseCount; i++)
            elements[i] = DecodeElement(bytes, i * elementSize, elementSize, bigEndian);

        // One case block per element writes the proven constant and reuses the
        // original terminator; the load block itself ends in the switch.
        var caseBlocks = new List<Block>(caseCount);
        var switchOperands = new List<IOperand>(caseCount + 2) { defaultBlock, selector };
        for (var i = 0; i < caseCount; i++)
        {
            var caseMove = new Instruction(-1, OpCode.Move, result, new Immediate(elements[i], elementSize));
            var caseTerminator = new Instruction(-1, terminator.OpCode, terminator.Operands.ToList());
            var caseBlock = new Block();
            caseBlock.AddInstruction(caseMove);
            caseBlock.AddInstruction(caseTerminator);
            caseBlock.Predecessors.Add(table);
            if (terminator.OpCode == OpCode.Jump)
                caseBlock.Successors.Add((Block)terminator.Operands[0]);
            else
                caseBlock.Successors.Add(cfg.ExitBlock);
            caseBlock.CalculateBlockType();
            caseBlocks.Add(caseBlock);
            switchOperands.Add(caseMove);
        }

        for (var i = 0; i < consumed; i++)
            table.Instructions.RemoveAt(table.Instructions.Count - 1);
        table.AddInstruction(new Instruction(load.Index, OpCode.Switch, switchOperands) { NativeAddress = load.NativeAddress });

        foreach (var oldSuccessor in table.Successors.ToList())
            oldSuccessor.Predecessors.Remove(table);
        table.Successors.Clear();
        table.Successors.Add(defaultBlock);
        defaultBlock.Predecessors.Add(table);
        foreach (var caseBlock in caseBlocks)
        {
            table.Successors.Add(caseBlock);
            foreach (var successor in caseBlock.Successors)
                successor.Predecessors.Add(caseBlock);
        }
        table.CalculateBlockType();

        var insertAt = cfg.Blocks.IndexOf(table) + 1;
        var nextId = cfg.Blocks.Max(block => block.ID) + 1;
        foreach (var caseBlock in caseBlocks)
        {
            caseBlock.ID = nextId++;
            cfg.Blocks.Insert(insertAt++, caseBlock);
        }

        // The address computation that fed the memory operand is dead once the
        // base constant is folded into the switch: drop defs of a base local
        // nothing else reads so the dispatch decompiles as a plain switch.
        if (memory.Base is LocalVariable baseLocal
            && definitions.TryGetValue(baseLocal, out var baseDefs)
            && !cfg.Blocks.SelectMany(block => block.Instructions)
                .Where(instruction => !baseDefs.Contains(instruction))
                .SelectMany(instruction => instruction.Operands)
                .SelectMany(LocalVariables.OperandLocals)
                .Any(other => SameLocal(other, baseLocal)))
        {
            foreach (var deadDef in baseDefs)
                cfg.FindBlockByInstruction(deadDef)?.Instructions.Remove(deadDef);
        }

        return true;
    }

    /// <summary>
    /// The guard condition reduced to an unsigned <c>selector &lt; count</c> bound
    /// on the edge named by <paramref name="inRangeOnTrue"/>. Only raw unsigned
    /// flag shapes qualify: flagC with its lifting-time flag Nots (cs/cc) and the
    /// flagC/flagZ composites (hi/ls). A bare relational check is signed-ambiguous
    /// (FlagConditionRecovery produces it for signed jl/jge), and a signed bound
    /// would let a negative selector slip past the switch's unsigned dispatch.
    /// </summary>
    private static bool TryMatchRangeCheck(LocalVariable condition,
        Dictionary<LocalVariable, List<Instruction>> definitions,
        out LocalVariable? selector, out int caseCount, out bool inRangeOnTrue)
    {
        selector = null;
        caseCount = 0;
        inRangeOnTrue = false;

        var definition = UnderlyingDefinition(condition, definitions);
        if (definition is null)
            return false;

        var nots = 0;
        while (definition.OpCode == OpCode.Not
               && definition.Operands.Count >= 2
               && definition.Operands[1] is LocalVariable)
        {
            nots++;
            definition = UnderlyingDefinition(definition.Operands[1], definitions)!;
            if (definition is null)
                return false;
        }

        long bound;
        switch (definition.OpCode)
        {
            // `sel <u bound`, flagC raw: one outer flag Not is b.cs to the
            // default edge (in range on the false edge); two are b.cc to the
            // table edge (in range on the taken edge).
            case OpCode.CheckLess
                when nots is 1 or 2 && TryMatchLessBound(definition, out selector, out bound)
                     && bound is > 0 and <= MaxTableElements:
                caseCount = (int)bound;
                inRangeOnTrue = nots == 2;
                break;

            // flagC && !flagZ is `sel >u bound` (b.hi); !!flagC || flagZ is
            // `sel <=u bound` (b.ls). The table's element count is bound + 1.
            case OpCode.And or OpCode.Or
                when TryMatchBoundPair(definition, definitions, out selector, out bound,
                         out var trueMeansOutOfRange)
                     && bound is >= 0 and < MaxTableElements:
                caseCount = (int)bound + 1;
                inRangeOnTrue = trueMeansOutOfRange != (nots % 2 == 0);
                break;

            default:
                return false;
        }

        return caseCount > 0;
    }

    // `CheckLess(sel, imm)` - the arm64 flagC form of `sel <u imm`.
    private static bool TryMatchLessBound(Instruction definition, out LocalVariable? selector, out long bound)
    {
        selector = null;
        bound = 0;
        if (definition.Operands.Count < 3
            || SelectorLocal(definition.Operands[1]) is not { } sel
            || definition.Operands[2] is not Immediate immediate)
            return false;
        selector = sel;
        bound = immediate.Value;
        return true;
    }

    // `CheckEqual(sel, imm)` folded, or the flagZ shape `CheckEqual(t, 0)` on
    // `t = subtract(sel, imm)`.
    private static bool TryMatchEqualBound(Instruction definition,
        Dictionary<LocalVariable, List<Instruction>> definitions,
        out LocalVariable? selector, out long bound)
    {
        selector = null;
        bound = 0;
        if (definition.Operands.Count < 3)
            return false;
        // flagZ first: `CheckEqual(t, 0)` where t = subtract(sel, bound). The
        // folded `CheckEqual(sel, imm)` check must come second - the flagZ
        // operand also reads as a local-plus-immediate pair.
        if (definition.Operands[2] is Immediate { Value: 0 }
            && definition.Operands[1] is LocalVariable subLocal
            && UnderlyingDefinition(subLocal, definitions) is { OpCode: OpCode.Subtract } sub
            && sub.Operands.Count >= 3
            && SelectorLocal(sub.Operands[1]) is { } subSelector
            && sub.Operands[2] is Immediate subBound)
        {
            selector = subSelector;
            bound = subBound.Value;
            return true;
        }
        if (SelectorLocal(definition.Operands[1]) is { } eqSelector
            && definition.Operands[2] is Immediate eqBound)
        {
            selector = eqSelector;
            bound = eqBound.Value;
            return true;
        }
        return false;
    }

    // The operand an unsigned bound compares: the selector local itself, or a
    // `sel.value__` read through an enum's backing field - the same bits in a
    // different spelling.
    private static LocalVariable? SelectorLocal(IOperand operand) => operand switch
    {
        LocalVariable local => local,
        FieldReference { Field.Name: "value__", Containers.Count: 0, Offset: 0 } field => field.Local,
        _ => null,
    };

    // The two sides of an unsigned bound composite: the flagC form
    // `sel <u imm` and the flagZ form `sel == imm`, each read through its flag
    // Nots. `positive` reports whether the operand's truth is the test itself.
    private static bool TryClassifyFlagOperand(IOperand operand,
        Dictionary<LocalVariable, List<Instruction>> definitions,
        out FlagTest test, out LocalVariable? selector, out long bound, out bool positive)
    {
        test = default;
        selector = null;
        bound = 0;
        positive = true;

        var definition = UnderlyingDefinition(operand, definitions);
        if (definition is null)
            return false;

        var nots = 0;
        while (definition.OpCode == OpCode.Not
               && definition.Operands.Count >= 2
               && definition.Operands[1] is LocalVariable)
        {
            nots++;
            definition = UnderlyingDefinition(definition.Operands[1], definitions)!;
            if (definition is null)
                return false;
        }
        positive = nots % 2 == 0;

        switch (definition.OpCode)
        {
            case OpCode.CheckLess when nots > 0:
                test = FlagTest.Less;
                return TryMatchLessBound(definition, out selector, out bound);
            case OpCode.CheckEqual:
                test = FlagTest.Equal;
                return TryMatchEqualBound(definition, definitions, out selector, out bound);
            default:
                return false;
        }
    }

    // The two flag compositions an unsigned bound takes. `And` of `sel >=u N`
    // with `sel != N` is `sel >u N` - out of range when true. `Or` of
    // `sel <u N` with `sel == N` is `sel <=u N` - in range when true. Any other
    // polarity mix is a different predicate, not a table bound.
    private static bool TryMatchBoundPair(Instruction composite,
        Dictionary<LocalVariable, List<Instruction>> definitions,
        out LocalVariable? selector, out long bound, out bool trueMeansOutOfRange)
    {
        selector = null;
        bound = 0;
        trueMeansOutOfRange = false;

        if (composite.Operands.Count < 3
            || !TryClassifyFlagOperand(composite.Operands[1], definitions,
                out var aTest, out var aSelector, out var aBound, out var aPositive)
            || !TryClassifyFlagOperand(composite.Operands[2], definitions,
                out var bTest, out var bSelector, out var bBound, out var bPositive)
            || aTest == bTest
            || aBound != bBound
            || aSelector is null || bSelector is null
            || !SameLocal(aSelector, bSelector))
            return false;

        var lessPositive = (aTest == FlagTest.Less && aPositive) || (bTest == FlagTest.Less && bPositive);
        var lessNegative = (aTest == FlagTest.Less && !aPositive) || (bTest == FlagTest.Less && !bPositive);
        var equalPositive = (aTest == FlagTest.Equal && aPositive) || (bTest == FlagTest.Equal && bPositive);
        var equalNegative = (aTest == FlagTest.Equal && !aPositive) || (bTest == FlagTest.Equal && !bPositive);

        if (composite.OpCode == OpCode.And)
        {
            if (!(lessNegative && equalNegative && !lessPositive && !equalPositive))
                return false;
            trueMeansOutOfRange = true;
        }
        else
        {
            if (!(lessPositive && equalPositive && !lessNegative && !equalNegative))
                return false;
        }

        selector = aSelector;
        bound = aBound;
        return true;
    }

    /// <summary>
    /// The local's single non-Move definition, chasing Move copies. Post-SSA a
    /// local may have several definitions; anything ambiguous returns null.
    /// </summary>
    private static Instruction? UnderlyingDefinition(IOperand operand,
        Dictionary<LocalVariable, List<Instruction>> definitions)
    {
        for (var depth = 0; depth < MaxCopyDepth; depth++)
        {
            if (operand is not LocalVariable local
                || !definitions.TryGetValue(local, out var defs)
                || defs.Count != 1)
                return null;
            var definition = defs[0];
            if (definition.OpCode != OpCode.Move || definition.Operands.Count < 2)
                return definition;
            operand = definition.Operands[1];
            if (operand is not LocalVariable)
                return definition;
        }
        return null;
    }

    /// <summary>
    /// A memory-operand base resolved to its fixed image address: an Immediate,
    /// or a local every definition of which is a Move of that same immediate.
    /// </summary>
    private static long? ResolveConstantAddress(IOperand? operand,
        Dictionary<LocalVariable, List<Instruction>> definitions, int depth = 0)
    {
        if (operand is null || depth > MaxCopyDepth)
            return operand is null ? 0 : null;
        switch (operand)
        {
            case Immediate immediate:
                return immediate.Value;
            case LocalVariable local:
                if (!definitions.TryGetValue(local, out var defs) || defs.Count == 0)
                    return null;
                long? address = null;
                foreach (var definition in defs)
                {
                    if (definition.OpCode != OpCode.Move || definition.Operands.Count < 2)
                        return null;
                    var resolved = ResolveConstantAddress(definition.Operands[1], definitions, depth + 1);
                    if (resolved is null)
                        return null;
                    if (address is null)
                        address = resolved;
                    else if (address != resolved)
                        return null;
                }
                return address;
            default:
                return null;
        }
    }

    /// <summary>
    /// Every non-trampoline predecessor of the block; jump/nop-only blocks are
    /// transparent, so the guard behind them still counts as the entry.
    /// </summary>
    private static List<Block> TrampolineSources(Block block)
    {
        var sources = new List<Block>();
        var seen = new HashSet<Block>();
        var pending = new Stack<Block>(block.Predecessors);
        while (pending.Count > 0)
        {
            var current = pending.Pop();
            if (!seen.Add(current))
                continue;
            if (IsTrampoline(current))
                foreach (var predecessor in current.Predecessors)
                    pending.Push(predecessor);
            else
                sources.Add(current);
        }
        return sources;
    }

    private static bool IsTrampoline(Block block) =>
        block.Instructions.All(instruction => instruction.OpCode is OpCode.Jump or OpCode.Nop);

    private static bool ReachesThroughTrampolines(Block from, Block into)
    {
        var seen = new HashSet<Block>();
        var pending = new Stack<Block>();
        pending.Push(from);
        while (pending.Count > 0)
        {
            var current = pending.Pop();
            if (ReferenceEquals(current, into))
                return true;
            if (!seen.Add(current) || !IsTrampoline(current))
                continue;
            foreach (var successor in current.Successors)
                pending.Push(successor);
        }
        return false;
    }

    // The single real block a successor edge lands on, through trampolines.
    private static Block? SoleReachableWorkBlock(Block start)
    {
        var seen = new HashSet<Block>();
        var work = new HashSet<Block>();
        var pending = new Stack<Block>();
        pending.Push(start);
        while (pending.Count > 0)
        {
            var current = pending.Pop();
            if (!seen.Add(current))
                continue;
            if (IsTrampoline(current))
                foreach (var successor in current.Successors)
                    pending.Push(successor);
            else
                work.Add(current);
        }
        return work.Count == 1 ? work.First() : null;
    }

    /// <summary>
    /// Reads a range the binary proves static and never patched: the address
    /// comes from the instruction stream (never a loaded pointer), and the
    /// whole range sits inside a read-only PT_LOAD - relocations can only patch
    /// writable pages. Non-ELF binaries carry no such proof, so the load keeps
    /// its diagnostic there.
    /// </summary>
    private static byte[]? ReadProvenBytes(Il2CppBinary binary, ulong address, int size)
    {
        if (binary is not ElfFile elf
            || !elf.IsReadOnlyRange(address, size)
            || !binary.TryMapVirtualAddressToRaw(address, out var raw)
            || raw < 0)
            return null;
        try
        {
            var bytes = binary.ReadByteArrayAtRawAddress(raw, size);
            return bytes.Length == size ? bytes : null;
        }
        catch
        {
            return null;
        }
    }

    // Table elements are read as the register write zero-extends them: byte
    // and halfword elements never set their high bits, matching `ldrb`/`ldrh`.
    private static long DecodeElement(byte[] bytes, int offset, int size, bool bigEndian) => size switch
    {
        1 => bytes[offset],
        2 => bigEndian
            ? BinaryPrimitives.ReadUInt16BigEndian(bytes.AsSpan(offset, 2))
            : BinaryPrimitives.ReadUInt16LittleEndian(bytes.AsSpan(offset, 2)),
        4 => bigEndian
            ? BinaryPrimitives.ReadUInt32BigEndian(bytes.AsSpan(offset, 4))
            : BinaryPrimitives.ReadUInt32LittleEndian(bytes.AsSpan(offset, 4)),
        _ => bigEndian
            ? BinaryPrimitives.ReadInt64BigEndian(bytes.AsSpan(offset, 8))
            : BinaryPrimitives.ReadInt64LittleEndian(bytes.AsSpan(offset, 8)),
    };

    // The slot a proven literal must fill: integral, floating-point or
    // unmanaged-pointer storage - the operand forms emission renders honestly.
    // Anything else (managed references, structs, byrefs) cannot take a byte
    // pattern the image proves.
    private static bool SlotAcceptsTableConstant(TypeAnalysisContext? slot) =>
        slot is not null and not ByRefTypeAnalysisContext
        && (IlGenerator.IntegralStackWidth(slot) != 0
            || slot.FullName is "System.Single" or "System.Double");

    private static bool SameLocal(LocalVariable a, LocalVariable b) =>
        ReferenceEquals(a, b)
        || (a.Name == b.Name && a.Register.Name == b.Register.Name
            && a.Register.Number == b.Register.Number);

    private static Dictionary<LocalVariable, List<Instruction>> BuildDefinitionMap(ISILControlFlowGraph cfg)
    {
        var definitions = new Dictionary<LocalVariable, List<Instruction>>();
        foreach (var block in cfg.Blocks)
            foreach (var instruction in block.Instructions)
                if (instruction.Destination is LocalVariable destination)
                {
                    if (!definitions.TryGetValue(destination, out var list))
                        definitions[destination] = list = [];
                    list.Add(instruction);
                }
        return definitions;
    }
}
