using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// clang tail-duplicates the code after <c>if (!K-&gt;cctor_finished) il2cpp_runtime_class_init(K);</c>
/// into both arms, so the arms never reconverge right after the call: the init arm is a copy of
/// the skip arm with the call, and the reloads the call forced, in front. This proves the two copies
/// do the same thing - the same effects in the same order on equal values, the same branches to the
/// same places, equal inputs to the phis where they rejoin - and then sends the guard straight to
/// the skip arm and deletes the copy.
/// </summary>
/// <remarks>
/// Values are compared as expressions over the values live before the guard: a copy is its source,
/// a phi whose inputs agree is that input, a pure op is its operator over its operands' expressions,
/// and a load is its address plus the number of effects run before it in its arm - the copy's
/// reloads read what the skip arm's earlier loads read, because the class initializer has already
/// run (or is running on this thread) by the time a managed static access executes. Matched call
/// results are equal by construction. Anything else is a distinct value, so an unproven difference
/// keeps the guard.
/// </remarks>
internal sealed class ClassInitArmMerger
{
    private const int MaxSteps = 4096;
    private const int MaxDepth = 24;

    private readonly ISILControlFlowGraph _cfg;
    private readonly Block _guard;
    private readonly Func<Instruction, bool> _isClassInit;
    private readonly Dictionary<LocalVariable, Instruction?> _definitions = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<LocalVariable, string> _keys = new(ReferenceEqualityComparer.Instance);
    private readonly HashSet<LocalVariable> _inProgress = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<Instruction, int> _epochs = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<object, int> _ids = new();
    private readonly HashSet<Block> _initArm = [];
    private readonly HashSet<Block> _skipArm = [];
    private readonly HashSet<Block> _passedThrough = [];
    private readonly List<(Block Join, Block InitEdge, Block SkipEdge)> _joins = [];
    private int _steps;
    private int _nextJoinEpoch = 1 << 20;

    private ClassInitArmMerger(ISILControlFlowGraph cfg, Block guard, Func<Instruction, bool> isClassInit)
    {
        _cfg = cfg;
        _guard = guard;
        _isClassInit = isClassInit;
        foreach (var instruction in cfg.Instructions)
            if (instruction.Destination is LocalVariable local)
                _definitions[local] = _definitions.ContainsKey(local) ? null : instruction;
    }

    /// <summary>
    /// Folds <paramref name="guard"/> to its <paramref name="skipEntry"/> arm when the
    /// <paramref name="initEntry"/> arm is proven to be a copy of it plus class-init calls.
    /// </summary>
    public static bool TryMerge(ISILControlFlowGraph cfg, Block guard, Block initEntry, Block skipEntry,
        Func<Instruction, bool> isClassInit)
    {
        if (initEntry == skipEntry)
            return false;

        var merger = new ClassInitArmMerger(cfg, guard, isClassInit);
        if (!merger.ProveEquivalent(initEntry, skipEntry) || merger._initArm.Count == 0 || !merger.CopyStaysInside())
            return false;

        cfg.RemovePredecessor(initEntry, guard);
        guard.Successors.Remove(initEntry);
        var terminator = guard.Instructions[^1];
        terminator.OpCode = OpCode.Jump;
        terminator.SetOperands(skipEntry);
        guard.CalculateBlockType();

        // The copy is now reachable from nowhere; detaching it drops its phi inputs at every join.
        cfg.RemoveUnreachableBlocks();
        return true;
    }

    private sealed class Cursor(Block block, Block from, HashSet<Block> arm)
    {
        public Block Block = block;
        public Block From = from;
        public int Index;
        public bool Entered;
        public bool PassingThrough;
        public readonly HashSet<Block> Arm = arm;

        public void Step(Block target)
        {
            From = Block;
            Block = target;
            Index = 0;
            Entered = false;
            PassingThrough = false;
        }
    }

    private abstract record Event;

    private sealed record Effect(Instruction Instruction) : Event;

    private sealed record Branch(Instruction Jump, Block From, Block Taken, Block NotTaken) : Event;

    private sealed record Join(Block Block, Block From) : Event;

    private bool ProveEquivalent(Block initEntry, Block skipEntry)
    {
        var work = new Queue<(Cursor Init, Cursor Skip, int Epoch)>();
        var pending = new List<(Cursor Init, Cursor Skip, int Epoch, Join InitJoin, Join SkipJoin)>();
        work.Enqueue((new Cursor(initEntry, _guard, _initArm), new Cursor(skipEntry, _guard, _skipArm), 0));

        while (work.Count > 0 || pending.Count > 0)
        {
            if (work.Count == 0 && !ResolvePending(pending, work))
                return false;

            var (init, skip, epoch) = work.Dequeue();
            while (true)
            {
                var initEvent = Advance(init, epoch);
                var skipEvent = Advance(skip, epoch);

                switch (initEvent, skipEvent)
                {
                    case (Effect a, Effect b):
                        if (!SameEffect(a.Instruction, b.Instruction))
                            return false;
                        epoch++;
                        continue;

                    case (Branch a, Branch b):
                        var (initCondition, initNegated) = Condition(a.Jump.Operands[1]);
                        var (skipCondition, skipNegated) = Condition(b.Jump.Operands[1]);
                        if (initCondition != skipCondition)
                            return false;
                        var flipped = initNegated != skipNegated;
                        work.Enqueue((new Cursor(a.Taken, a.From, _initArm),
                            new Cursor(flipped ? b.NotTaken : b.Taken, b.From, _skipArm), epoch));
                        work.Enqueue((new Cursor(a.NotTaken, a.From, _initArm),
                            new Cursor(flipped ? b.Taken : b.NotTaken, b.From, _skipArm), epoch));
                        break;

                    case (Join a, Join b) when a.Block == b.Block:
                        _joins.Add((a.Block, a.From, b.From));
                        break;

                    // Different joins wait until every path has arrived: they are either the two
                    // copies of one join inside the duplicated code, or one side still has to run
                    // through a shared block on its way to the other's.
                    case (Join a, Join b):
                        pending.Add((init, skip, epoch, a, b));
                        break;

                    default:
                        return false;
                }

                break;
            }
        }

        // Where the copies rejoin, each phi must receive the same value from both.
        foreach (var (join, initEdge, skipEdge) in _joins)
        {
            var initIndex = join.Predecessors.IndexOf(initEdge);
            var skipIndex = join.Predecessors.IndexOf(skipEdge);
            if (initIndex < 0 || skipIndex < 0)
                return false;
            foreach (var phi in join.Instructions.Where(i => i.OpCode == OpCode.Phi))
                if (1 + Math.Max(initIndex, skipIndex) >= phi.Operands.Count
                    || Key(phi.Operands[1 + initIndex]) != Key(phi.Operands[1 + skipIndex]))
                    return false;
        }

        return true;
    }

    // Runs a cursor up to its next effect, branch, or edge into a block its arm does not own.
    private Event? Advance(Cursor cursor, int epoch)
    {
        while (++_steps < MaxSteps)
        {
            if (!cursor.Entered)
            {
                var block = cursor.Block;
                if (block == _cfg.EntryBlock || block == _guard)
                    return null;
                if (block == _cfg.ExitBlock || block.Predecessors.Count != 1)
                    return new Join(block, cursor.From);
                if (_initArm.Contains(block) || _skipArm.Contains(block) || _passedThrough.Contains(block))
                    return null;
                cursor.Arm.Add(block);
                cursor.Entered = true;
            }

            if (cursor.Index >= cursor.Block.Instructions.Count)
            {
                if (cursor.Block.Successors.Count != 1)
                    return null;
                cursor.Step(cursor.Block.Successors[0]);
                continue;
            }

            var instruction = cursor.Block.Instructions[cursor.Index++];
            switch (instruction.OpCode)
            {
                // An owned block has one predecessor, so its phis are copies; a block run through
                // has its phis bound to the incoming edge.
                case OpCode.Nop:
                case OpCode.Phi:
                    continue;
                case OpCode.Jump when instruction.Operands is [Block target] && cursor.Block.Successors.Contains(target):
                    cursor.Step(target);
                    continue;
                case OpCode.ConditionalJump when !cursor.PassingThrough
                                                 && instruction.Operands is [Block taken, _]
                                                 && cursor.Block.Successors.Count == 2
                                                 && cursor.Block.Successors.FirstOrDefault(s => s != taken) is { } notTaken:
                    return new Branch(instruction, cursor.Block, taken, notTaken);
                case OpCode.Jump or OpCode.ConditionalJump:
                    return null;
            }

            if (_isClassInit(instruction))
                continue;
            if (IsPure(instruction))
            {
                _epochs[instruction] = epoch;
                continue;
            }

            return cursor.PassingThrough ? null : new Effect(instruction);
        }

        return null;
    }

    // A shared block only computes and falls through: running it on the way costs nothing.
    private bool CanPassThrough(Block block) =>
        block != _cfg.EntryBlock && block != _cfg.ExitBlock && block != _guard
        && !_initArm.Contains(block) && !_skipArm.Contains(block) && !_passedThrough.Contains(block)
        && block.Successors.Count == 1
        && block.Instructions.All(i => i.OpCode is OpCode.Nop or OpCode.Phi || IsPure(i) || _isClassInit(i)
                                       || i.OpCode == OpCode.Jump && i == block.Instructions[^1]);

    private bool ResolvePending(List<(Cursor Init, Cursor Skip, int Epoch, Join InitJoin, Join SkipJoin)> pending,
        Queue<(Cursor Init, Cursor Skip, int Epoch)> work)
    {
        // Two copies of one join: every edge into each comes from its own arm, paired path by path.
        foreach (var group in pending.GroupBy(p => (p.InitJoin.Block, p.SkipJoin.Block)).ToList())
        {
            var (initJoin, skipJoin) = group.Key;
            var edges = group.ToList();
            if (edges.Count != initJoin.Predecessors.Count || edges.Count != skipJoin.Predecessors.Count
                || edges.Select(e => e.InitJoin.From).Distinct().Count() != edges.Count
                || edges.Select(e => e.SkipJoin.From).Distinct().Count() != edges.Count
                || !Claimable(initJoin) || !Claimable(skipJoin))
                continue;

            // Each phi of one copy pairs with a phi of the other fed equal values on every path.
            var skipPhis = skipJoin.Instructions.Where(i => i.OpCode == OpCode.Phi).ToList();
            foreach (var initPhi in initJoin.Instructions.Where(i => i.OpCode == OpCode.Phi))
            {
                var match = skipPhis.FirstOrDefault(skipPhi => edges.All(e =>
                    Input(initPhi, initJoin, e.InitJoin.From) is { } initInput
                    && Input(skipPhi, skipJoin, e.SkipJoin.From) is { } skipInput
                    && Key(initInput) == Key(skipInput)));
                if (match == null || initPhi.Operands[0] is not LocalVariable initMerged
                                  || match.Operands[0] is not LocalVariable skipMerged)
                    continue;
                skipPhis.Remove(match);
                _keys[initMerged] = _keys[skipMerged] = $"(phi {Id(initPhi)})";
            }

            _initArm.Add(initJoin);
            _skipArm.Add(skipJoin);
            pending.RemoveAll(p => p.InitJoin.Block == initJoin && p.SkipJoin.Block == skipJoin);

            // Paths may have run different effects before rejoining: loads after the join are
            // compared at a fresh epoch, equal across the two copies and to nothing earlier.
            var epoch = _nextJoinEpoch++;
            work.Enqueue((new Cursor(initJoin, edges[0].InitJoin.From, _initArm) { Entered = true },
                new Cursor(skipJoin, edges[0].SkipJoin.From, _skipArm) { Entered = true }, epoch));
            return true;
        }

        // A shared block that only computes, on the way from one side's join to the other's.
        foreach (var item in pending)
        {
            Cursor? runner = null;
            if (CanPassThrough(item.InitJoin.Block) && PassThroughChain(item.InitJoin.Block).Contains(item.SkipJoin.Block))
                runner = item.Init;
            else if (CanPassThrough(item.SkipJoin.Block) && PassThroughChain(item.SkipJoin.Block).Contains(item.InitJoin.Block))
                runner = item.Skip;
            if (runner == null || !PassThrough(runner))
                continue;

            pending.Remove(item);
            work.Enqueue((item.Init, item.Skip, item.Epoch));
            return true;
        }

        return false;
    }

    private static IOperand? Input(Instruction phi, Block join, Block from)
    {
        var index = join.Predecessors.IndexOf(from);
        return index >= 0 && 1 + index < phi.Operands.Count ? phi.Operands[1 + index] : null;
    }

    private bool Claimable(Block block) =>
        block != _cfg.EntryBlock && block != _cfg.ExitBlock && block != _guard
        && !_initArm.Contains(block) && !_skipArm.Contains(block) && !_passedThrough.Contains(block);

    // The blocks reached by running through computing-only blocks from `block`.
    private List<Block> PassThroughChain(Block block)
    {
        var chain = new List<Block>();
        while (CanPassThrough(block) && !chain.Contains(block))
        {
            chain.Add(block);
            block = block.Successors[0];
        }

        chain.Add(block);
        return chain;
    }

    private bool PassThrough(Cursor cursor)
    {
        var block = cursor.Block;
        var edge = block.Predecessors.IndexOf(cursor.From);
        if (edge < 0)
            return false;

        // On this path each phi is the input arriving on our edge.
        foreach (var phi in block.Instructions.Where(i => i.OpCode == OpCode.Phi))
        {
            if (phi.Operands[0] is not LocalVariable merged || 1 + edge >= phi.Operands.Count)
                return false;
            _keys[merged] = Key(phi.Operands[1 + edge]);
        }

        _passedThrough.Add(block);
        cursor.Entered = true;
        cursor.PassingThrough = true;
        return true;
    }

    // Locals the copy defines may only flow out through the phis that lose its edges.
    private bool CopyStaysInside()
    {
        var defined = new HashSet<LocalVariable>(ReferenceEqualityComparer.Instance);
        foreach (var block in _initArm)
            foreach (var instruction in block.Instructions)
                if (instruction.Destination is LocalVariable local)
                    defined.Add(local);

        return _cfg.Blocks.Where(block => !_initArm.Contains(block))
            .SelectMany(block => block.Instructions)
            .Where(instruction => instruction.OpCode != OpCode.Phi)
            .All(instruction => !instruction.Operands.Any(operand => Mentions(operand, defined)));
    }

    private static bool Mentions(IOperand operand, HashSet<LocalVariable> locals) => operand switch
    {
        LocalVariable local => locals.Contains(local),
        MemoryOperand memory => memory.Base != null && Mentions(memory.Base, locals)
                                || memory.Index != null && Mentions(memory.Index, locals),
        _ => false,
    };

    private static bool IsPure(Instruction instruction) =>
        instruction.Destination is LocalVariable
        && instruction.OpCode is OpCode.Move or OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide
            or OpCode.Modulo or OpCode.ShiftLeft or OpCode.ShiftRight or OpCode.And or OpCode.Or or OpCode.Xor
            or OpCode.Not or OpCode.Negate or OpCode.VectorMin or OpCode.VectorMax or OpCode.SignExtend32
            or OpCode.Convert or (>= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual);

    private bool SameEffect(Instruction a, Instruction b)
    {
        // Registers a call defines implicitly have no definition here, so any later read of them
        // stays a distinct value on each side.
        if (a.OpCode != b.OpCode || a.Operands.Count != b.Operands.Count || Flags(a) != Flags(b))
            return false;

        var aResult = a.Destination as LocalVariable;
        var bResult = b.Destination as LocalVariable;
        if ((aResult == null) != (bResult == null))
            return false;

        for (var i = 0; i < a.Operands.Count; i++)
        {
            if (aResult != null && ReferenceEquals(a.Operands[i], aResult) && ReferenceEquals(b.Operands[i], bResult))
                continue;
            if (Key(a.Operands[i]) != Key(b.Operands[i]))
                return false;
        }

        // A matched effect's results are one value.
        if (aResult != null)
            _keys[aResult] = _keys[bResult!] = $"(result {Id(a)})";
        return true;
    }

    // The value a branch tests, with the negations peeled off: !x and x != y test x and x == y.
    private (string Key, bool Negated) Condition(IOperand operand)
    {
        var negated = false;
        for (var depth = 0; depth < 8 && operand is LocalVariable local; depth++)
        {
            switch (Definition(local))
            {
                case { OpCode: OpCode.Not, Operands: [_, var inner] }:
                    negated = !negated;
                    operand = inner;
                    continue;
                case { OpCode: OpCode.CheckNotEqual, Operands: [_, var left, var right] } check:
                    return ($"(CheckEqual{Flags(check)} {Key(left)} {Key(right)})", !negated);
            }

            break;
        }

        return (Key(operand), negated);
    }

    private Instruction? Definition(LocalVariable local) =>
        _definitions.TryGetValue(local, out var definition) ? definition : null;

    private string Key(IOperand? operand, int depth = 0) => operand switch
    {
        null => "",
        LocalVariable local => LocalKey(local, depth),
        MemoryOperand memory =>
            $"[{Key(memory.Base, depth + 1)}+{Key(memory.Index, depth + 1)}*{memory.Scale}+{memory.Addend}:{memory.AccessSize}]",
        Immediate immediate => $"#{immediate.Value}",
        StringLiteral literal => $"\"{literal.Value}\"",
        _ => $"@{Id(operand)}",
    };

    private string LocalKey(LocalVariable local, int depth)
    {
        if (_keys.TryGetValue(local, out var known))
            return known;
        if (depth > MaxDepth || !_inProgress.Add(local))
            return $"L{Id(local)}";

        var key = Expand(local, depth);
        _inProgress.Remove(local);
        _keys[local] = key;
        return key;
    }

    private string Expand(LocalVariable local, int depth)
    {
        var identity = $"L{Id(local)}";
        if (Definition(local) is not { } definition)
            return identity;

        if (definition.OpCode == OpCode.Phi)
        {
            // A phi whose inputs (other than itself around a loop) are one value is that value.
            var inputs = definition.Operands.Skip(1)
                .Where(input => input is not LocalVariable inputLocal || !_inProgress.Contains(inputLocal))
                .Select(input => Key(input, depth + 1))
                .Distinct()
                .ToList();
            return inputs is [var single] ? single : identity;
        }

        if (!IsPure(definition))
            return identity;

        if (definition is { OpCode: OpCode.Move, Operands: [_, var source] })
            return source is MemoryOperand
                ? $"(load{(_epochs.TryGetValue(definition, out var epoch) ? epoch : 0)} {Key(source, depth + 1)})"
                : Key(source, depth + 1);

        return $"({definition.OpCode}{Flags(definition)} {string.Join(" ", definition.Operands.Skip(1).Select(o => Key(o, depth + 1)))})";
    }

    private static string Flags(Instruction instruction) =>
        $"|{instruction.IsVirtualDispatch}|{instruction.ThrowFromNonReturningCall}|{instruction.NativeIntegerWidthBits}"
        + $"|{instruction.NativeFloatWidthBits}|{instruction.NativeFloatWriteBits}|{instruction.NativeMemoryAccessSize}"
        + $"|{instruction.NativeStoreWidthBytes}|{instruction.ConversionFromFloat}|{instruction.ConversionUnsigned}"
        + $"|{instruction.ConversionSourceWidthBits}|{instruction.NativeReadWidthBits}|{instruction.NativeReadSignExtend}|";

    private int Id(object value)
    {
        // Locals and instructions are identities; other operands use their own equality.
        if (value is LocalVariable or Instruction or Block)
            value = new IdentityBox(value);
        if (!_ids.TryGetValue(value, out var id))
            _ids[value] = id = _ids.Count;
        return id;
    }

    private sealed class IdentityBox(object value)
    {
        private readonly object _value = value;
        public override bool Equals(object? other) => other is IdentityBox box && ReferenceEquals(box._value, _value);
        public override int GetHashCode() => System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(_value);
    }
}
