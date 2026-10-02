using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// The inverse of il2cpp-null-check and il2cpp-bounds-check. IL2CPP puts <c>NullCheck(x)</c> before
/// every dereference of a reference and <c>IL2CPP_ARRAY_BOUNDS_CHECK(index, length)</c> before every
/// array element - one per dimension inside a T[,]'s Get/Set/Address. Each fails by calling a
/// non-returning runtime helper (<c>il2cpp_codegen_raise_null_reference_exception</c>,
/// <c>..._index_out_of_range_exception</c>), which lifts to a bare <c>Throw</c> of the helper's
/// exception type. The source IL has neither check: ldfld, ldlen, ldelem, callvirt and the array
/// accessors fail the same way on their own.
///
/// A branch into such a raise that guards exactly the access il2cpp guards is that access's check
/// and is removed: the same reference is dereferenced, or the same index is used against the same
/// array's length in the same dimension, with nothing observable in between. A user-written
/// <c>throw new NullReferenceException()</c> constructs its exception and raises the object (a Throw
/// of a local), so it never matches. A removed null check that guarded a direct instance call says
/// the source called it with callvirt, which IL generation reads back.
///
/// Runs after <see cref="ArrayRecovery.Run"/>: a T[,] index is only recovered while its bounds
/// check still proves it, and only then are its accesses Get/Set/Address calls to match.
/// </summary>
public static class Il2CppCheckRecovery
{
    private const string NullCheckedCallsKey = "Il2CppCheckRecovery.NullCheckedCalls";
    private const string NullReference = "System.NullReferenceException";
    private const string IndexOutOfRange = "System.IndexOutOfRangeException";
    private const int TraceBlocks = 8;

    internal static bool ReceiverWasNullChecked(MethodAnalysisContext method, Instruction call)
        => call.Operands.FirstOrDefault() is MethodAnalysisContext { IsStatic: false, Name: not ".ctor" }
           && method.GetExtraData<HashSet<Instruction>>(NullCheckedCallsKey)?.Contains(call) == true;

    public static void Run(MethodAnalysisContext method)
    {
        var lengthCalls = new HashSet<Instruction>();
        // The accesses whose checks are gone, by the exception each now raises on its own: a check
        // of the other kind may not be moved past one, or the two exceptions would swap order.
        var guarded = new Dictionary<Instruction, string>();
        // The access is the innermost: a T[,]'s second-dimension check sits between its first and
        // the element, and the null check before them all, so peel outwards one round at a time.
        for (var round = 0; round < 8 && RemoveRound(method, IndexOutOfRange, lengthCalls, guarded); round++)
        {
        }

        for (var round = 0; round < 8 && RemoveRound(method, NullReference, lengthCalls, guarded); round++)
        {
        }
    }

    private static bool RemoveRound(MethodAnalysisContext method, string exception, HashSet<Instruction> lengthCalls,
        Dictionary<Instruction, string> guarded)
    {
        var cfg = method.ControlFlowGraph!;
        var removed = false;
        var facts = new MethodFacts(cfg);
        foreach (var block in cfg.Blocks.ToList())
        {
            if (block.Instructions.LastOrDefault() is not { OpCode: OpCode.ConditionalJump, Operands: [Block target, _] } branch
                || block.Successors.Count != 2
                || block.Successors.FirstOrDefault(s => s != target) is not { } fallThrough
                || fallThrough == cfg.ExitBlock || target == cfg.ExitBlock)
                continue;

            var throwsOnTrue = Raises(target) == exception;
            if (!throwsOnTrue && Raises(fallThrough) != exception)
                continue;
            var raise = throwsOnTrue ? target : fallThrough;
            var trace = new Trace(block, throwsOnTrue ? fallThrough : target, cfg, facts, guarded);
            var usedLengths = new HashSet<Instruction>();
            Instruction? checkedCall = null;
            if ((exception == IndexOutOfRange ? !trace.ProvesBoundsCheck(throwsOnTrue, usedLengths)
                    : !trace.ProvesNullCheck(throwsOnTrue, out checkedCall))
                || FallsIntoProtectedCall(method, raise))
                continue;

            branch.OpCode = OpCode.Nop;
            branch.SetOperands();
            block.Successors.Remove(raise);
            cfg.RemovePredecessor(raise, block);
            block.CalculateBlockType();
            lengthCalls.UnionWith(usedLengths);
            guarded[trace.Access!] = exception;
            if (checkedCall != null)
                NullCheckedCalls(method).Add(checkedCall);
            removed = true;
        }

        if (!removed)
            return false;

        cfg.RemoveUnreachableBlocks();
        DeadCodeEliminator.Run(cfg, method);
        // The lengths a removed bounds check compared are GetLength calls ArrayRecovery made; with
        // the check gone nothing reads them.
        var read = cfg.Instructions.SelectMany(DeadCodeEliminator.UsedLocals).ToHashSet();
        foreach (var call in lengthCalls)
            if (call.Destination is LocalVariable length && !read.Contains(length))
            {
                call.OpCode = OpCode.Nop;
                call.SetOperands();
            }
        return true;
    }

    // InjectedCheckRemover drops null checks without proving what they guarded. When one guarded a
    // direct instance call on the checked reference, the source made that call with callvirt.
    internal static void MarkCheckedReceiver(MethodAnalysisContext method, Block block, Block raise)
    {
        if (block.Successors.FirstOrDefault(successor => successor != raise) is not { } next)
            return;
        if (new Trace(block, next, method.ControlFlowGraph!, null, []).ProvesNullCheck(true, out var call) && call != null)
            NullCheckedCalls(method).Add(call);
    }

    // A method with landing pads has its regions proven on the native code, where
    // NativeExceptionRegionProof learns which calls never return from the Throws left in the graph.
    // Once a raise is gone - with its last check, here or in a later pass - its call seems to fall
    // through into the native instructions after it and to merge its frame into theirs. When that
    // reaches a call inside a protected range before a landing pad, that call site's handler could
    // no longer be proven, so the checks raising there stay.
    private static bool FallsIntoProtectedCall(MethodAnalysisContext method, Block raise)
    {
        if (method.UnwindInfo is not { CallSites.Count: > 0 } unwind || method.ExceptionRegionInstructions is not { } native)
            return false;
        var pads = unwind.CallSites.Select(site => site.LandingPad).ToHashSet();
        var addresses = native.Select(i => i.NativeAddress).Where(a => a != 0).Distinct().Order().ToList();
        foreach (var call in raise.Instructions.Where(i => i.OpCode == OpCode.Throw && i.NativeAddress != 0))
        {
            var found = addresses.BinarySearch(call.NativeAddress);
            for (var next = found >= 0 ? found + 1 : ~found; next < addresses.Count && !pads.Contains(addresses[next]); next++)
                if (unwind.CallSites.Any(site => addresses[next] >= site.Start && addresses[next] < site.End))
                    return true;
        }
        return false;
    }

    // The exception a block raises when all it does is call an il2cpp check's helper (lifted as a
    // Throw of the helper's exception type, perhaps followed by the call's impossible return).
    private static string? Raises(Block block)
    {
        string? thrown = null;
        foreach (var instruction in block.Instructions)
        {
            switch (instruction)
            {
                case { OpCode: OpCode.Nop or OpCode.Interrupt }:
                case { OpCode: OpCode.Return } when thrown != null:
                    continue;
                case { OpCode: OpCode.Throw, Operands: [TypeAnalysisContext type] } when thrown == null:
                    thrown = type.FullName;
                    continue;
                default:
                    return null;
            }
        }
        return thrown;
    }

    private enum Relation { Less, LessOrEqual, Greater, GreaterOrEqual, Equal, NotEqual }

    private readonly record struct Term(IOperand Operand, int At);

    private readonly record struct Comparison(Relation Relation, Term Left, Term Right)
    {
        public Comparison Negate() => this with
        {
            Relation = Relation switch
            {
                Relation.Less => Relation.GreaterOrEqual,
                Relation.GreaterOrEqual => Relation.Less,
                Relation.LessOrEqual => Relation.Greater,
                Relation.Greater => Relation.LessOrEqual,
                Relation.Equal => Relation.NotEqual,
                _ => Relation.Equal,
            }
        };
    }

    // The value a local holds at a point of the trace: its last definition before that point (or
    // its value on entry when the trace never defines it), followed through plain copies. A field
    // read is the field of its object's value, valid until the next memory write.
    private readonly record struct Value(object Root, int Definition, object? Field = null, int Epoch = 0);

    // One straight path through the method: the single-predecessor chain before the check's block,
    // the block, then the single-successor chain on the side that does not raise. Values are
    // numbered along it, so out of SSA a local means the same thing at two points exactly when the
    // path does not redefine it between them.
    private sealed class Trace
    {
        private readonly List<Instruction> _code = [];
        private readonly int _branch;
        private readonly HashSet<Instruction> _lengthCalls = [];

        private readonly MethodFacts? _facts;
        private readonly Dictionary<Instruction, string> _guarded;
        private string _exception = "";

        // The access a proven check guards.
        public Instruction? Access { get; private set; }

        public Trace(Block block, Block next, ISILControlFlowGraph cfg, MethodFacts? facts, Dictionary<Instruction, string> guarded)
        {
            _facts = facts;
            _guarded = guarded;
            var before = new List<Block>();
            for (var current = block; before.Count < TraceBlocks && current.Predecessors is [var single]
                                      && single != cfg.EntryBlock && single != block && !before.Contains(single);
                 current = single)
                before.Insert(0, single);
            foreach (var previous in before)
                _code.AddRange(previous.Instructions);
            _code.AddRange(block.Instructions);
            _branch = _code.Count - 1;
            var after = next;
            for (var count = 0; count < TraceBlocks && after != cfg.ExitBlock; count++)
            {
                _code.AddRange(after.Instructions);
                if (after.Successors is not [var following])
                    break;
                after = following;
            }
        }

        // A null check `x == 0` raising, then the first thing the path does dereferences x.
        // A dereference that is a direct instance call comes back as `checkedCall`.
        public bool ProvesNullCheck(bool throwsOnTrue, out Instruction? checkedCall)
        {
            checkedCall = null;
            _exception = NullReference;
            var condition = _code[_branch].Operands[1];
            var at = _branch;
            while (Definition(condition, at) is { } negation && _code[negation] is { OpCode: OpCode.Not, Operands: [_, var inner] })
                (condition, at, throwsOnTrue) = (inner, negation, !throwsOnTrue);
            if (Definition(condition, at) is not { } checkAt
                || _code[checkAt] is not { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, var left, var right] } check
                || (check.OpCode == OpCode.CheckEqual) != throwsOnTrue)
                return false;
            var reference = right is Immediate { Value: 0 } ? left : left is Immediate { Value: 0 } ? right : null;
            if (reference is null or Immediate || ValueOf(reference, checkAt) is not { } checkedValue)
                return false;

            bool Same(IOperand operand, int position) => ValueOf(operand, position) is { } value && value.Equals(checkedValue);
            if (FirstEffect(position => Dereferenced(_code[position], operand => Same(operand, position))) is not { } access)
                return false;
            var instruction = _code[access];
            Access = instruction;
            bool SameHere(IOperand operand) => Same(operand, access);

            if (instruction.IsCall && instruction.Operands[0] is MethodAnalysisContext { IsStatic: false } target)
            {
                var receiver = instruction.OpCode == OpCode.Call ? 2 : 1;
                if (instruction.Operands.Count > receiver && SameHere(instruction.Operands[receiver]))
                {
                    if (target is { Name: not ".ctor", DeclaringType: { IsValueType: false } and not ArrayTypeAnalysisContext })
                        checkedCall = instruction;
                    return true;
                }
            }
            return Read(instruction).Any(operand => Dereferences(operand, SameHere));
        }

        // Whether the instruction dereferences the value `same` names, as an instance call's
        // receiver or in an operand it touches.
        private static bool Dereferenced(Instruction instruction, System.Func<IOperand, bool> same)
            => instruction.IsCall && instruction.Operands[0] is MethodAnalysisContext { IsStatic: false }
               && instruction.Operands.Count > (instruction.OpCode == OpCode.Call ? 2 : 1)
               && same(instruction.Operands[instruction.OpCode == OpCode.Call ? 2 : 1])
               || Read(instruction).Any(operand => Dereferences(operand, same));

        // `index >= length` (unsigned) raising, then the first thing the path does is the element at
        // that index of that length's array and dimension.
        public bool ProvesBoundsCheck(bool throwsOnTrue, HashSet<Instruction> lengthCalls)
        {
            _exception = IndexOutOfRange;
            if (Compare(new Term(_code[_branch].Operands[1], _branch), 0) is not { } condition)
                return false;
            var raised = throwsOnTrue ? condition : condition.Negate();
            var (index, length) = raised.Relation switch
            {
                Relation.GreaterOrEqual => (raised.Left, raised.Right),
                Relation.LessOrEqual => (raised.Right, raised.Left),
                Relation.Equal when raised.Right.Operand is Immediate { Value: 0 } => (raised.Right, raised.Left),
                Relation.Equal when raised.Left.Operand is Immediate { Value: 0 } => (raised.Left, raised.Right),
                // A counter that starts at or above 0 and steps by 1 meets its length before it can
                // pass it, so clang checks it with `cmp len, i; b.eq`.
                Relation.Equal when CountsUp(raised.Right) && LengthOf(raised.Left) != null => (raised.Right, raised.Left),
                Relation.Equal when CountsUp(raised.Left) && LengthOf(raised.Right) != null => (raised.Left, raised.Right),
                _ => (default, default),
            };
            if (index.Operand == null || LengthOf(length) is not { } bound || LengthOf(index) != null)
                return false;

            var checkedIndex = IndexValue(index.Operand, index.At);
            bool Accesses(int position)
            {
                var instruction = _code[position];
                bool SameArray(IOperand array) => ValueOf(array, position) is { } value && value.Equals(bound.Array);
                bool SameIndex(IOperand candidate) => IndexValue(candidate, position) is { } value && value.Equals(checkedIndex);
                if (instruction.IsCall && instruction.Operands[0] is MethodAnalysisContext
                        { DeclaringType: ArrayTypeAnalysisContext grid, Name: "Get" or "Set" or "Address" })
                {
                    var array = instruction.OpCode == OpCode.Call ? 2 : 1;
                    return bound.Dimension < grid.Rank && instruction.Operands.Count > array + 1 + bound.Dimension
                        && SameArray(instruction.Operands[array])
                        && SameIndex(instruction.Operands[array + 1 + bound.Dimension]);
                }
                return bound.Dimension == 0 && Read(instruction).Any(operand => Element(operand) is var (array, at)
                    && SameArray(array) && SameIndex(at));
            }

            if (FirstEffect(Accesses) is not { } access || !Accesses(access))
                return false;
            Access = _code[access];
            lengthCalls.UnionWith(_lengthCalls);
            return true;
        }

        // The operands an instruction touches before its own effect: a call's arguments are loaded
        // before it runs, but the store of its result comes after.
        private static IEnumerable<IOperand> Read(Instruction instruction) => instruction.OpCode switch
        {
            OpCode.Call => instruction.Operands.Skip(2),
            OpCode.CallVoid => instruction.Operands.Skip(1),
            _ => instruction.Operands,
        };

        private static (LocalVariable, IOperand)? Element(IOperand operand) => operand switch
        {
            ArrayAccess access => (access.Array, access.Index),
            ArrayElementFieldReference field => (field.Array, field.Index),
            AddressOf { Target: var target } => Element(target),
            _ => null,
        };

        private static bool Dereferences(IOperand operand, System.Func<IOperand, bool> same) => operand switch
        {
            MemoryOperand { Base: { } address } => same(address),
            FieldReference field => same(field.Local),
            ArrayLength length => same(length.Array),
            ArrayAccess access => same(access.Array),
            ArrayElementFieldReference element => same(element.Array),
            AddressOf { Target: var target } => Dereferences(target, same),
            _ => false,
        };

        // The first instruction past the branch that is the guarded access, or that does anything
        // observable before it.
        private int? FirstEffect(System.Func<int, bool> isAccess)
        {
            for (var i = _branch + 1; i < _code.Count; i++)
                if (isAccess(i) || !Pure(_code[i]) || _guarded.TryGetValue(_code[i], out var raised) && raised != _exception)
                    return i;
            return null;
        }

        // Computes into a local: no store, call or control flow. A load is pure too: the native
        // code reaches it with no check of its own on the way, so it cannot fault there - il2cpp
        // would have guarded it otherwise - and it does not fault in the IL either.
        private static bool Pure(Instruction instruction) => instruction.OpCode switch
        {
            OpCode.Nop or OpCode.Jump => true,
            OpCode.Move or OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.ShiftLeft or OpCode.ShiftRight
                or OpCode.And or OpCode.Or or OpCode.Xor or OpCode.Not or OpCode.Negate or OpCode.SignExtend32
                or OpCode.Convert or (>= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual)
                => instruction.Destination is LocalVariable && instruction.Operands.All(o => o is LocalVariable or Immediate
                    or FieldReference or MemoryOperand or ArrayLength or ArrayAccess or ArrayElementFieldReference
                    or StringLiteral),
            _ => false,
        };

        private static bool WritesMemory(Instruction instruction)
            => instruction.IsCall
               || instruction.OpCode is OpCode.IndirectCall or OpCode.MemoryCopy or OpCode.MemorySet or OpCode.MemoryMove
               || instruction.Destination is { } destination and not LocalVariable;

        private int? Definition(IOperand operand, int at)
        {
            if (operand is not LocalVariable local)
                return null;
            for (var i = at - 1; i >= 0; i--)
                if (ReferenceEquals(_code[i].Destination, local))
                    return i;
            return null;
        }

        private Value? ValueOf(IOperand operand, int at)
        {
            for (var depth = 0; depth < 16; depth++)
            {
                switch (operand)
                {
                    case Immediate immediate:
                        return new Value(immediate.Value, -2);
                    case FieldReference field:
                        return ValueOf(field.Local, at) is { } owner
                            ? new Value(owner, -3, (field.Field, string.Join("/", field.Containers.Select(c => c.Name))), Epoch(at))
                            : null;
                    case ArrayAccess element:
                        return ValueOf(element.Array, at) is { } array && IndexValue(element.Index, at) is { } index
                            ? new Value(array, -4, index, Epoch(at))
                            : null;
                    case MemoryOperand { Base: { } address, Index: null } memory:
                        return ValueOf(address, at) is { } pointer
                            ? new Value(pointer, -5, (memory.Addend, memory.AccessSize), Epoch(at))
                            : null;
                    case LocalVariable local:
                        if (Definition(local, at) is not { } definition)
                            return new Value(local, -1);
                        if (_code[definition] is { OpCode: OpCode.Move, Operands: [_, LocalVariable or Immediate or FieldReference
                                or ArrayAccess or MemoryOperand { Index: null }] } copy)
                        {
                            operand = copy.Operands[1];
                            at = definition;
                            continue;
                        }
                        return new Value(local, definition);
                    default:
                        return null;
                }
            }
            return null;
        }

        private int Epoch(int at)
        {
            var writes = 0;
            for (var i = 0; i < at; i++)
                if (WritesMemory(_code[i]))
                    writes++;
            return writes;
        }

        private Value? IndexValue(IOperand operand, int at)
            => Definition(operand, at) is { } definition && _code[definition] is { OpCode: OpCode.SignExtend32, Operands: [_, var source] }
                ? ValueOf(source, definition)
                : ValueOf(operand, at);

        // The array and dimension whose length an operand holds: `array.Length`, or the GetLength
        // call ArrayRecovery made of a T[,]'s bounds block.
        private (Value Array, int Dimension)? LengthOf(Term term)
        {
            var (operand, at) = term;
            for (var depth = 0; depth < 16; depth++)
            {
                if (operand is ArrayLength length)
                    return ValueOf(length.Array, at) is { } array ? (array, 0) : null;
                if (Definition(operand, at) is not { } definition)
                    return GlobalLengthOf(operand, 0);
                switch (_code[definition])
                {
                    case { OpCode: OpCode.Move, Operands: [_, var source] }:
                        (operand, at) = (source, definition);
                        continue;
                    case { OpCode: OpCode.And, Operands: [_, var masked, Immediate { Value: -1 or 0xFFFFFFFF }] }:
                        (operand, at) = (masked, definition);
                        continue;
                    case { OpCode: OpCode.Call, Operands: [MethodAnalysisContext { Name: "GetLength", DeclaringType.FullName: "System.Array" },
                        _, var array, Immediate dimension, ..] } call when ValueOf(array, definition) is { } owner:
                        _lengthCalls.Add(call);
                        return (owner, (int)dimension.Value);
                    default:
                        return null;
                }
            }
            return null;
        }

        // The length a local holds when the path does not define it: its one definition, made outside
        // any loop, reads the length of an array that holds one value too (a parameter, or another
        // local written once outside any loop) - the same value the path sees on entry.
        private (Value Array, int Dimension)? GlobalLengthOf(IOperand operand, int depth)
        {
            if (operand is ArrayLength { Array: var lengthOf })
                return _facts!.IsStable(lengthOf) ? (new Value(lengthOf, -1), 0) : null;
            if (depth > 8 || operand is not LocalVariable local || _facts!.StableDefinition(local) is not { } definition)
                return null;
            switch (definition)
            {
                case { OpCode: OpCode.Move, Operands: [_, var source] }:
                    return GlobalLengthOf(source, depth + 1);
                case { OpCode: OpCode.And, Operands: [_, var masked, Immediate { Value: -1 or 0xFFFFFFFF }] }:
                    return GlobalLengthOf(masked, depth + 1);
                case { OpCode: OpCode.Call, Operands: [MethodAnalysisContext { Name: "GetLength", DeclaringType.FullName: "System.Array" },
                    _, LocalVariable array, Immediate dimension, ..] } call when _facts!.IsStable(array):
                    _lengthCalls.Add(call);
                    return (new Value(array, -1), (int)dimension.Value);
                default:
                    return null;
            }
        }

        // An index the path does not define, written exactly twice in the method: `i = s` with s >= 0,
        // and `i = i + 1`, directly or through a copy of `i + 1`.
        private bool CountsUp(Term term)
            => ValueOf(term.Operand, term.At) is { Root: LocalVariable counter, Definition: -1 } && _facts!.CountsUp(counter);

        // The comparison a condition local computes, from the lifted flag arithmetic: ARM's C is
        // `!(a < b)` and Z is `(a - b) == 0` after `cmp a, b`, so b.ls is `!C || Z`, b.hs is C;
        // `tst x, #~k; b.eq` with k + 1 a power of two is `x <= k`.
        private Comparison? Compare(Term term, int depth)
        {
            if (depth > 8 || Definition(term.Operand, term.At) is not { } at)
                return null;
            var instruction = _code[at];
            switch (instruction)
            {
                case { OpCode: OpCode.Move, Operands: [_, LocalVariable source] }:
                    return Compare(new Term(source, at), depth + 1);
                case { OpCode: OpCode.Not, Operands: [_, var inner] }:
                    return Compare(new Term(inner, at), depth + 1)?.Negate();
                case { OpCode: OpCode.CheckLess, Operands: [_, var a, var b] }:
                    return new Comparison(Relation.Less, new Term(a, at), new Term(b, at));
                case { OpCode: OpCode.CheckLessOrEqual, Operands: [_, var a, var b] }:
                    return new Comparison(Relation.LessOrEqual, new Term(a, at), new Term(b, at));
                case { OpCode: OpCode.CheckGreater, Operands: [_, var a, var b] }:
                    return new Comparison(Relation.Greater, new Term(a, at), new Term(b, at));
                case { OpCode: OpCode.CheckGreaterOrEqual, Operands: [_, var a, var b] }:
                    return new Comparison(Relation.GreaterOrEqual, new Term(a, at), new Term(b, at));
                case { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, var a, var b] }:
                    var equal = Equality(a, b, at);
                    return instruction.OpCode == OpCode.CheckEqual ? equal : equal.Negate();
                case { OpCode: OpCode.Or or OpCode.And, Operands: [_, var a, var b] }
                    when Compare(new Term(a, at), depth + 1) is { } left && Compare(new Term(b, at), depth + 1) is { } right:
                    return Combine(instruction.OpCode == OpCode.Or, left, right) ?? Combine(instruction.OpCode == OpCode.Or, right, left);
                default:
                    return null;
            }
        }

        private Comparison Equality(IOperand a, IOperand b, int at)
        {
            var (value, zero) = b is Immediate { Value: 0 } ? (a, true) : a is Immediate { Value: 0 } ? (b, true) : (a, false);
            if (zero && Definition(value, at) is { } definition)
            {
                switch (_code[definition])
                {
                    case { OpCode: OpCode.Subtract, Operands: [_, var x, var y] }:
                        return new Comparison(Relation.Equal, new Term(x, definition), new Term(y, definition));
                    case { OpCode: OpCode.And, Operands: [_, var x, Immediate mask] }
                        when (mask.Value >> 32) is 0 or -1 && (~(uint)mask.Value + 1UL) is var bound
                             && bound > 1 && (bound & (bound - 1)) == 0:
                        return new Comparison(Relation.LessOrEqual, new Term(x, definition),
                            new Term(new Immediate((long)(bound - 1)), definition));
                }
            }
            return zero ? new Comparison(Relation.Equal, new Term(value, at), new Term(new Immediate(0), at))
                : new Comparison(Relation.Equal, new Term(a, at), new Term(b, at));
        }

        // `a < b || a == b` is `a <= b`, `a >= b && a != b` is `a > b`, and their mirrors.
        private Comparison? Combine(bool or, Comparison strict, Comparison equality)
        {
            if (equality.Relation != (or ? Relation.Equal : Relation.NotEqual))
                return null;
            var relation = (or, strict.Relation) switch
            {
                (true, Relation.Less) => Relation.LessOrEqual,
                (true, Relation.Greater) => Relation.GreaterOrEqual,
                (false, Relation.GreaterOrEqual) => Relation.Greater,
                (false, Relation.LessOrEqual) => Relation.Less,
                _ => (Relation?)null,
            };
            if (relation == null)
                return null;
            var same = SameTerm(strict.Left, equality.Left) && SameTerm(strict.Right, equality.Right)
                       || SameTerm(strict.Left, equality.Right) && SameTerm(strict.Right, equality.Left);
            return same ? strict with { Relation = relation.Value } : null;
        }

        private bool SameTerm(Term a, Term b)
            => ValueOf(a.Operand, a.At) is { } x && x.Equals(ValueOf(b.Operand, b.At))
               || LengthOf(a) is { } la && LengthOf(b) is { } lb && la.Equals(lb);
    }

    // Whole-method facts about locals, out of SSA: how often each is written, and where.
    private sealed class MethodFacts
    {
        private readonly Dictionary<LocalVariable, List<(Instruction Instruction, Block Block)>> _definitions = [];
        private readonly Dictionary<Block, bool> _cyclic = [];

        public MethodFacts(ISILControlFlowGraph cfg)
        {
            foreach (var block in cfg.Blocks)
            foreach (var instruction in block.Instructions)
                if (instruction.Destination is LocalVariable local)
                    (_definitions.TryGetValue(local, out var list) ? list : _definitions[local] = []).Add((instruction, block));
        }

        // Never written (a parameter), or written once in a block no loop runs again.
        public bool IsStable(LocalVariable local)
            => !_definitions.TryGetValue(local, out var definitions) || definitions is [var only] && !OnCycle(only.Block);

        public Instruction? StableDefinition(LocalVariable local)
            => _definitions.TryGetValue(local, out var definitions) && definitions is [var only] && !OnCycle(only.Block)
                ? only.Instruction
                : null;

        public bool CountsUp(LocalVariable counter)
        {
            if (!_definitions.TryGetValue(counter, out var definitions) || definitions.Count != 2)
                return false;
            Instruction? Single(LocalVariable local)
                => _definitions.TryGetValue(local, out var list) && list is [var only] ? only.Instruction : null;
            return definitions.Any(d => d.Instruction is { OpCode: OpCode.Move, Operands: [_, Immediate { Value: >= 0 }] })
                   && definitions.Any(d => (d.Instruction is { OpCode: OpCode.Move, Operands: [_, LocalVariable copy] } ? Single(copy) : d.Instruction)
                       is { OpCode: OpCode.Add, Operands: [_, LocalVariable from, Immediate { Value: 1 }] }
                       && ReferenceEquals(from, counter));
        }

        private bool OnCycle(Block block)
        {
            if (_cyclic.TryGetValue(block, out var cyclic))
                return cyclic;
            var seen = new HashSet<Block>();
            var work = new Stack<Block>(block.Successors);
            while (work.TryPop(out var current))
            {
                if (current == block)
                    return _cyclic[block] = true;
                if (seen.Add(current))
                    foreach (var successor in current.Successors)
                        work.Push(successor);
            }
            return _cyclic[block] = false;
        }
    }

    private static HashSet<Instruction> NullCheckedCalls(MethodAnalysisContext method)
    {
        if (method.GetExtraData<HashSet<Instruction>>(NullCheckedCallsKey) is not { } calls)
            method.PutExtraData(NullCheckedCallsKey, calls = []);
        return calls;
    }
}
