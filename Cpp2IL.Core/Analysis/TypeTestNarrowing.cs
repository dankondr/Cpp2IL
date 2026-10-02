using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// `x is K k ? k.F : ...` tests x's class and then reads K's fields straight off x's register: the
/// cast result is the same pointer, so clang never touches it again. x keeps its static (base)
/// type, so a field K declares finds no field there and the read stays an unmanaged load. Where a
/// branch on the type test proves x is a K - the edge where the isinst result is non-null, or
/// where x's class is a sealed K - every read of a K field off x in the blocks that edge
/// dominates goes through the cast result instead, typed K.
/// </summary>
internal static class TypeTestNarrowing
{
    public static void Run(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var definitions = new Dictionary<LocalVariable, Instruction?>(ReferenceEqualityComparer.Instance);
        foreach (var instruction in cfg.Instructions)
            if (instruction.Destination is LocalVariable local)
                definitions[local] = definitions.ContainsKey(local) ? null : instruction;

        DominatorInfo? dominators = null;
        foreach (var block in cfg.Blocks.ToList())
        {
            if (block.Instructions.Count == 0
                || block.Instructions[^1] is not { OpCode: OpCode.ConditionalJump, Operands: [Block taken, LocalVariable condition] }
                || block.Successors.Count != 2
                || block.Successors.FirstOrDefault(successor => successor != taken) is not { } notTaken
                || !TryMatchTest(condition, definitions, out var test, out var instanceWhenTrue))
                continue;

            var instanceEdge = instanceWhenTrue ? taken : notTaken;
            if (instanceEdge.Predecessors.Count != 1 || instanceEdge == cfg.ExitBlock)
                continue;

            dominators ??= new DominatorInfo(cfg);
            // A class compare reads x's class pointer: only a path that proved x non-null reaches
            // it (IsInstSealed tests null first), and only there is it the same as isinst.
            if (test.ExactClass && !ProvenNonNull(cfg, dominators, block, test.Value, definitions))
                continue;
            var reads = SubtypeOnlyReads(method, dominators, instanceEdge, test.Value, test.Type, definitions);
            if (reads.Count == 0)
                continue;

            // The test is often recognized only once field resolution has run, so the read
            // becomes the field here.
            var narrowed = test.CastResult ?? HoistCast(method, test, definitions);
            foreach (var (instruction, operandIndex, memory, path) in reads)
                instruction.SetOperand(operandIndex, new FieldReference(
                    test.Type is GenericInstanceTypeAnalysisContext
                        ? MetadataResolver.BindResolvedFieldLeaf(test.Type, path.Containers, path.Field)
                        : path.Field,
                    narrowed, (int)memory.Addend, path.Containers, memory.AccessSize));
        }
    }

    // A test of x against K: the instruction that computes it, the operand slot holding the
    // isinst (null when the cast already has a local), and what it proves.
    private sealed record Test(Instruction Compare, LocalVariable Value, TypeAnalysisContext Type,
        LocalVariable? CastResult, int CastOperand, bool ExactClass);

    // The branch condition, through negations, is `isinst<K>(x) != null` (or `== null`), the
    // isinst sitting inline or in a local; or `class(x) == K` for a sealed K.
    private static bool TryMatchTest(LocalVariable condition, Dictionary<LocalVariable, Instruction?> definitions,
        out Test test, out bool instanceWhenTrue)
    {
        test = null!;
        instanceWhenTrue = false;
        var negated = false;
        IOperand current = condition;
        for (var depth = 0; depth < 6 && current is LocalVariable local; depth++)
        {
            if (Definition(local, definitions) is not { } definition)
                return false;

            switch (definition)
            {
                case { OpCode: OpCode.Not, Operands: [_, var inner] }:
                    negated = !negated;
                    current = inner;
                    continue;
                case { OpCode: OpCode.Move, Operands: [_, LocalVariable copied] }:
                    current = copied;
                    continue;
                case { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, var left, var right] }:
                    var equal = definition.OpCode == OpCode.CheckEqual;
                    for (var side = 1; side <= 2; side++)
                    {
                        var tested = side == 1 ? left : right;
                        var other = side == 1 ? right : left;
                        if (other is Immediate { Value: 0 } && IsInstOf(tested, definitions) is { } cast)
                        {
                            // `isinst == null` is true on the not-an-instance edge.
                            instanceWhenTrue = !equal != negated;
                            test = new Test(definition, cast.Value, cast.Type, tested as LocalVariable, side, false);
                            return Narrowable(test);
                        }

                        if (ClassOf(tested, definitions) is { } value && SealedClass(other, definitions) is { } sealedClass)
                        {
                            instanceWhenTrue = equal != negated;
                            test = new Test(definition, value, sealedClass, null, side, true);
                            return Narrowable(test);
                        }
                    }
                    return false;
            }

            return false;
        }

        return false;
    }

    // A shared-generic K (List<T> tested inside Foo<T>) has no closed field to bind: leave it.
    private static bool Narrowable(Test test) =>
        test.Type is { IsValueType: false, IsInterface: false } and not GenericParameterTypeAnalysisContext
        && !Open(test.Type)
        && test.Value.Type is { IsValueType: false } valueType
        && !ReferenceEquals(valueType, test.Type)
        && test.Type.IsAssignableTo(valueType);

    private static bool Open(TypeAnalysisContext type) => type switch
    {
        GenericParameterTypeAnalysisContext => true,
        GenericInstanceTypeAnalysisContext instance => instance.GenericArguments.Any(Open),
        _ => type.GenericParameters.Count > 0,
    };

    private static Instruction? Definition(LocalVariable local, Dictionary<LocalVariable, Instruction?> definitions) =>
        definitions.TryGetValue(local, out var definition) ? definition : null;

    private static ReferenceCast? IsInstOf(IOperand operand, Dictionary<LocalVariable, Instruction?> definitions) =>
        operand switch
        {
            ReferenceCast { NullOnFailure: true } cast => cast,
            LocalVariable local when Definition(local, definitions) is
                { OpCode: OpCode.Move, Operands: [_, ReferenceCast { NullOnFailure: true } held] } => held,
            _ => null,
        };

    // `[x + 0]`, the class pointer of an object x, loaded inline or into a local.
    private static LocalVariable? ClassOf(IOperand operand, Dictionary<LocalVariable, Instruction?> definitions) =>
        operand switch
        {
            MemoryOperand { Base: LocalVariable value, Index: null, Scale: 0, Addend: 0 } => value,
            LocalVariable local when Definition(local, definitions) is
                { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: LocalVariable value, Index: null, Scale: 0, Addend: 0 }] } => value,
            _ => null,
        };

    // A class literal for a sealed reference type: only instances of exactly that class have it.
    private static TypeAnalysisContext? SealedClass(IOperand operand, Dictionary<LocalVariable, Instruction?> definitions)
    {
        var type = operand switch
        {
            RuntimeClassTypeAnalysisContext runtimeClass => runtimeClass.RepresentedType,
            TypeAnalysisContext literal => literal,
            LocalVariable local when Definition(local, definitions) is { OpCode: OpCode.Move, Operands: [_, var source] }
                && source is not LocalVariable => SealedClass(source, definitions),
            _ => null,
        };
        return type is { IsSealed: true, IsValueType: false } ? type : null;
    }

    // Reads off x that only K declares, in the blocks the instance edge dominates. x must be one
    // value throughout: a parameter or a single definition.
    private static List<(Instruction Instruction, int OperandIndex, MemoryOperand Memory,
        (FieldAnalysisContext Field, IReadOnlyList<FieldAnalysisContext> Containers) Path)> SubtypeOnlyReads(
        MethodAnalysisContext method, DominatorInfo dominators, Block instanceEdge, LocalVariable value,
        TypeAnalysisContext type, Dictionary<LocalVariable, Instruction?> definitions)
    {
        var reads = new List<(Instruction, int, MemoryOperand, (FieldAnalysisContext, IReadOnlyList<FieldAnalysisContext>))>();
        if (definitions.TryGetValue(value, out var definition) && definition == null)
            return reads;

        foreach (var block in method.ControlFlowGraph!.Blocks.Where(block => dominators.Dominates(instanceEdge, block)))
            foreach (var instruction in block.Instructions)
                for (var i = 0; i < instruction.Operands.Count; i++)
                    if (instruction.Operands[i] is MemoryOperand { Base: LocalVariable owner, Index: null, Scale: 0, Addend: > 0 } memory
                        && ReferenceEquals(owner, value)
                        && MetadataResolver.FindInstanceFieldPathAtOffset(value.Type!, memory.Addend, memory.AccessSize) == null
                        && MetadataResolver.FindInstanceFieldPathAtOffset(type, memory.Addend, memory.AccessSize) is { } path
                        && !MetadataResolver.MemberPathUnspellable(path, method,
                            store: i == 0 && instruction.OpCode == OpCode.Move, addressed: false))
                        reads.Add((instruction, i, memory, path));
        return reads;
    }

    // Some block dominating `at` branches on x == null and only its non-null edge leads on to `at`.
    private static bool ProvenNonNull(ISILControlFlowGraph cfg, DominatorInfo dominators, Block at,
        LocalVariable value, Dictionary<LocalVariable, Instruction?> definitions)
    {
        for (var dominator = dominators.ImmediateDominators.GetValueOrDefault(at); dominator != null;
             dominator = dominators.ImmediateDominators.GetValueOrDefault(dominator))
        {
            if (dominator.Instructions.Count == 0
                || dominator.Instructions[^1] is not { OpCode: OpCode.ConditionalJump, Operands: [Block taken, LocalVariable condition] }
                || dominator.Successors.Count != 2
                || dominator.Successors.FirstOrDefault(successor => successor != taken) is not { } notTaken
                || NullTest(condition, value, definitions) is not { } nullWhenTrue)
                continue;

            var nonNullEdge = nullWhenTrue ? notTaken : taken;
            if (nonNullEdge.Predecessors.Count == 1 && dominators.Dominates(nonNullEdge, at))
                return true;
        }

        return false;
    }

    // Whether the condition, through negations, is true when x is null (null when it does not test x).
    private static bool? NullTest(LocalVariable condition, LocalVariable value, Dictionary<LocalVariable, Instruction?> definitions)
    {
        var negated = false;
        IOperand current = condition;
        for (var depth = 0; depth < 6 && current is LocalVariable local; depth++)
        {
            switch (Definition(local, definitions))
            {
                case { OpCode: OpCode.Not, Operands: [_, var inner] }:
                    negated = !negated;
                    current = inner;
                    continue;
                case { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual, Operands: [_, var left, var right] } check
                    when left is Immediate { Value: 0 } && ReferenceEquals(right, value)
                         || right is Immediate { Value: 0 } && ReferenceEquals(left, value):
                    return (check.OpCode == OpCode.CheckEqual) != negated;
            }

            return null;
        }

        return null;
    }

    // An inline isinst becomes `k = isinst<K>(x)`, tested in its place - the local the source
    // pattern `x is K k` names. A sealed class compare becomes the same isinst: for a non-null x
    // (the compare reads x's class, so the path already proved it) both mean "x is a K".
    private static LocalVariable HoistCast(MethodAnalysisContext method, Test test,
        Dictionary<LocalVariable, Instruction?> definitions)
    {
        var name = $"is{test.Type.Name}_{method.Locals.Count}";
        var narrowed = new LocalVariable(name, new Register(null, name), test.Type);
        method.Locals.Add(narrowed);
        var hoisted = new Instruction(-1, OpCode.Move, narrowed, new ReferenceCast(test.Value, test.Type, nullOnFailure: true));
        // The compare can sit in an earlier block than the branch that tests it.
        var home = method.ControlFlowGraph!.Blocks.First(block => block.Instructions.Contains(test.Compare));
        home.Instructions.Insert(home.Instructions.IndexOf(test.Compare), hoisted);
        definitions[narrowed] = hoisted;

        if (test.ExactClass)
        {
            // class(x) == K  ->  isinst<K>(x) != null, and != -> ==.
            test.Compare.OpCode = test.Compare.OpCode == OpCode.CheckEqual ? OpCode.CheckNotEqual : OpCode.CheckEqual;
            test.Compare.SetOperands(test.Compare.Operands[0], narrowed, new Immediate(0));
        }
        else
            test.Compare.SetOperand(test.CastOperand, narrowed);
        return narrowed;
    }
}
