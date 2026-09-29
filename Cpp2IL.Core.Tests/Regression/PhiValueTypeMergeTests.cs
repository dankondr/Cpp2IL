using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: typed local -> mismatched slot (castle-recovery#143). When one
// register is redefined into differently-typed locals across a control-flow join,
// SsaForm.Remove inserts an edge copy per predecessor. A copy between value types
// the CLR cannot convert - a struct and a scalar that is not its lane, Nullable<T>
// and T, two unrelated structs - is a bit-pattern merge: emitting it produced a
// `No legal conversion` diagnostic plus a synthetic default identical to the value
// the slot already held. The unrepresentable edge copy is not inserted; edges with
// a legal conversion (numeric width, float/int, lane field) still copy.
public class PhiValueTypeMergeTests
{
    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    // A value type with no Single view: two public Int32 fields at offsets 0/4, so
    // nothing lane-folds it into a Single or scalar slot.
    private static TypeAnalysisContext Pair(ApplicationAnalysisContext app)
    {
        var pair = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Pair",
            app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        pair.Fields.Add(new InjectedFieldAnalysisContext("a", app.SystemTypes.SystemInt32Type,
            R.FieldAttributes.Public, pair, 0));
        pair.Fields.Add(new InjectedFieldAnalysisContext("b", app.SystemTypes.SystemInt32Type,
            R.FieldAttributes.Public, pair, 4));
        return pair;
    }

    // A value type shaped like a vector: a public Single `x` at offset 0 is the
    // register's low lane, so a Single view of it stays legal.
    private static TypeAnalysisContext Vector(ApplicationAnalysisContext app)
    {
        var vector = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Vec2",
            app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        vector.Fields.Add(new InjectedFieldAnalysisContext("x", app.SystemTypes.SystemSingleType,
            R.FieldAttributes.Public, vector, 0));
        vector.Fields.Add(new InjectedFieldAnalysisContext("y", app.SystemTypes.SystemSingleType,
            R.FieldAttributes.Public, vector, 4));
        return vector;
    }

    private static ISILControlFlowGraph JoinedGraph(LocalVariable destination, params LocalVariable[] sources)
    {
        var instructions = new List<Instruction>
        {
            new(0, OpCode.ConditionalJump, new Immediate(3), new Register(null, "cond")),
            new(1, OpCode.Nop),
            new(2, OpCode.Jump, new Immediate(4)),
            new(3, OpCode.Nop),
            new(4, OpCode.Return),
        };
        foreach (var instruction in instructions)
            if (instruction.OpCode is OpCode.Jump or OpCode.ConditionalJump)
                instruction.SetOperand(0, instructions[(int)((Immediate)instruction.Operands[0]).Value]);

        var graph = new ISILControlFlowGraph(instructions);
        var join = graph.Blocks.First(b => b.Instructions.Any(i => i.OpCode == OpCode.Return));
        join.Instructions.Insert(0, new Instruction(-1, OpCode.Phi,
            [destination, .. sources]));
        return graph;
    }

    private static List<Instruction> RemovedCopies(ISILControlFlowGraph graph)
    {
        var method = new InjectedMethodAnalysisContext(App.SystemTypes.SystemObjectType, "Join",
            App.SystemTypes.SystemVoidType, R.MethodAttributes.Static, [])
        {
            ControlFlowGraph = graph,
        };

        SsaForm.Remove(method);

        return graph.Instructions.Where(i => i.OpCode == OpCode.Move).ToList();
    }

    [Test]
    public void PhiEdgeMergingUnconvertibleValueTypesDropsOnlyTheIllegalCopy()
    {
        var app = App;
        var pair = Pair(app);
        var incompatible = new LocalVariable("incompatible", new Register(null, "X0", 1), pair);
        var compatible = new LocalVariable("compatible", new Register(null, "X0", 2), app.SystemTypes.SystemSingleType);
        var destination = new LocalVariable("destination", new Register(null, "X0", 3), app.SystemTypes.SystemSingleType);

        var copies = RemovedCopies(JoinedGraph(destination, incompatible, compatible));

        Assert.Multiple(() =>
        {
            Assert.That(copies.Any(copy => ReferenceEquals(copy.Operands[1], compatible)), Is.True);
            Assert.That(copies.Any(copy => ReferenceEquals(copy.Operands[1], incompatible)), Is.False);
        });
    }

    [Test]
    public void PhiEdgeWithNumericConversionStillCopies()
    {
        var app = App;
        var wide = new LocalVariable("wide", new Register(null, "X1", 1), app.SystemTypes.SystemInt64Type);
        var narrow = new LocalVariable("narrow", new Register(null, "X1", 2), app.SystemTypes.SystemInt32Type);
        var destination = new LocalVariable("destination", new Register(null, "X1", 3), app.SystemTypes.SystemInt32Type);

        var copies = RemovedCopies(JoinedGraph(destination, wide, narrow));

        Assert.Multiple(() =>
        {
            Assert.That(copies.Any(copy => ReferenceEquals(copy.Operands[1], wide)), Is.True);
            Assert.That(copies.Any(copy => ReferenceEquals(copy.Operands[1], narrow)), Is.True);
        });
    }

    [Test]
    public void PhiEdgeWithLaneViewStillCopies()
    {
        var app = App;
        var vector = Vector(app);
        var aggregate = new LocalVariable("aggregate", new Register(null, "V2", 1), vector);
        var lane = new LocalVariable("lane", new Register(null, "V2", 2), app.SystemTypes.SystemSingleType);
        var destination = new LocalVariable("destination", new Register(null, "V2", 3), app.SystemTypes.SystemSingleType);

        var copies = RemovedCopies(JoinedGraph(destination, aggregate, lane));

        Assert.Multiple(() =>
        {
            Assert.That(copies.Any(copy => ReferenceEquals(copy.Operands[1], aggregate)), Is.True);
            Assert.That(copies.Any(copy => ReferenceEquals(copy.Operands[1], lane)), Is.True);
        });
    }
}
