using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.NestedFieldPathLoadTests;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// `u is Ranged r ? r.Range : 1f` (corpus il2cpp-type-test ArcherPattern.RangeOf): clang reads
// Range straight off u's register once the inlined hierarchy test passed, and u is typed Unit,
// which has no field at +0x14. On the edge where the test passed the read is Ranged.Range.
public class TypeTestNarrowingTests
{
    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    // Unit { int Hp @0x10 } <- Ranged { float Range @0x14 } <- sealed Archer { int Arrows @0x18 }
    private static (InjectedTypeAnalysisContext Unit, InjectedTypeAnalysisContext Ranged, InjectedTypeAnalysisContext Archer) Units()
    {
        var unit = InjectClass(App, "Unit");
        InjectField("Hp", App.SystemTypes.SystemInt32Type, unit, 0x10);
        var ranged = new InjectedTypeAnalysisContext(App.AssembliesByName["mscorlib"], "Tests", "Ranged", unit,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        InjectField("Range", App.SystemTypes.SystemSingleType, ranged, 0x14);
        var archer = new InjectedTypeAnalysisContext(App.AssembliesByName["mscorlib"], "Tests", "Archer", ranged,
            R.TypeAttributes.Public | R.TypeAttributes.Class | R.TypeAttributes.Sealed);
        InjectField("Arrows", App.SystemTypes.SystemInt32Type, archer, 0x18);
        return (unit, ranged, archer);
    }

    private static InjectedMethodAnalysisContext Method(ISILControlFlowGraph graph) =>
        new(App.SystemTypes.SystemObjectType, "Fixture", App.SystemTypes.SystemSingleType,
            R.MethodAttributes.Static, [])
        {
            ControlFlowGraph = graph,
            Locals = [],
        };

    [Test]
    public void SubclassFieldReadOnThePassingEdgeGoesThroughTheIsInst()
    {
        var (unit, ranged, _) = Units();
        var u = Local("u", unit);
        var miss = Local("miss");
        var range = Local("range");
        var missed = new Instruction(4, OpCode.Return, new Immediate(0));
        var read = new Instruction(2, OpCode.Move, range, new MemoryOperand(u, null, 0x14, 0, 4));
        var missRead = new Instruction(5, OpCode.Move, Local("missRange"), new MemoryOperand(u, null, 0x14, 0, 4));
        var graph = new ISILControlFlowGraph(
        [
            new(0, OpCode.CheckEqual, miss, new ReferenceCast(u, ranged, nullOnFailure: true), new Immediate(0)),
            new(1, OpCode.ConditionalJump, missRead, miss),
            read,
            new(3, OpCode.Return, range),
            missRead,
            missed,
        ]);

        TypeTestNarrowing.Run(Method(graph));

        Assert.Multiple(() =>
        {
            Assert.That(read.Operands[1], Is.InstanceOf<FieldReference>());
            var field = (FieldReference)read.Operands[1];
            Assert.That(field.Field.Name, Is.EqualTo("Range"));
            Assert.That(field.Local.Type, Is.SameAs(ranged));
            Assert.That(graph.Instructions.Any(i => i.Operands.Contains(field.Local) && i.OpCode == OpCode.CheckEqual), Is.True,
                "the test reads the same isinst local the field read goes through");
            Assert.That(missRead.Operands[1], Is.InstanceOf<MemoryOperand>(), "the failing edge proves nothing");
        });
    }

    // `u is Archer a ? a.Arrows : 0` with a sealed Archer: IsInstSealed is a null test then a class
    // compare, and only the compare's equal edge proves u is an Archer.
    [Test]
    public void SealedClassCompareAfterANullTestNarrowsLikeIsInst()
    {
        var (unit, _, archer) = Units();
        var u = Local("u", unit);
        var isNull = Local("isNull");
        var klass = Local("klass");
        var same = Local("same");
        var arrows = Local("arrows");
        var miss = new Instruction(7, OpCode.Return, new Immediate(0));
        var hit = new Instruction(5, OpCode.Move, arrows, new MemoryOperand(u, null, 0x18, 0, 4));
        var graph = new ISILControlFlowGraph(
        [
            new(0, OpCode.CheckEqual, isNull, u, new Immediate(0)),
            new(1, OpCode.ConditionalJump, miss, isNull),
            new(2, OpCode.Move, klass, new MemoryOperand(u, null, 0, 0, 8)),
            new(3, OpCode.CheckEqual, same, klass, archer),
            new(4, OpCode.ConditionalJump, hit, same),
            new(8, OpCode.Jump, miss),
            hit,
            new(6, OpCode.Return, arrows),
            miss,
        ]);

        TypeTestNarrowing.Run(Method(graph));

        Assert.That(hit.Operands[1], Is.InstanceOf<FieldReference>());
        Assert.That(((FieldReference)hit.Operands[1]).Field.Name, Is.EqualTo("Arrows"));
    }

    // Without the null test the class compare is not IsInstSealed's: leave it alone.
    [Test]
    public void SealedClassCompareWithoutANullTestIsKept()
    {
        var (unit, _, archer) = Units();
        var u = Local("u", unit);
        var klass = Local("klass");
        var same = Local("same");
        var miss = new Instruction(5, OpCode.Return, new Immediate(0));
        var hit = new Instruction(3, OpCode.Move, Local("arrows"), new MemoryOperand(u, null, 0x18, 0, 4));
        var graph = new ISILControlFlowGraph(
        [
            new(0, OpCode.Move, klass, new MemoryOperand(u, null, 0, 0, 8)),
            new(1, OpCode.CheckEqual, same, klass, archer),
            new(2, OpCode.ConditionalJump, hit, same),
            new(6, OpCode.Jump, miss),
            hit,
            new(4, OpCode.Return, hit.Operands[0]),
            miss,
        ]);

        TypeTestNarrowing.Run(Method(graph));

        Assert.That(hit.Operands[1], Is.InstanceOf<MemoryOperand>());
    }
}
