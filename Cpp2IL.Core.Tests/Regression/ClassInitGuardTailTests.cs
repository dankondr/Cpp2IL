using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Regression;

// `if (!K->cctor_finished) il2cpp_runtime_class_init(K);` after clang has moved code around it:
// the code after the guard copied into both arms (Countdown::get_IsOver), the flag loaded once
// and tested by every copy of the guard (StorePurchaseBehaviour::OnPurchaseFailure), a null
// recheck in the init arm (VoodooLive::set_UseCacheOnly), and the init arm running into a reload
// shared with another path (DeviceUtils::GetLocale). cctor_finished is +0xE0 in the 2019 test game.
public class ClassInitGuardTailTests
{
    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static LocalVariable Local(string name) => new(name, new Register(null, name));

    private static TypeAnalysisContext Klass => App.AssembliesByName["mscorlib"].GetTypeByFullName("System.IO.MemoryStream")!;

    private static Instruction ClassInit(int index, LocalVariable klass) =>
        new(index, OpCode.Call, new StringLiteral("il2cpp_codegen_runtime_class_init"), Local("initResult"), klass);

    private static void Run(ISILControlFlowGraph graph)
    {
        var method = new InjectedMethodAnalysisContext(App.SystemTypes.SystemObjectType, "Fixture",
            App.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [])
        {
            ControlFlowGraph = graph,
        };
        MetadataInitGuardRemover.Run(graph, 0x135, method);
    }

    private static bool ReadsInitialisedFlag(ISILControlFlowGraph graph) =>
        graph.Instructions.Any(instruction => instruction.Operands.Any(operand => operand is MemoryOperand { Addend: 0xE0 }));

    // if (!K->cctor_finished) init(K); return x == 0 ? 1 : 0; - the branch copied into both arms,
    // the init arm testing it with the opposite polarity after reloading K.
    private static ISILControlFlowGraph DuplicatedBranch(bool initArmStores)
    {
        var klass = Local("klass");
        var flag = Local("flag");
        var clear = Local("clear");
        var x = Local("x");
        var skipTest = Local("skipTest");
        var initTest = Local("initTest");
        var initNegated = Local("initNegated");
        var init = ClassInit(7, klass);
        var yes = new Instruction(13, OpCode.Return, new Immediate(1));
        var no = new Instruction(14, OpCode.Return, new Immediate(0));
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, klass, Klass),
            new(1, OpCode.Move, flag, new MemoryOperand(klass, null, 0xE0, 0)),
            new(2, OpCode.CheckEqual, clear, flag, new Immediate(0)),
            new(3, OpCode.ConditionalJump, init, clear),
            new(4, OpCode.CheckEqual, skipTest, x, new Immediate(0)),
            new(5, OpCode.ConditionalJump, yes, skipTest),
            new(6, OpCode.Jump, no),
            init,
            new(8, OpCode.Move, Local("reloaded"), Klass),
            new(9, OpCode.CheckEqual, initTest, x, new Immediate(0)),
            new(10, OpCode.Not, initNegated, initTest),
            new(11, OpCode.ConditionalJump, no, initNegated),
            new(12, OpCode.Jump, yes),
            yes,
            no,
        };
        if (initArmStores)
            instructions.Insert(9, new Instruction(15, OpCode.Move, new MemoryOperand(x, null, 8, 0), new Immediate(1)));
        return new ISILControlFlowGraph(instructions);
    }

    [Test]
    public void GuardWhoseTailWasCopiedIntoBothArmsKeepsOneCopy()
    {
        var graph = DuplicatedBranch(initArmStores: false);

        Run(graph);

        Assert.Multiple(() =>
        {
            Assert.That(ReadsInitialisedFlag(graph), Is.False);
            Assert.That(graph.Instructions.Any(instruction => instruction.OpCode == OpCode.Not), Is.False,
                "the init arm's copy of the branch is gone");
            Assert.That(graph.Instructions.Count(instruction => instruction.OpCode == OpCode.ConditionalJump), Is.EqualTo(1));
        });
    }

    [Test]
    public void GuardWhoseArmsDoDifferentThingsIsKept()
    {
        var graph = DuplicatedBranch(initArmStores: true);

        Run(graph);

        Assert.That(ReadsInitialisedFlag(graph), Is.True);
    }

    // switch (selector) { case A: ...; case B: ... } Localization.Get(key): the guard copied into
    // each case, every copy testing one flag load hoisted above the switch, one shared init call.
    [Test]
    public void GuardCopiesTestingAHoistedFlagLoadAreExcisedTogether()
    {
        var klass = Local("klass");
        var flag = Local("flag");
        var selector = Local("selector");
        var isA = Local("isA");
        var setA = Local("setA");
        var setB = Local("setB");
        var caseB = new Instruction(8, OpCode.CheckNotEqual, setB, flag, new Immediate(0));
        var trampoline = ClassInit(10, klass);
        var merge = new Instruction(12, OpCode.Return);
        var graph = new ISILControlFlowGraph(
        [
            new(0, OpCode.Move, klass, Klass),
            new(1, OpCode.Move, flag, new MemoryOperand(klass, null, 0xE0, 0)),
            new(2, OpCode.CheckEqual, isA, selector, new Immediate(0)),
            new(3, OpCode.ConditionalJump, caseB, isA),
            new(4, OpCode.Move, Local("key"), new StringLiteral("a")),
            new(5, OpCode.CheckNotEqual, setA, flag, new Immediate(0)),
            new(6, OpCode.ConditionalJump, merge, setA),
            new(7, OpCode.Jump, trampoline),
            caseB,
            new(9, OpCode.ConditionalJump, merge, setB),
            trampoline,
            new(11, OpCode.Jump, merge),
            merge,
        ]);

        Run(graph);

        Assert.That(ReadsInitialisedFlag(graph), Is.False);
    }

    // The init arm reloads the static it is about to dereference and null-checks the reload into
    // the NullReferenceException tail it shares with an earlier check (which merges the registers
    // of both in a phi); the skip arm already holds the checked value.
    [Test]
    public void InitArmWithANullRecheckIntoASharedThrowTailIsExcised()
    {
        var klass = Local("klass");
        var statics = Local("statics");
        var held = Local("held");
        var heldNull = Local("heldNull");
        var flag = Local("flag");
        var set = Local("set");
        var reloaded = Local("reloaded");
        var isNull = Local("isNull");
        var target = Local("target");
        var failed = Local("failed");
        var merge = new Instruction(13, OpCode.Phi, target);
        var fail = new Instruction(16, OpCode.Phi, failed);
        var graph = new ISILControlFlowGraph(
        [
            new(0, OpCode.Move, klass, Klass),
            new(1, OpCode.Move, statics, new MemoryOperand(klass, null, 0xB8, 0)),
            new(2, OpCode.Move, held, new MemoryOperand(statics, null, 8, 0)),
            new(3, OpCode.CheckEqual, heldNull, held, new Immediate(0)),
            new(4, OpCode.ConditionalJump, fail, heldNull),
            new(5, OpCode.Move, flag, new MemoryOperand(klass, null, 0xE0, 0)),
            new(6, OpCode.CheckNotEqual, set, flag, new Immediate(0)),
            new(7, OpCode.ConditionalJump, merge, set),
            ClassInit(8, klass),
            new(9, OpCode.Move, reloaded, new MemoryOperand(statics, null, 8, 0)),
            new(10, OpCode.CheckEqual, isNull, reloaded, new Immediate(0)),
            new(11, OpCode.ConditionalJump, fail, isNull),
            new(12, OpCode.Jump, merge),
            merge,
            new(14, OpCode.Move, new MemoryOperand(target, null, 0x10, 0), new Immediate(1)),
            new(15, OpCode.Return),
            fail,
            new(17, OpCode.Throw, App.AssembliesByName["mscorlib"].GetTypeByFullName("System.NullReferenceException")!),
            new(18, OpCode.Return),
        ]);
        var mergeBlock = graph.Blocks.Single(block => block.Instructions.Contains(merge));
        var failBlock = graph.Blocks.Single(block => block.Instructions.Contains(fail));
        var guardBlock = graph.Blocks.Single(block => block.Instructions.Any(i => i.Index == 7));
        var entryBlock = graph.Blocks.Single(block => block.Instructions.Any(i => i.Index == 4));
        merge.SetOperands([target, ..mergeBlock.Predecessors.Select(IOperand (p) => p == guardBlock ? held : reloaded)]);
        fail.SetOperands([failed, ..failBlock.Predecessors.Select(IOperand (p) => p == entryBlock ? heldNull : isNull)]);

        Run(graph);

        Assert.Multiple(() =>
        {
            Assert.That(ReadsInitialisedFlag(graph), Is.False);
            Assert.That(failBlock.Predecessors, Has.Count.EqualTo(1), "only the earlier check still reaches the throw");
            Assert.That(fail.OpCode != OpCode.Phi || fail.Operands.Count == 2, Is.True, "the throw tail's phi lost the excised edge");
        });
    }

    // if (s_value == null) s_value = Compute(); return s_value; - the init arm runs into the
    // statics reload that the compute path also uses, the skip arm returns the value it holds.
    [Test]
    public void InitArmRunningIntoASharedReloadIsExcised()
    {
        var klass = Local("klass");
        var statics = Local("statics");
        var value = Local("value");
        var missing = Local("missing");
        var flag = Local("flag");
        var set = Local("set");
        var reloadedKlass = Local("reloadedKlass");
        var reloadedStatics = Local("reloadedStatics");
        var merged = Local("merged");
        var result = Local("result");
        var compute = new Instruction(10, OpCode.CallVoid, new Immediate(0x1234), statics);
        var tail = new Instruction(11, OpCode.Move, reloadedKlass, Klass);
        var phi = new Instruction(13, OpCode.Phi, merged);
        var graph = new ISILControlFlowGraph(
        [
            new(0, OpCode.Move, klass, Klass),
            new(1, OpCode.Move, statics, new MemoryOperand(klass, null, 0xB8, 0)),
            new(2, OpCode.Move, value, new MemoryOperand(statics, null, 0x20, 0)),
            new(3, OpCode.CheckEqual, missing, value, new Immediate(0)),
            new(4, OpCode.ConditionalJump, compute, missing),
            new(5, OpCode.Move, flag, new MemoryOperand(klass, null, 0xE0, 0)),
            new(6, OpCode.CheckNotEqual, set, flag, new Immediate(0)),
            new(7, OpCode.ConditionalJump, phi, set),
            ClassInit(8, klass),
            new(9, OpCode.Jump, tail),
            compute,
            tail,
            new(12, OpCode.Move, reloadedStatics, new MemoryOperand(reloadedKlass, null, 0xB8, 0)),
            phi,
            new(14, OpCode.Move, result, new MemoryOperand(merged, null, 0x20, 0)),
            new(15, OpCode.Return, result),
        ]);
        var join = graph.Blocks.Single(block => block.Instructions.Contains(phi));
        var tailBlock = graph.Blocks.Single(block => block.Instructions.Contains(tail));
        phi.SetOperands([merged, ..join.Predecessors.Select(IOperand (predecessor) => predecessor == tailBlock ? reloadedStatics : statics)]);

        Run(graph);

        Assert.Multiple(() =>
        {
            Assert.That(ReadsInitialisedFlag(graph), Is.False);
            Assert.That(graph.Blocks, Does.Contain(tailBlock), "the compute path still reloads through the shared block");
        });
    }
}
