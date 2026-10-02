using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using System.Runtime.CompilerServices;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Regression;

// castle-recovery#289: a conditional select whose kept arm is a parameter's entry value
// (`csel w0, w0, w1, lt`, `fcsel s0, s1, s0, mi`) leaves the same-register copy
// `merged = param` on that edge after SSA destruction. Coalescing must not fold the parameter
// into a merge local that has other stores (its reads would become reads of a local nothing
// assigns), and post-SSA propagation must not forward the other arm's store across the join.
public class CoalescedParameterMergeTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [Test]
    public void SelectIntoAParameterRegisterKeepsBothArms()
    {
        // static int MinInt(int a, int b) => a < b ? a : b;   cmp w0, w1; csel w0, w0, w1, lt
        var intType = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type;
        var a = new LocalVariable("a", new Register(0, "X0"), intType);
        var b = new LocalVariable("b", new Register(1, "X1"), intType);
        var merged = new LocalVariable("merged", new Register(0, "X0", 1), intType);
        var less = new LocalVariable("less", new Register(null, "TEMP", 1));
        var ret = new Instruction(6, OpCode.Return, merged);
        var method = Method([
            new(0, OpCode.CheckLess, less, a, b),
            new(1, OpCode.ConditionalJump, Imm(4), less),
            new(2, OpCode.Move, merged, b),
            new(3, OpCode.Jump, Imm(6)),
            new(4, OpCode.Move, merged, a),
            new(5, OpCode.Jump, Imm(6)),
            ret], [a, b], merged, less);

        CopyCoalescer.Run(method);
        Simplifier.Simplify(method);

        Assert.Multiple(() =>
        {
            Assert.That(ret.Operands[0], Is.SameAs(merged), Dump(method));
            Assert.That(HasMove(method, merged, a), Is.True, "the parameter arm stays a store");
            Assert.That(HasMove(method, merged, b), Is.True, "the other arm stays a store");
            Assert.That(method.ControlFlowGraph!.Instructions.Any(i => ReferenceEquals(i.Destination, a)), Is.False,
                "nothing is stored into the parameter");
        });
    }

    [TestCase(false)]
    [TestCase(true)]
    public void IdentityArmOfASelectIsNotDropped(bool isFloat)
    {
        // void Set(float value) => field = value < 0f ? 0f : value;   fcsel s0, s1, s0, mi
        // void Set(int value)   => field = value < 0 ? 7 : value;     csel w0, w8, w0, lt
        var app = Cpp2IlApi.CurrentAppContext!;
        var type = isFloat ? app.SystemTypes.SystemSingleType : app.SystemTypes.SystemInt32Type;
        IOperand constant = isFloat ? new FloatLiteral(0f) : Imm(7);
        var value = new LocalVariable("value", new Register(32, "V0"), type);
        var merged = new LocalVariable("merged", new Register(32, "V0", 1), type);
        var notNegative = new LocalVariable("notNegative", new Register(null, "TEMP", 1));
        var use = new Instruction(5, OpCode.CallVoid, Str("Store"), merged);
        var method = Method([
            new(0, OpCode.CheckGreaterOrEqual, notNegative, value, Imm(0)),
            new(1, OpCode.ConditionalJump, Imm(4), notNegative),
            new(2, OpCode.Move, merged, constant),
            new(3, OpCode.Jump, Imm(5)),
            new(4, OpCode.Move, merged, value),
            use,
            new(6, OpCode.Return)], [value], merged, notNegative);

        CopyCoalescer.Run(method);
        Simplifier.Simplify(method);

        Assert.Multiple(() =>
        {
            Assert.That(use.Operands[1], Is.SameAs(merged), Dump(method));
            Assert.That(HasMove(method, merged, value), Is.True, "the identity arm stays a store");
            Assert.That(HasMove(method, merged, constant), Is.True, "the constant arm stays a store");
        });
    }

    [Test]
    public void NullDefaultOnACriticalEdgeKeepsBothArms()
    {
        // void M(string r) { if (r == null) r = "Default"; Use(r); }   cbnz x1, L; adrp/ldr x1, ...; L: bl Use
        // The cbnz edge is critical, so its `merged = r` copy sits before the branch itself.
        var stringType = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemStringType;
        var r = new LocalVariable("r", new Register(1, "X1"), stringType);
        var loaded = new LocalVariable("loaded", new Register(1, "X1", 2), stringType);
        var merged = new LocalVariable("merged", new Register(1, "X1", 3), stringType);
        var notNull = new LocalVariable("notNull", new Register(null, "TEMP", 1));
        var use = new Instruction(5, OpCode.CallVoid, Str("Use"), merged);
        var method = Method([
            new(0, OpCode.CheckNotEqual, notNull, r, Imm(0)),
            new(1, OpCode.Move, merged, r),
            new(2, OpCode.ConditionalJump, Imm(5), notNull),
            new(3, OpCode.Move, loaded, Str("Default")),
            new(4, OpCode.Move, merged, loaded),
            use,
            new(6, OpCode.Return)], [r], loaded, merged, notNull);

        CopyCoalescer.Run(method);
        Simplifier.Simplify(method);

        Assert.Multiple(() =>
        {
            Assert.That(use.Operands[1], Is.SameAs(merged), Dump(method));
            Assert.That(HasMove(method, merged, r), Is.True, "the non-null path keeps the argument");
            Assert.That(method.ControlFlowGraph!.Instructions.Any(i => i.OpCode == OpCode.Move
                && ReferenceEquals(i.Operands[0], merged) && i.Operands[1] is StringLiteral), Is.True,
                "the null path stores the default");
        });
    }

    [Test]
    public void AParameterStoreIsNotForwardedPastTheJoinItsArgumentReaches()
    {
        // if (c) p = 7; Use(p);   the argument reaches Use on the other path
        var intType = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type;
        var p = new LocalVariable("p", new Register(0, "X0"), intType);
        var c = new LocalVariable("c", new Register(null, "TEMP", 1));
        var use = new Instruction(3, OpCode.CallVoid, Str("Use"), p);
        var method = Method([
            new(0, OpCode.CheckEqual, c, p, Imm(0)),
            new(1, OpCode.ConditionalJump, Imm(3), c),
            new(2, OpCode.Move, p, Imm(7)),
            use,
            new(4, OpCode.Return)], [p], c);

        Simplifier.Simplify(method);

        Assert.That(use.Operands[1], Is.SameAs(p), Dump(method));
    }

    [Test]
    public void AFieldLoadIntoItsOwnReceiverIsNotForwarded()
    {
        // while (n != null) { t += n.V; n = n.Next; }: the loop test after `n = n.Next` reads the
        // new n, not n.Next.
        var app = Cpp2IlApi.CurrentAppContext!;
        var next = new InjectedFieldAnalysisContext("Next", app.SystemTypes.SystemObjectType,
            FieldAttributes.Public, app.SystemTypes.SystemObjectType);
        var n = new LocalVariable("n", new Register(0, "X0"), app.SystemTypes.SystemObjectType);
        var c = new LocalVariable("c", new Register(null, "TEMP", 1));
        var test = new Instruction(2, OpCode.CheckNotEqual, c, n, Imm(0));
        var method = Method([
            new(0, OpCode.CallVoid, Str("Visit"), n),
            new(1, OpCode.Move, n, new FieldReference(next, n, 16)),
            test,
            new(3, OpCode.ConditionalJump, Imm(0), c),
            new(4, OpCode.Return)], [n], c);

        Simplifier.Simplify(method);

        Assert.That(test.Operands[1], Is.SameAs(n), Dump(method));
    }

    [Test]
    public void ANullTestedEdgeOfAnUnrelatedReferenceMergeCarriesNull()
    {
        // string Id => _instance?.Id ?? "";   ldr x9, [x0, #f]; cbz x9, join; ldr x9, [x9, #id]; join: ...
        // x9 merges the instance (typed Instance) and its Id (string): no managed copy between the
        // two, but on the cbz edge the instance is null, and null is a string too.
        var app = Cpp2IlApi.CurrentAppContext!;
        var stringType = app.SystemTypes.SystemStringType;
        var instanceType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Edge", "Instance",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public | TypeAttributes.Class);
        var id = new InjectedFieldAnalysisContext("Id", stringType, FieldAttributes.Public, instanceType);
        var instance = new LocalVariable("instance", new Register(9, "X9", 1), instanceType);
        var loaded = new LocalVariable("loaded", new Register(9, "X9", 3), stringType);
        var merged = new LocalVariable("merged", new Register(9, "X9", 2), stringType);
        var isNull = new LocalVariable("isNull", new Register(null, "TEMP", 1));
        var phi = new Instruction(4, OpCode.Phi, merged, instance, instance);
        var method = Method([
            new(0, OpCode.CallVoid, Str("Load"), instance),
            new(1, OpCode.CheckEqual, isNull, instance, Imm(0)),
            new(2, OpCode.ConditionalJump, Imm(4), isNull),
            new(3, OpCode.Move, loaded, new FieldReference(id, instance, 16)),
            phi,
            new(5, OpCode.Return, merged)], [], instance, loaded, merged, isNull);
        var graph = method.ControlFlowGraph!;
        var join = graph.Blocks.Single(b => b.Instructions.Contains(phi));
        var test = graph.Blocks.Single(b => b.Instructions.Any(i => i.OpCode == OpCode.ConditionalJump));
        for (var k = 0; k < join.Predecessors.Count; k++)
            phi.SetOperand(1 + k, join.Predecessors[k] == test ? instance : loaded);

        SsaForm.Remove(method);

        Assert.Multiple(() =>
        {
            Assert.That(test.Instructions.Any(i => i.OpCode == OpCode.Move && i.Operands[0] == merged
                && i.Operands[1] is Immediate { Value: 0 }), Is.True, Dump(method));
            Assert.That(HasMove(method, merged, loaded), Is.True, "the loaded Id still flows on the other edge");
        });
    }

    private static bool HasMove(MethodAnalysisContext method, LocalVariable destination, IOperand source)
        => method.ControlFlowGraph!.Instructions.Any(i => i.OpCode == OpCode.Move
            && ReferenceEquals(i.Operands[0], destination) && Equals(i.Operands[1], source));

    private static MethodAnalysisContext Method(List<Instruction> instructions, List<LocalVariable> parameters,
        params LocalVariable[] locals)
    {
        foreach (var instruction in instructions)
            if (instruction.OpCode is OpCode.Jump or OpCode.ConditionalJump && instruction.Operands[0] is Immediate target)
                instruction.SetOperand(0, instructions.Single(i => i.Index == (int)target.Value));

        var method = (MethodAnalysisContext)RuntimeHelpers.GetUninitializedObject(typeof(MethodAnalysisContext));
        method.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        method.ParameterLocals = parameters;
        method.Locals = [.. parameters, .. locals];
        return method;
    }

    private static string Dump(MethodAnalysisContext method)
        => string.Join("\n", method.ControlFlowGraph!.Instructions);
}
