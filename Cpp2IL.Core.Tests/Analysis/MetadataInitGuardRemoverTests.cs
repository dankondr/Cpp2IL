using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class MetadataInitGuardRemoverTests
{
    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [Test]
    public void SplitAddressFlagLoadIsRecognized()
    {
        var klass = new LocalVariable("klass", new Register(null, "klass"));
        var address = new LocalVariable("address", new Register(null, "address"));
        var masked = new LocalVariable("masked", new Register(null, "masked"));
        var test = new Instruction(1, OpCode.And, masked, new MemoryOperand(address), new Immediate(1));
        var graph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Add, address, klass, new Immediate(0x135)),
            test,
            new Instruction(2, OpCode.Return)
        ]);

        Assert.That(MetadataInitGuardRemover.IsInitialisedFlagTest(graph, test, 0x135), Is.True);
    }

    [Test]
    public void MetadataGuardWithValueProducingSkipArmIsRemoved()
    {
        var flag = new LocalVariable("flag", new Register(null, "x8"));
        var condition = new LocalVariable("condition", new Register(null, "temp"));
        var address = new LocalVariable("address", new Register(null, "x9"));
        var result = new LocalVariable("result", new Register(null, "x0"));
        var handle = new LocalVariable("handle", new Register(null, "x1"));
        var skipped = new LocalVariable("skipped", new Register(null, "x2"));
        var initialized = new LocalVariable("initialized", new Register(null, "x3"));
        var merged = new LocalVariable("merged", new Register(null, "x4"));
        var init = new Instruction(5, OpCode.Nop);
        var phi = new Instruction(9, OpCode.Phi, merged, initialized, skipped);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, flag, new MemoryOperand(address, addend: 0xC01)),
            new(1, OpCode.CheckEqual, condition, flag, new Immediate(0)),
            new(2, OpCode.ConditionalJump, init, condition),
            new(3, OpCode.Move, skipped, new Immediate(0)),
            new(4, OpCode.Jump, phi),
            init,
            new(6, OpCode.Call, new StringLiteral("il2cpp_codegen_initialize_runtime_metadata"), result, handle),
            new(7, OpCode.Move, initialized, new Immediate(1)),
            new(8, OpCode.Move, new MemoryOperand(address, addend: 0xC01), new Immediate(1)),
            phi,
            new(10, OpCode.Return, merged),
        };
        var graph = new ISILControlFlowGraph(instructions);

        MetadataInitGuardRemover.Run(graph, 0x135);

        Assert.That(graph.Instructions.Any(i => i.OpCode == OpCode.Call), Is.False);
        Assert.That(graph.Instructions.Any(i => i.Destination is MemoryOperand { Addend: 0xC01 }), Is.False);
        Assert.That(graph.Instructions.Any(i => i.OpCode == OpCode.Move && ReferenceEquals(i.Destination, skipped)), Is.True);
    }

    [Test]
    public void BitTestMetadataGuardIsRemoved()
    {
        var address = new LocalVariable("address", new Register(null, "x9"));
        var flag = new LocalVariable("flag", new Register(null, "x8"));
        var masked = new LocalVariable("masked", new Register(null, "temp"));
        var result = new LocalVariable("result", new Register(null, "x0"));
        var handle = new LocalVariable("handle", new Register(null, "x1"));
        var ret = new Instruction(5, OpCode.Return);
        var graph = new ISILControlFlowGraph([
            new(0, OpCode.Move, flag, new MemoryOperand(address, addend: 0xCFC)),
            new(1, OpCode.And, masked, flag, new Immediate(1)),
            new(2, OpCode.ConditionalJump, ret, masked),
            new(3, OpCode.Call, new StringLiteral("il2cpp_codegen_initialize_runtime_metadata"), result, handle),
            new(4, OpCode.Move, new MemoryOperand(address, addend: 0xCFC), new Immediate(1)),
            ret,
        ]);

        MetadataInitGuardRemover.Run(graph, 0x135);

        Assert.That(graph.Instructions.Any(i => i.OpCode == OpCode.Call), Is.False);
        Assert.That(graph.Instructions.Any(i => i.Destination is MemoryOperand { Addend: 0xCFC }), Is.False);
    }

    [Test]
    public void ValueProducingMetadataGuardFoldsTheRuntimeFlag()
    {
        var address = new LocalVariable("address", new Register(null, "x9"));
        var instance = new LocalVariable("instance", new Register(null, "x19"));
        var flag = new MemoryOperand(addend: 0x86FA497, accessSize: 1);
        var loadedFlag = new LocalVariable("flag", new Register(null, "x8"));
        var condition = new LocalVariable("condition", new Register(null, "condition"));
        var result = new LocalVariable("result", new Register(null, "x0"));
        var handle = new LocalVariable("handle", new Register(null, "x1"));
        var one = new LocalVariable("one", new Register(null, "x24"));
        var init = new Instruction(5, OpCode.Nop);
        var merge = new Instruction(10, OpCode.Return);
        var graph = new ISILControlFlowGraph([
            new(0, OpCode.Move, loadedFlag, flag),
            new(1, OpCode.CheckEqual, condition, loadedFlag, new Immediate(0)),
            new(2, OpCode.ConditionalJump, init, condition),
            new(3, OpCode.Nop),
            new(4, OpCode.Jump, merge),
            init,
            new(6, OpCode.Call, new StringLiteral("il2cpp_codegen_initialize_runtime_metadata"), result, handle),
            new(7, OpCode.Move, one, new Immediate(1)),
            new(8, OpCode.Move, flag, one),
            new(9, OpCode.Move, new MemoryOperand(instance, addend: 0x240), new Immediate(42)),
            merge,
        ]);

        MetadataInitGuardRemover.Run(graph, 0x135);

        Assert.That(graph.Instructions.Any(i => i.Operands.Any(o => o is MemoryOperand memory && memory.Equals(flag))), Is.False);
    }

    [Test]
    public void MetadataFlagStoreThroughConstantBaseMatchesAbsoluteLoad()
    {
        var baseAddress = new LocalVariable("base", new Register(null, "x22"));
        var loadedFlag = new LocalVariable("flag", new Register(null, "x8"));
        var condition = new LocalVariable("condition", new Register(null, "condition"));
        var result = new LocalVariable("result", new Register(null, "x0"));
        var handle = new LocalVariable("handle", new Register(null, "x1"));
        var init = new Instruction(4, OpCode.Nop);
        var merge = new Instruction(8, OpCode.Return);
        var graph = new ISILControlFlowGraph([
            new(0, OpCode.Move, baseAddress, new Immediate(0x86FA000)),
            new(1, OpCode.Move, loadedFlag, new MemoryOperand(addend: 0x86FA497, accessSize: 4)),
            new(2, OpCode.CheckEqual, condition, loadedFlag, new Immediate(0)),
            new(3, OpCode.ConditionalJump, init, condition),
            init,
            new(5, OpCode.Call, new StringLiteral("il2cpp_codegen_initialize_runtime_metadata"), result, handle),
            new(6, OpCode.Move, new MemoryOperand(baseAddress, addend: 0x497, accessSize: 1), new Immediate(1)),
            new(7, OpCode.Jump, merge),
            merge,
        ]);

        MetadataInitGuardRemover.Run(graph, 0x135);

        Assert.That(graph.Instructions.Any(instruction => instruction.Operands.Any(operand =>
            operand is MemoryOperand memory && memory.Addend == 0x86FA497)), Is.False);
    }

    [Test]
    public void BareRuntimeClassInitCallIsRemoved()
    {
        var result = new LocalVariable("result", new Register(null, "x0"));
        var klass = new LocalVariable("klass", new Register(null, "x0"));
        var graph = new ISILControlFlowGraph([
            new(0, OpCode.Call, new StringLiteral("il2cpp_codegen_runtime_class_init"), result, klass),
            new(1, OpCode.Return),
        ]);

        MetadataInitGuardRemover.Run(graph, 0x135);

        Assert.That(graph.Instructions.Any(instruction => instruction.IsCall), Is.False);
    }

    // if ([ctx + rgctxOffset] == 0) { <unresolved helper>(ctx); } - the shape codegen emits around
    // the extra generic-context argument's lazily-initialized rgctx slot.
    private static (InjectedMethodAnalysisContext Method, ISILControlFlowGraph Graph) LazyContextFixture(
        LocalVariable context, long slotOffset, IOperand callTarget, IOperand callArgument,
        IOperand[] parameterOperands)
    {
        var condition = new LocalVariable("condition", new Register(null, "condition"));
        var negated = new LocalVariable("negated", new Register(null, "negated"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var reloaded = new LocalVariable("reloaded", new Register(null, "reloaded"));
        var init = new Instruction(3, OpCode.Nop);
        var merge = new Instruction(6, OpCode.Move, reloaded, new MemoryOperand(context, addend: slotOffset));
        var method = new InjectedMethodAnalysisContext(App.SystemTypes.SystemObjectType, "Fixture",
            App.SystemTypes.SystemObjectType, System.Reflection.MethodAttributes.Static,
            [App.SystemTypes.SystemObjectType]);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.CheckEqual, condition, new MemoryOperand(context, addend: slotOffset), new Immediate(0)),
            new(1, OpCode.Not, negated, condition),
            new(2, OpCode.ConditionalJump, merge, negated),
            init,
            new(4, OpCode.Call, callTarget, result, callArgument),
            new(5, OpCode.Jump, merge),
            merge,
            new(7, OpCode.Return, reloaded),
        };
        method.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        method.ParameterOperands = parameterOperands.ToList();
        return (method, method.ControlFlowGraph);
    }

    private static readonly IOperand[] OneParamAndMethodInfoOperands =
        [new Register(null, "X0"), new Register(null, "X1")];

    [Test]
    public void RgctxGuardForUntypedExtraContextArgumentIsExcised()
    {
        // X2 holds the extra generic-context argument: untyped, and beyond the signature's operands.
        var context = new LocalVariable("context", new Register(null, "X2"));
        var (method, graph) = LazyContextFixture(context, 0x38,
            new Immediate(0x12345678), context, OneParamAndMethodInfoOperands);

        MetadataInitGuardRemover.RunRgctx(method);

        Assert.That(graph.Instructions.Any(instruction => instruction.IsCall), Is.False);
        Assert.That(graph.Instructions.Any(instruction => instruction.OpCode == OpCode.Move
            && instruction.Operands is [_, MemoryOperand { Addend: 0x38 }]), Is.True);
    }

    [Test]
    public void RgctxGuardOnDeclaredParameterRegisterIsKept()
    {
        // Same shape, but the guarded base occupies a register the signature accounts for -
        // indistinguishable from a user lazy field init, so the call must survive.
        var context = new LocalVariable("context", new Register(null, "X0"));
        var (method, graph) = LazyContextFixture(context, 0x38,
            new Immediate(0x12345678), context, OneParamAndMethodInfoOperands);

        MetadataInitGuardRemover.RunRgctx(method);

        Assert.That(graph.Instructions.Any(instruction => instruction.IsCall), Is.True);
    }

    [Test]
    public void RgctxGuardKeepsArmCallThatDoesNotTakeTheContext()
    {
        // The region call has to be provably an initializer of the guarded object; a helper taking
        // a different argument is an arbitrary effect and the guard stays.
        var context = new LocalVariable("context", new Register(null, "X2"));
        var other = new LocalVariable("other", new Register(null, "X3"));
        var (method, graph) = LazyContextFixture(context, 0x38,
            new Immediate(0x12345678), other, OneParamAndMethodInfoOperands);

        MetadataInitGuardRemover.RunRgctx(method);

        Assert.That(graph.Instructions.Any(instruction => instruction.IsCall), Is.True);
    }

    [Test]
    public void RgctxGuardKeepsResolvedManagedCallee()
    {
        // A managed call we resolved is user code, not an init helper; keep the guard.
        var context = new LocalVariable("context", new Register(null, "X2"));
        var callee = new InjectedMethodAnalysisContext(App.SystemTypes.SystemObjectType, "Helper",
            App.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static,
            [App.SystemTypes.SystemObjectType]);
        var (method, graph) = LazyContextFixture(context, 0x38,
            callee, context, OneParamAndMethodInfoOperands);

        MetadataInitGuardRemover.RunRgctx(method);

        Assert.That(graph.Instructions.Any(instruction => instruction.IsCall), Is.True);
    }

    [Test]
    public void GuardOnADifferentFieldOffsetIsKept()
    {
        // The rgctx slot offset is the discriminator; a different field must not match.
        var context = new LocalVariable("context", new Register(null, "X2"));
        var (method, graph) = LazyContextFixture(context, 0x40,
            new Immediate(0x12345678), context, OneParamAndMethodInfoOperands);

        MetadataInitGuardRemover.RunRgctx(method);

        Assert.That(graph.Instructions.Any(instruction => instruction.IsCall), Is.True);
    }
}
