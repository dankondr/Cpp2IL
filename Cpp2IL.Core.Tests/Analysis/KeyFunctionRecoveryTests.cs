using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class KeyFunctionRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [Test]
    public void BoxTypeFallsBackToAddressedValue()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var value = new LocalVariable("value", new Register(null, "value"))
            { Type = app.SystemTypes.SystemInt32Type };
        var result = new LocalVariable("result", new Register(null, "result"));
        var instruction = new Instruction(0, OpCode.Call,
            new StringLiteral("il2cpp_vm_object_box"), result,
            new MemoryOperand(addend: 0x81AAA10), new AddressOf(value));

        KeyFunctionRecovery.RewriteBox(instruction);

        Assert.That(instruction.OpCode, Is.EqualTo(OpCode.Box));
        Assert.That(instruction.Operands[0], Is.SameAs(result));
        Assert.That(instruction.Operands[1], Is.SameAs(app.SystemTypes.SystemInt32Type));
        Assert.That(((AddressOf)instruction.Operands[2]).Target, Is.SameAs(value));
    }

    [Test]
    public void IsInstHelperBecomesManagedReferenceCast()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var value = new LocalVariable("value", new Register(null, "value"))
            { Type = app.SystemTypes.SystemObjectType };
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemStringType };
        var instruction = new Instruction(0, OpCode.Call,
            new StringLiteral("il2cpp_vm_object_is_inst"), result, value,
            app.SystemTypes.SystemStringType, new Immediate(0));

        KeyFunctionRecovery.RewriteIsInst(instruction);

        Assert.That(instruction.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(instruction.Operands[0], Is.SameAs(result));
        Assert.That(instruction.Operands[1], Is.TypeOf<ReferenceCast>());
        Assert.That(((ReferenceCast)instruction.Operands[1]).Type,
            Is.SameAs(app.SystemTypes.SystemStringType));
    }

    [Test]
    public void Unity6DefaultsInt32ClassOffsetIsRecognized()
    {
        var types = Cpp2IlApi.CurrentAppContext!.SystemTypes;

        Assert.That(KeyFunctionRecovery.Unity6PrimitiveDefaultsClass(types, 0x48),
            Is.SameAs(types.SystemInt32Type));
        Assert.That(KeyFunctionRecovery.Unity6PrimitiveDefaultsClass(types, 0x78),
            Is.SameAs(types.SystemSingleType));
        Assert.That(KeyFunctionRecovery.Unity6PrimitiveDefaultsClass(types, 0x90),
            Is.SameAs(types.SystemStringType));
    }

    [Test]
    public void Unity6DefaultsClassLoadSeedsRuntimeClassType()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimpleV106Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var defaults = new LocalVariable("defaults", new Register(null, "X8"));
        var klass = new LocalVariable("klass", new Register(null, "X9"));
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, defaults, new MemoryOperand(addend: 0x81AAA10)),
            new(1, OpCode.Move, klass, new MemoryOperand(defaults, addend: 0x90)),
            new(2, OpCode.Return)]);

        LocalVariables.SeedIl2CppDefaultsClassTypes(context);

        Assert.That(klass.Type, Is.TypeOf<RuntimeClassTypeAnalysisContext>());
        Assert.That(((RuntimeClassTypeAnalysisContext)klass.Type!).RepresentedType,
            Is.SameAs(app.SystemTypes.SystemStringType));
    }

    [Test]
    public void DefaultsDefinitionMatchesClonedSsaLocalByRegister()
    {
        var register = new Register(null, "x23", 4);
        var definition = new LocalVariable("definition", register);
        var use = new LocalVariable("use", register);
        var graph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, definition, new MemoryOperand(addend: 0x81AAA10)),
            new Instruction(1, OpCode.Return),
        ]);

        Assert.That(KeyFunctionRecovery.HasAbsoluteDefinition(graph, use), Is.True);
    }

    [Test]
    public void BoxClassPointerMoveIsUnwrappedToDefaultsField()
    {
        var defaults = new LocalVariable("defaults", new Register(null, "x23", 4));
        var classPointer = new LocalVariable("classPointer", new Register(null, "x0", 126));
        var source = new MemoryOperand(defaults, addend: 0x48);
        var graph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, classPointer, source),
            new Instruction(1, OpCode.Return),
        ]);

        Assert.That(KeyFunctionRecovery.ResolveMoveSource(graph, classPointer), Is.EqualTo(source));
    }
}
