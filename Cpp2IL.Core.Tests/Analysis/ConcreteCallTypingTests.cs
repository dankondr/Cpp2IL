using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class ConcreteCallTypingTests
{
    [TestCase("get_Item", false)]
    [TestCase("set_Item", false)]
    [TestCase("get_Item", true)]
    [TestCase("set_Item", true)]
    public void DelayedMethodInfoTypesReceiverParametersAndResult(string name, bool callerParameter)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        TypeAnalysisContext element = app.SystemTypes.SystemStringType;
        if (callerParameter)
        {
            var parameter = new GenericParameterTypeAnalysisContext("T", 0,
                Il2CppTypeEnum.IL2CPP_TYPE_MVAR, 0, caller);
            caller.GenericParameters.Add(parameter);
            element = parameter;
        }
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var definition = list.Methods.Single(m => m.Name == name);
        var canonical = new ConcreteGenericMethodAnalysisContext(definition, [app.SystemTypes.SystemObjectType], []);
        var concrete = new ConcreteGenericMethodAnalysisContext(definition, [element], []);
        var info = new LocalVariable("info", new Register(null, "info"));
        var hidden = new LocalVariable("hidden", new Register(null, "hidden"));
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"));
        var value = new LocalVariable("value", new Register(null, "value"));
        var call = name == "get_Item"
            ? new Instruction(2, OpCode.Call, canonical, value, receiver, new Immediate(0), hidden)
            : new Instruction(2, OpCode.CallVoid, canonical, receiver, new Immediate(0), value, hidden);
        var observe = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Observe",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [app.SystemTypes.SystemObjectType]);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.Move, info, new RuntimeMethodInfoAnalysisContext(concrete, list.DeclaringAssembly)),
                new(1, OpCode.Move, hidden, info), call,
                name == "get_Item" ? new(3, OpCode.CallVoid, observe, value) : new(3, OpCode.Nop),
                new(4, OpCode.Return)]);

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(call.Operands[0], Is.SameAs(concrete));
            Assert.That(receiver.Type!.FullName, Is.EqualTo(concrete.DeclaringType!.FullName));
            Assert.That(value.Type, Is.SameAs(element));
        });
    }

    [Test]
    public void LoopHeaderKeepsConcreteReceiverCopy()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var definition = list.Methods.Single(m => m.Name == "get_Item");
        var canonical = new ConcreteGenericMethodAnalysisContext(definition, [app.SystemTypes.SystemObjectType], []);
        var concrete = new ConcreteGenericMethodAnalysisContext(definition, [app.SystemTypes.SystemStringType], []);
        var incoming = new LocalVariable("incoming", new Register(null, "list", 1), concrete.DeclaringType!);
        var receiver = new LocalVariable("receiver", new Register(null, "list", 2));
        var backedge = new LocalVariable("backedge", new Register(null, "list", 3));
        var value = new LocalVariable("value", new Register(null, "value"));
        var hidden = new LocalVariable("hidden", new Register(null, "hidden"));
        var info = new LocalVariable("info", new Register(null, "info"));
        var header = new Instruction(2, OpCode.Nop);
        var call = new Instruction(3, OpCode.Call, canonical, value, receiver, new Immediate(0), hidden);
        var exit = new Instruction(6, OpCode.Return);
        var graph = new ISILControlFlowGraph([
            new(0, OpCode.Move, info, new RuntimeMethodInfoAnalysisContext(concrete, list.DeclaringAssembly)),
            new(1, OpCode.Move, hidden, info), header, call,
            new(4, OpCode.Move, backedge, incoming),
            new(5, OpCode.ConditionalJump, header, new Immediate(1)), exit]);
        var block = graph.Blocks.Single(b => b.Instructions.Contains(header));
        block.Instructions.Insert(0, new Instruction(-1, OpCode.Phi, receiver, incoming, backedge));
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []) { ControlFlowGraph = graph };

        LocalVariables.ResolveTypesAndFields(caller);
        SsaForm.Remove(caller);

        Assert.Multiple(() =>
        {
            Assert.That(receiver.Type!.FullName, Is.EqualTo(concrete.DeclaringType!.FullName));
            Assert.That(graph.Instructions.Any(i => i.OpCode == OpCode.Move
                && ReferenceEquals(i.Operands[0], receiver) && ReferenceEquals(i.Operands[1], incoming)), Is.True);
        });
    }

    [Test]
    public void UnprovenInstantiationKeepsCanonicalTypes()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var definition = list.Methods.Single(m => m.Name == "get_Item");
        var canonical = new ConcreteGenericMethodAnalysisContext(definition, [app.SystemTypes.SystemObjectType], []);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"));
        var value = new LocalVariable("value", new Register(null, "value"));
        var call = new Instruction(0, OpCode.Call, canonical, value, receiver, new Immediate(0));
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [])
        { ControlFlowGraph = new ISILControlFlowGraph([call, new(1, OpCode.Return)]) };

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(call.Operands[0], Is.SameAs(canonical));
            Assert.That(receiver.Type, Is.SameAs(canonical.DeclaringType));
            Assert.That(value.Type, Is.SameAs(app.SystemTypes.SystemObjectType));
        });
    }
    [TestCase(false)]
    [TestCase(true)]
    public void ConcreteReceiverProvesInstantiationWithoutMethodInfo(bool constrained)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var definition = list.Methods.Single(m => m.Name == "get_Item");
        var canonical = new ConcreteGenericMethodAnalysisContext(definition, [app.SystemTypes.SystemObjectType], []);
        var listType = new GenericInstanceTypeAnalysisContext(list, [app.SystemTypes.SystemStringType]);
        var source = new LocalVariable("source", new Register(null, "source"), listType);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"));
        var value = new LocalVariable("value", new Register(null, "value"));
        var call = new Instruction(1, OpCode.Call, canonical, value,
            constrained ? new AddressOf(receiver) : receiver, new Immediate(0));
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [])
        { ControlFlowGraph = new ISILControlFlowGraph([new(0, OpCode.Move, receiver, source), call, new(2, OpCode.Return)]) };

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(((MethodAnalysisContext)call.Operands[0]).DeclaringType!.FullName, Is.EqualTo(listType.FullName));
            Assert.That(value.Type, Is.SameAs(app.SystemTypes.SystemStringType));
        });
    }

    [TestCase(false)]
    [TestCase(true)]
    public void MethodInfoSpecializesOpenDefinitionAndEnumMarker(bool enumMarker)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var corlib = app.AssembliesByName["mscorlib"];
        var definition = corlib.GetTypeByFullName("System.Activator")!.Methods.Single(m =>
            m.Name == "CreateInstance" && m.GenericParameters.Count == 1 && m.Parameters.Count == 0);
        var element = enumMarker ? corlib.GetTypeByFullName("System.DayOfWeek")! : app.SystemTypes.SystemStringType;
        MethodAnalysisContext canonical = enumMarker
            ? new ConcreteGenericMethodAnalysisContext(definition, [], [corlib.GetTypeByFullName("System.Int32Enum")!])
            : definition;
        var concrete = new ConcreteGenericMethodAnalysisContext(definition, [], [element]);
        var value = new LocalVariable("value", new Register(null, "value"));
        var call = new Instruction(0, OpCode.Call, canonical, value,
            new RuntimeMethodInfoAnalysisContext(concrete, corlib));
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [])
        { ControlFlowGraph = new ISILControlFlowGraph([call, new(1, OpCode.Return)]) };

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(call.Operands[0], Is.SameAs(concrete));
            Assert.That(value.Type, Is.SameAs(element));
        });
    }

    [TestCase(false)]
    [TestCase(true)]
    public void ReceiverCannotReplaceAnAuthoritativeInstantiation(bool descriptor)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var definition = list.Methods.Single(m => m.Name == "get_Item");
        var element = descriptor ? app.SystemTypes.SystemObjectType : app.SystemTypes.SystemInt32Type;
        var callee = new ConcreteGenericMethodAnalysisContext(definition, [element], []);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"),
            new GenericInstanceTypeAnalysisContext(list, [app.SystemTypes.SystemStringType]));
        var value = new LocalVariable("value", new Register(null, "value"));
        var call = new Instruction(0, OpCode.Call, callee, value, receiver, new Immediate(0));
        var hidden = new LocalVariable("hidden", new Register(null, "hidden"));
        var info = new LocalVariable("info", new Register(null, "info"));
        if (descriptor)
            call.AddOperands([hidden]);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [])
        { ControlFlowGraph = new ISILControlFlowGraph([
            new(-2, OpCode.Move, info, new RuntimeMethodInfoAnalysisContext(callee, list.DeclaringAssembly)),
            new(-1, OpCode.Move, hidden, info), call, new(1, OpCode.Return)]) };

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(call.Operands[0], Is.SameAs(callee));
            Assert.That(value.Type, Is.SameAs(element));
        });
    }

    [Test]
    public void GenericOutUsesProducedTypeInsteadOfLaterConsumerHint()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var corlib = app.AssembliesByName["mscorlib"];
        var dictionary = corlib.GetTypeByFullName("System.Collections.Generic.Dictionary`2")!;
        var definition = dictionary.Methods.Single(m => m.Name == "TryGetValue");
        var stream = corlib.GetTypeByFullName("System.IO.Stream")!;
        var memoryStream = corlib.GetTypeByFullName("System.IO.MemoryStream")!;
        var canonical = new ConcreteGenericMethodAnalysisContext(definition,
            [app.SystemTypes.SystemStringType, app.SystemTypes.SystemObjectType], []);
        var concrete = new ConcreteGenericMethodAnalysisContext(definition,
            [app.SystemTypes.SystemStringType, memoryStream], []);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var value = new LocalVariable("value", new Register(null, "value"));
        var info = new LocalVariable("info", new Register(null, "info"));
        var hidden = new LocalVariable("hidden", new Register(null, "hidden"));
        var observe = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Observe",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [stream]);
        var call = new Instruction(2, OpCode.Call, canonical, result, receiver,
            new Immediate(0), new AddressOf(value), hidden);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [])
        { ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, info, new RuntimeMethodInfoAnalysisContext(concrete, corlib)),
            new(1, OpCode.Move, hidden, info), call,
            new(3, OpCode.CallVoid, observe, value), new(4, OpCode.Return)]) };

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(call.Operands[0], Is.SameAs(concrete));
            Assert.That(value.Type, Is.SameAs(memoryStream));
            Assert.That(result.Type, Is.SameAs(app.SystemTypes.SystemBooleanType));
        });
    }

    [Test]
    public void ConcreteHiddenReturnAlsoRewritesBufferUses()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var definition = list.Methods.Single(m => m.Name == "GetEnumerator");
        var canonical = new ConcreteGenericMethodAnalysisContext(definition, [app.SystemTypes.SystemObjectType], []);
        var concrete = new ConcreteGenericMethodAnalysisContext(definition, [app.SystemTypes.SystemStringType], []);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"));
        var buffer = new LocalVariable("buffer", new Register(null, "stack_-30"));
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var info = new LocalVariable("info", new Register(null, "info"));
        var hidden = new LocalVariable("hidden", new Register(null, "hidden"));
        var observe = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Observe",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static,
            [new ByRefTypeAnalysisContext(concrete.ReturnType)]);
        var call = new Instruction(3, OpCode.Call, canonical, new MemoryOperand(pointer), receiver, hidden);
        var use = new Instruction(4, OpCode.CallVoid, observe, new AddressOf(buffer));
        var item = new LocalVariable("item", new Register(null, "item"));
        var current = new LocalVariable("current", new Register(null, "stack_-20"));
        var read = new Instruction(5, OpCode.Move, item, current);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.Move, pointer, new AddressOf(buffer)),
                new(1, OpCode.Move, info, new RuntimeMethodInfoAnalysisContext(concrete, list.DeclaringAssembly)),
                new(2, OpCode.Move, hidden, info), call, use, read, new(6, OpCode.Return)])
        };

        LocalVariables.ResolveTypesAndFields(caller);

        var result = (LocalVariable)call.Destination!;
        Assert.Multiple(() =>
        {
            Assert.That(result.Type!.FullName, Is.EqualTo(concrete.ReturnType.FullName));
            Assert.That(((AddressOf)use.Operands[1]).Target, Is.SameAs(result));
            Assert.That(((FieldReference)read.Operands[1]).Field.FieldType.FullName,
                Is.EqualTo(app.SystemTypes.SystemStringType.FullName));
        });
    }

}
