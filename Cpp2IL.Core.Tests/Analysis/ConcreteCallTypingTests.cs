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

    [TestCase("MoveNext")]
    [TestCase("Dispose")]
    public void PointerRegisterReceiverProvesInstantiation(string name)
    {
        // A byref receiver reaches the call as an untyped register holding `Move ptr, &local`
        // until the lea folds into the operand late in analysis. The pointee's concrete type is
        // the instantiation proof, not the pointer register's (missing) type.
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var enumerator = list.NestedTypes.Single(t => t.Name!.Contains("Enumerator"));
        var definition = enumerator.Methods.Single(m => m.Name == name);
        var canonical = new ConcreteGenericMethodAnalysisContext(definition, [app.SystemTypes.SystemObjectType], []);
        var instance = new GenericInstanceTypeAnalysisContext(enumerator, [app.SystemTypes.SystemStringType]);
        var cell = new LocalVariable("cell", new Register(null, "cell"), instance);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var call = name == "MoveNext"
            ? new Instruction(1, OpCode.Call, canonical, result, pointer)
            : new Instruction(1, OpCode.CallVoid, canonical, pointer);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.Move, pointer, new AddressOf(cell)), call, new(2, OpCode.Return)])
        };

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(((MethodAnalysisContext)call.Operands[0]).DeclaringType!.FullName,
                Is.EqualTo(instance.FullName));
            if (name == "MoveNext")
                Assert.That(result.Type, Is.SameAs(app.SystemTypes.SystemBooleanType));
        });
    }

    [Test]
    public void FieldAddressedReceiverProvesInstantiation()
    {
        // Same pointer-register shape, but the lea carries `&local.field` - the field's
        // declared instantiation is the proof.
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var definition = list.Methods.Single(m => m.Name == "get_Item");
        var canonical = new ConcreteGenericMethodAnalysisContext(definition, [app.SystemTypes.SystemObjectType], []);
        var instance = new GenericInstanceTypeAnalysisContext(list, [app.SystemTypes.SystemStringType]);
        var field = new InjectedFieldAnalysisContext("items", instance, FieldAttributes.Public, list, 16);
        var owner = new LocalVariable("owner", new Register(null, "owner"), instance);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var value = new LocalVariable("value", new Register(null, "value"));
        var call = new Instruction(1, OpCode.Call, canonical, value, pointer, new Immediate(0));
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.Move, pointer,
                    new AddressOf(new FieldReference(field, owner, 16))),
                call, new(2, OpCode.Return)])
        };

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(((MethodAnalysisContext)call.Operands[0]).DeclaringType!.FullName,
                Is.EqualTo(instance.FullName));
            Assert.That(value.Type, Is.SameAs(app.SystemTypes.SystemStringType));
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

    [Test]
    public void KlassHierarchyCastCheckTypesSurvivingLocal()
    {
        // castclass<T> lowers to a klass-hierarchy walk: [v] reads the klass,
        // [klass+table+depth*8] the hierarchy entry, and a mismatch branch throws
        // InvalidCastException. Reaching past that check proves the value is a T,
        // which types the erased IEnumerator.get_Current result it consumed.
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var corlib = app.AssembliesByName["mscorlib"];
        var getCurrent = corlib.GetTypeByFullName("System.Collections.IEnumerator")!
            .Methods.Single(m => m.Name == "get_Current");
        var stream = corlib.GetTypeByFullName("System.IO.Stream")!;
        var invalidCast = corlib.GetTypeByFullName("System.InvalidCastException")!;
        var observe = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Observe",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [app.SystemTypes.SystemObjectType]);
        var enumerator = new LocalVariable("enumerator", new Register(null, "X21"),
            corlib.GetTypeByFullName("System.Collections.IEnumerator"));
        var item = new LocalVariable("item", new Register(null, "X0"));
        var klass = new LocalVariable("klass", new Register(null, "X8"));
        var depth = new LocalVariable("depth", new Register(null, "W9"), app.SystemTypes.SystemInt32Type);
        var address = new LocalVariable("address", new Register(null, "X9"));
        var condition = new LocalVariable("condition", new Register(null, "cond"));
        var throwInstruction = new Instruction(7, OpCode.Throw, invalidCast);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.Call, getCurrent, item, enumerator),
                new(1, OpCode.Move, klass, new MemoryOperand(item)),
                new(2, OpCode.Add, address, new MemoryOperand(klass, null, 0xC8), depth),
                new(3, OpCode.CheckNotEqual, condition, new MemoryOperand(address, null, -8), stream),
                new(4, OpCode.ConditionalJump, throwInstruction, condition),
                new(5, OpCode.CallVoid, observe, item),
                new(6, OpCode.Return),
                throwInstruction])
        };

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.That(IlGenerator.EmittedLocalType(item, caller), Is.EqualTo(stream));
    }

    [Test]
    public void BooleanMergeDefinitionsEmitBoolean()
    {
        // A junk-merge register defined only by 0/1 literal copies across its
        // branch arms holds a bool even though no stack contract names one.
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var flag = new LocalVariable("flag", new Register(null, "X22"));
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.Move, flag, new Immediate(0)),
                new(1, OpCode.Move, flag, new Immediate(1)),
                new(2, OpCode.Move, new LocalVariable("sink", new Register(null, "sink")), flag),
                new(3, OpCode.Return)])
        };

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.That(IlGenerator.EmittedLocalType(flag, caller),
            Is.EqualTo(app.SystemTypes.SystemBooleanType));
    }

    [Test]
    public void SeededUnionSurvivesConditionalFlagUse()
    {
        // A copy-merge class whose only typed mate declares Boolean is provably
        // boolean; a brtrue use adds no contrary evidence and cannot veto it.
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var flag = new LocalVariable("flag", new Register(null, "X22"));
        var erased = new LocalVariable("erased", new Register(null, "X23"), app.SystemTypes.SystemObjectType);
        var destination = new LocalVariable("destination", new Register(null, "X24"),
            app.SystemTypes.SystemBooleanType);
        var hidden = new LocalVariable("hidden", new Register(null, "hidden"));
        var thenBlock = new Instruction(6, OpCode.Nop);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.Move, erased, hidden),
                new(1, OpCode.Move, flag, erased),
                new(2, OpCode.Move, destination, flag),
                new(3, OpCode.ConditionalJump, thenBlock, flag),
                new(4, OpCode.Move, flag, erased),
                new(5, OpCode.Return),
                thenBlock])
        };

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(IlGenerator.EmittedLocalType(flag, caller),
                Is.EqualTo(app.SystemTypes.SystemBooleanType));
            Assert.That(IlGenerator.EmittedLocalType(erased, caller),
                Is.EqualTo(app.SystemTypes.SystemBooleanType));
        });
    }

    [Test]
    public void AddressTakenLocalStaysUntypedDespiteBooleanDefinitions()
    {
        // A slot that is memset/memcpy'd through `&v` is raw storage; literal
        // 0/1 defs landing in it do not make it a bool - `ldloca`/`initblk`
        // over a Boolean local is unverifiable. Keep it untyped.
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var slot = new LocalVariable("slot", new Register(null, "X22"));
        var pointer = new LocalVariable("pointer", new Register(null, "X8"));
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.Move, slot, new Immediate(0)),
                new(1, OpCode.Move, pointer, new AddressOf(slot)),
                new(2, OpCode.Move, slot, new Immediate(1)),
                new(3, OpCode.Return)])
        };

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.That(IlGenerator.EmittedLocalType(slot, caller),
            Is.EqualTo(app.SystemTypes.SystemObjectType));
    }

    [Test]
    public void AddressTakenLocalStaysUntypedDespiteCastCheck()
    {
        // Same rule for the castclass proof: a `&`-taken slot is raw storage,
        // so even a proven klass-hierarchy check cannot type it - the emission
        // must keep the address diagnostic instead of `ldloca` over a managed
        // local.
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();
        var corlib = app.AssembliesByName["mscorlib"];
        var getCurrent = corlib.GetTypeByFullName("System.Collections.IEnumerator")!
            .Methods.Single(m => m.Name == "get_Current");
        var stream = corlib.GetTypeByFullName("System.IO.Stream")!;
        var invalidCast = corlib.GetTypeByFullName("System.InvalidCastException")!;
        var observe = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Observe",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [app.SystemTypes.SystemObjectType]);
        var enumerator = new LocalVariable("enumerator", new Register(null, "X21"),
            corlib.GetTypeByFullName("System.Collections.IEnumerator"));
        var item = new LocalVariable("item", new Register(null, "X0"));
        var klass = new LocalVariable("klass", new Register(null, "X8"));
        var depth = new LocalVariable("depth", new Register(null, "W9"), app.SystemTypes.SystemInt32Type);
        var address = new LocalVariable("address", new Register(null, "X9"));
        var condition = new LocalVariable("condition", new Register(null, "cond"));
        var pointer = new LocalVariable("pointer", new Register(null, "X10"));
        var throwInstruction = new Instruction(7, OpCode.Throw, invalidCast);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([
                new(0, OpCode.Call, getCurrent, item, enumerator),
                new(1, OpCode.Move, klass, new MemoryOperand(item)),
                new(2, OpCode.Add, address, new MemoryOperand(klass, null, 0xC8), depth),
                new(3, OpCode.CheckNotEqual, condition, new MemoryOperand(address, null, -8), stream),
                new(4, OpCode.ConditionalJump, throwInstruction, condition),
                new(5, OpCode.CallVoid, observe, item),
                new(6, OpCode.Move, pointer, new AddressOf(item)),
                new(7, OpCode.Return),
                throwInstruction])
        };

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.That(IlGenerator.EmittedLocalType(item, caller),
            Is.EqualTo(app.SystemTypes.SystemObjectType));
    }

}
