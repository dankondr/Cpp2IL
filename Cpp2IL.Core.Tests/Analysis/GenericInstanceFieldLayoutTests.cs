using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;

namespace Cpp2IL.Core.Tests.Analysis;

public class GenericInstanceFieldLayoutTests
{
    [Test]
    public void PhiSelectedOffsetsResolveToManagedFields()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Background",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var radius = new InjectedFieldAnalysisContext("radius", app.SystemTypes.SystemSingleType,
            FieldAttributes.Public, owner, 16);
        var corner = new InjectedFieldAnalysisContext("corner", app.SystemTypes.SystemSingleType,
            FieldAttributes.Public, owner, 20);
        owner.Fields.Add(radius);
        owner.Fields.Add(corner);
        var method = new InjectedMethodAnalysisContext(owner, "Read", app.SystemTypes.SystemVoidType,
            MethodAttributes.Static, []);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), owner);
        var left = new LocalVariable("left", new Register(null, "left"));
        var right = new LocalVariable("right", new Register(null, "right"));
        var selector = new LocalVariable("selector", new Register(null, "selector"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var load = new Instruction(3, OpCode.Move, result,
            new MemoryOperand(receiver, selector, accessSize: 4));
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, left, new Immediate(16)),
            new(1, OpCode.Move, right, new Immediate(20)),
            new(2, OpCode.Phi, selector, left, right),
            load,
            new(4, OpCode.Return)]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.That(load.Operands[1], Is.TypeOf<SelectedFieldReference>());
        var selected = (SelectedFieldReference)load.Operands[1];
        Assert.Multiple(() =>
        {
            Assert.That(selected.FieldType, Is.SameAs(app.SystemTypes.SystemSingleType));
            Assert.That(selected.Choices.Select(c => c.Value), Is.EqualTo(new long[] { 16, 20 }));
            Assert.That(selected.Choices.Select(c => c.Field.Field.Name), Is.EqualTo(new[] { "radius", "corner" }));
        });
    }

    [TestCase(16, "x")]
    [TestCase(20, "y")]
    public void NativeScalarAccessInsideValueTypeResolvesNestedField(int offset, string expectedName)
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var valueType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!;
        var vector = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Vector",
            valueType, TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout);
        var x = new InjectedFieldAnalysisContext("x", app.SystemTypes.SystemSingleType,
            FieldAttributes.Public, vector, 0);
        var y = new InjectedFieldAnalysisContext("y", app.SystemTypes.SystemSingleType,
            FieldAttributes.Public, vector, 4);
        vector.Fields.Add(x);
        vector.Fields.Add(y);
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var container = new InjectedFieldAnalysisContext("position", vector, FieldAttributes.Public, owner, 16);
        owner.Fields.Add(container);
        var method = new InjectedMethodAnalysisContext(owner, "Read", app.SystemTypes.SystemVoidType,
            MethodAttributes.Static, []);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), owner);
        var result = new LocalVariable("result", new Register(null, "result"));
        var load = new Instruction(0, OpCode.Move, result, new MemoryOperand(receiver, addend: offset, accessSize: 4));
        method.ControlFlowGraph = new ISILControlFlowGraph([load, new(1, OpCode.Return)]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.That(load.Operands[1], Is.TypeOf<FieldReference>());
        var resolved = (FieldReference)load.Operands[1];
        Assert.Multiple(() =>
        {
            Assert.That(resolved.Field.Name, Is.EqualTo(expectedName));
            Assert.That(resolved.Containers, Is.EqualTo(new[] { container }));
        });
    }

    [TestCase(16, "id")]
    [TestCase(24, "prefab")]
    public void GenericEnumeratorCurrentResolvesNestedValueField(int offset, string expectedName)
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var valueType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!;
        var entry = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Entry",
            valueType, TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout);
        var id = new InjectedFieldAnalysisContext("id", app.SystemTypes.SystemStringType,
            FieldAttributes.Public, entry, 0);
        var prefab = new InjectedFieldAnalysisContext("prefab", app.SystemTypes.SystemObjectType,
            FieldAttributes.Public, entry, 8);
        entry.Fields.Add(id);
        entry.Fields.Add(prefab);
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var enumerator = new GenericInstanceTypeAnalysisContext(
            list.NestedTypes.Single(type => type.Name == "Enumerator"), [entry]);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), enumerator);
        var result = new LocalVariable("result", new Register(null, "result"));
        var load = new Instruction(0, OpCode.Move, result,
            new MemoryOperand(receiver, addend: offset, accessSize: 8));
        method.ControlFlowGraph = new ISILControlFlowGraph([load, new(1, OpCode.Return)]);

        MetadataResolver.ResolveFieldOffsets(method);

        var resolved = (FieldReference)load.Operands[1];
        Assert.Multiple(() =>
        {
            Assert.That(resolved.Field.Name, Is.EqualTo(expectedName));
            Assert.That(resolved.Containers.Single().Name, Is.EqualTo("_current"));
        });
    }

    [TestCase(16, "System.String")]
    [TestCase(24, "System.Object")]
    public void GenericEnumeratorCurrentSplitsNestedGenericPair(int offset, string expectedType)
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var pairDefinition = app.AssembliesByName["mscorlib"]
            .GetTypeByFullName("System.Collections.Generic.KeyValuePair`2")!;
        var pair = new GenericInstanceTypeAnalysisContext(pairDefinition,
            [app.SystemTypes.SystemStringType, app.SystemTypes.SystemObjectType]);
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var enumerator = new GenericInstanceTypeAnalysisContext(
            list.NestedTypes.Single(type => type.Name == "Enumerator"), [pair]);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), enumerator);
        var result = new LocalVariable("result", new Register(null, "result"));
        var load = new Instruction(0, OpCode.Move, result,
            new MemoryOperand(receiver, addend: offset, accessSize: 8));
        method.ControlFlowGraph = new ISILControlFlowGraph([load, new(1, OpCode.Return)]);

        MetadataResolver.ResolveFieldOffsets(method);

        var resolved = (FieldReference)load.Operands[1];
        Assert.Multiple(() =>
        {
            Assert.That(resolved.Field.FieldType.FullName, Is.EqualTo(expectedType));
            Assert.That(resolved.Field.DeclaringType.FullName, Does.Contain("KeyValuePair"));
            Assert.That(resolved.Containers.Single().Name, Is.EqualTo("_current"));
        });
    }

    [Test]
    public void CopiedGenericEnumeratorStackSlotResolvesNestedCurrentField()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var valueType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!;
        var entry = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Entry",
            valueType, TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout);
        entry.Fields.Add(new InjectedFieldAnalysisContext("id", app.SystemTypes.SystemStringType,
            FieldAttributes.Public, entry, 0));
        var prefab = new InjectedFieldAnalysisContext("prefab", app.SystemTypes.SystemObjectType,
            FieldAttributes.Public, entry, 8);
        entry.Fields.Add(prefab);
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var enumerator = new GenericInstanceTypeAnalysisContext(
            list.NestedTypes.Single(type => type.Name == "Enumerator"), [entry]);
        var root = new LocalVariable("root", new Register(null, "stack_-80"), enumerator);
        var samePhysicalRoot = new LocalVariable("samePhysicalRoot", new Register(null, "stack_-80", 2), enumerator);
        var fieldSlot = new LocalVariable("fieldSlot", new Register(null, "stack_-68"),
            app.SystemTypes.SystemObjectType);
        var result = new LocalVariable("result", new Register(null, "result"),
            app.SystemTypes.SystemBooleanType);
        var moved = new LocalVariable("moved", new Register(null, "moved"),
            app.SystemTypes.SystemStringType);
        var write = new Instruction(0, OpCode.Move, fieldSlot, new Immediate(0));
        var moveRead = new Instruction(1, OpCode.Move, moved, fieldSlot);
        var read = new Instruction(2, OpCode.CheckEqual, result, fieldSlot, new Immediate(0));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, [])
        {
            ControlFlowGraph = new ISILControlFlowGraph([write, moveRead, read, new(3, OpCode.Return)]),
            Locals = [root, samePhysicalRoot, fieldSlot, moved, result],
            ParameterLocals = [],
            AnalysisWarnings = [],
        };

        LocalVariables.ResolveTypesAndFields(method);

        var resolved = (FieldReference)read.Operands[1];
        Assert.Multiple(() =>
        {
            Assert.That(resolved.Local.Register.Name, Is.EqualTo(root.Register.Name));
            Assert.That(resolved.Field, Is.SameAs(prefab));
            Assert.That(resolved.Containers.Single().Name, Is.EqualTo("_current"));
            Assert.That(write.Operands[0], Is.SameAs(fieldSlot));
            Assert.That(((FieldReference)moveRead.Operands[1]).Field, Is.SameAs(prefab));
            Assert.That(moved.Type, Is.SameAs(app.SystemTypes.SystemObjectType));
        });
    }

    [TestCase(false)]
    [TestCase(true)]
    public void StaticStoragePointerSupportsDirectAndSplitClassAddress(bool splitAddress)
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "StaticStorage",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        var owner = app.SystemTypes.SystemStringType;
        var klass = new LocalVariable("klass", new Register(null, "klass"),
            new RuntimeClassTypeAnalysisContext(owner, owner.DeclaringAssembly));
        var address = new LocalVariable("address", new Register(null, "address"));
        var storage = new LocalVariable("storage", new Register(null, "storage"));
        var instructions = new List<Instruction>();
        if (splitAddress)
            instructions.Add(new Instruction(0, OpCode.Add, address, klass, new Immediate(0xB8)));
        instructions.Add(new Instruction(1, OpCode.Move, storage,
            new MemoryOperand(splitAddress ? address : klass, addend: splitAddress ? 0 : 0xB8)));
        instructions.Add(new Instruction(2, OpCode.Return));
        method.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        method.Locals = [klass, address, storage];
        method.ParameterLocals = [];

        LocalVariables.ResolveTypesAndFields(method);

        Assert.That(storage.Type, Is.TypeOf<StaticFieldStorageTypeAnalysisContext>());
        Assert.That(((StaticFieldStorageTypeAnalysisContext)storage.Type!).OwnerType, Is.SameAs(owner));
    }

    [Test]
    public void FusedStaticStorageFieldAddressResolvesWriteBarrierStore()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Statics",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("Items", app.SystemTypes.SystemObjectType,
            FieldAttributes.Public | FieldAttributes.Static, owner, 56);
        owner.Fields.Add(field);
        var method = new InjectedMethodAnalysisContext(owner, "Store", app.SystemTypes.SystemVoidType,
            MethodAttributes.Static, []);
        var klass = new LocalVariable("klass", new Register(null, "klass"),
            new RuntimeClassTypeAnalysisContext(owner, owner.DeclaringAssembly));
        var storage = new LocalVariable("storage", new Register(null, "storage"));
        var address = new LocalVariable("address", new Register(null, "address"));
        var value = new LocalVariable("value", new Register(null, "value"), app.SystemTypes.SystemObjectType);
        var store = new Instruction(2, OpCode.Move, new MemoryOperand(address), value);
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, storage, new MemoryOperand(klass, addend: 0xB8)),
            new(1, OpCode.Add, address, storage, new Immediate(56)),
            store,
            new(3, OpCode.Return)]);
        method.Locals = [klass, storage, address, value];
        method.ParameterLocals = [];

        LocalVariables.ResolveTypesAndFields(method);

        Assert.That(store.Operands[0], Is.TypeOf<FieldReference>());
        Assert.That(((FieldReference)store.Operands[0]).Field, Is.SameAs(field));
    }

    [Test]
    public void StaticGenericFieldsUseStorageOffsetsInsteadOfZeroedMetadataOffsets()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Holder`1",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var parameter = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR, 0, owner);
        owner.GenericParameters.Add(parameter);
        var instance = owner.InjectFieldContext("Instance", parameter, FieldAttributes.Public | FieldAttributes.Static);
        var initialized = owner.InjectFieldContext("Initialized", app.SystemTypes.SystemBooleanType,
            FieldAttributes.Public | FieldAttributes.Static);
        var callback = owner.InjectFieldContext("Callback", app.SystemTypes.SystemObjectType,
            FieldAttributes.Public | FieldAttributes.Static);

        Assert.Multiple(() =>
        {
            Assert.That(GenericInstanceFieldLayout.FindStaticFieldAtOffset(owner, 0), Is.SameAs(instance));
            Assert.That(GenericInstanceFieldLayout.FindStaticFieldAtOffset(owner, 8), Is.SameAs(initialized));
            Assert.That(GenericInstanceFieldLayout.FindStaticFieldAtOffset(owner, 16), Is.SameAs(callback));
        });
    }

    [Test]
    public void GenericDerivedLayoutStartsAfterInheritedInstanceFields()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = app.AssembliesByName["mscorlib"];
        var baseType = new InjectedTypeAnalysisContext(assembly, "Tests", "Base",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        baseType.Fields.Add(new InjectedFieldAnalysisContext("cached", app.SystemTypes.SystemObjectType,
            FieldAttributes.Public, baseType, 16));
        var derived = new InjectedTypeAnalysisContext(assembly, "Tests", "Derived`1", baseType,
            TypeAttributes.Public);
        derived.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0,
            Il2CppTypeEnum.IL2CPP_TYPE_VAR, 0, derived));
        var value = derived.InjectFieldContext("value", app.SystemTypes.SystemObjectType, FieldAttributes.Public);

        Assert.That(GenericInstanceFieldLayout.FindFieldAtOffset(derived, 24), Is.SameAs(value));
    }

    [Test]
    public void GenericDerivedLayoutUsesFieldsFromGenericInstanceBase()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = app.AssembliesByName["mscorlib"];
        var baseType = new InjectedTypeAnalysisContext(assembly, "Tests", "Base`1",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        baseType.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0,
            Il2CppTypeEnum.IL2CPP_TYPE_VAR, 0, baseType));
        baseType.InjectFieldContext("cached", app.SystemTypes.SystemObjectType, FieldAttributes.Public);
        var derived = new InjectedTypeAnalysisContext(assembly, "Tests", "Derived`1",
            new GenericInstanceTypeAnalysisContext(baseType, [app.SystemTypes.SystemObjectType]),
            TypeAttributes.Public);
        derived.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0,
            Il2CppTypeEnum.IL2CPP_TYPE_VAR, 0, derived));
        var value = derived.InjectFieldContext("value", app.SystemTypes.SystemObjectType, FieldAttributes.Public);

        Assert.That(GenericInstanceFieldLayout.FindFieldAtOffset(derived, 24), Is.SameAs(value));
    }

    [Test]
    public void UnusedValueTypeArgumentDoesNotBlockStableGenericLayout()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = app.AssembliesByName["mscorlib"];
        var definition = new InjectedTypeAnalysisContext(assembly, "Tests", "Holder`1",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        definition.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0,
            Il2CppTypeEnum.IL2CPP_TYPE_VAR, 0, definition));
        var enumType = new InjectedTypeAnalysisContext(assembly, "Tests", "Mode",
            assembly.GetTypeByFullName("System.Enum"), TypeAttributes.Public | TypeAttributes.Sealed);
        var erasedNestedEnum = new GenericInstanceTypeAnalysisContext(enumType, [app.SystemTypes.SystemInt32Type])
        {
            OverrideBaseType = app.SystemTypes.SystemObjectType
        };
        definition.InjectFieldContext("mode", erasedNestedEnum, FieldAttributes.Public);
        var stable = definition.InjectFieldContext("stable", app.SystemTypes.SystemObjectType,
            FieldAttributes.Public);
        var instance = new GenericInstanceTypeAnalysisContext(definition, [app.SystemTypes.SystemInt32Type]);

        Assert.That(MetadataResolver.FindInstanceFieldAtOffset(instance, 24), Is.SameAs(stable));
    }

    [Test]
    public void NonGenericDerivedTypeFindsFieldInGenericBaseLayout()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = app.AssembliesByName["mscorlib"];
        var baseType = new InjectedTypeAnalysisContext(assembly, "Tests", "Base`1",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        baseType.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0,
            Il2CppTypeEnum.IL2CPP_TYPE_VAR, 0, baseType));
        var inherited = baseType.InjectFieldContext("inherited", app.SystemTypes.SystemObjectType,
            FieldAttributes.Public);
        var derived = new InjectedTypeAnalysisContext(assembly, "Tests", "Derived",
            new GenericInstanceTypeAnalysisContext(baseType, [app.SystemTypes.SystemObjectType]),
            TypeAttributes.Public);

        var resolved = MetadataResolver.FindInstanceFieldAtOffset(derived, 16);
        Assert.That(resolved, Is.TypeOf<ConcreteGenericFieldAnalysisContext>());
        Assert.That(((ConcreteGenericFieldAnalysisContext)resolved!).BaseFieldContext, Is.SameAs(inherited));
    }
}
