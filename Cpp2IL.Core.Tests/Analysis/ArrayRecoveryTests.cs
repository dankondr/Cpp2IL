using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ArrayRecoveryTests
{
    [Test]
    public void ResolvesFieldThroughMistypedObjectAddressAlias()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("value", app.SystemTypes.SystemObjectType,
            FieldAttributes.Public, ownerType, 24);
        ownerType.Fields.Add(field);
        var owner = new LocalVariable("owner", new Register(null, "owner"), ownerType);
        var address = new LocalVariable("address", new Register(null, "address"), app.SystemTypes.SystemInt32Type);
        var result = new LocalVariable("result", new Register(null, "result"));
        var load = new Instruction(1, OpCode.Move, result, new MemoryOperand(address, accessSize: 8));
        var method = new InjectedMethodAnalysisContext(ownerType, "Read",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Add, address, owner, new Immediate(24)), load, new(2, OpCode.Return)]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.That(load.Operands[1], Is.TypeOf<FieldReference>());
        Assert.That(((FieldReference)load.Operands[1]).Field, Is.SameAs(field));
    }

    [Test]
    public void RecoversObjectValueFieldAddressDespiteWrongDestinationType()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("value", app.SystemTypes.SystemSingleType,
            FieldAttributes.Public, ownerType, 24);
        ownerType.Fields.Add(field);
        var owner = new LocalVariable("owner", new Register(null, "owner"), ownerType);
        var address = new LocalVariable("address", new Register(null, "address"), app.SystemTypes.SystemSingleType);
        var loaded = new LocalVariable("loaded", new Register(null, "loaded"));
        var add = new Instruction(0, OpCode.Add, address, owner, new Immediate(24));
        var call = new Instruction(1, OpCode.CallVoid, new StringLiteral("consume"), address);
        var load = new Instruction(2, OpCode.Move, loaded, new MemoryOperand(address, accessSize: 4));
        var method = new InjectedMethodAnalysisContext(ownerType, "Read",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        method.ControlFlowGraph = new ISILControlFlowGraph([add, call, load, new(3, OpCode.Return)]);

        ArrayRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(add.OpCode, Is.EqualTo(OpCode.Nop));
            Assert.That(call.Operands[1], Is.TypeOf<AddressOf>());
            Assert.That(((FieldReference)((AddressOf)call.Operands[1]).Target).Field, Is.SameAs(field));
            Assert.That(load.Operands[1], Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)load.Operands[1]).Field, Is.SameAs(field));
        });
    }

    [Test]
    public void RecoversObjectFieldAddressWithUntypedDestination()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("items", app.SystemTypes.SystemObjectType,
            FieldAttributes.Public, ownerType, 56);
        ownerType.Fields.Add(field);
        var owner = new LocalVariable("owner", new Register(null, "owner"), ownerType);
        var address = new LocalVariable("address", new Register(null, "address"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var add = new Instruction(0, OpCode.Add, address, owner, new Immediate(56));
        var load = new Instruction(1, OpCode.Move, result, new MemoryOperand(address, accessSize: 8));
        var method = new InjectedMethodAnalysisContext(ownerType, "Read",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        method.ControlFlowGraph = new ISILControlFlowGraph([add, load, new(2, OpCode.Return)]);

        ArrayRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(add.OpCode, Is.EqualTo(OpCode.Nop));
            Assert.That(load.Operands[1], Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)load.Operands[1]).Field, Is.SameAs(field));
        });
    }

    [Test]
    public void CollapsesCopiedFieldAddressBeforeDereference()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("items", app.SystemTypes.SystemObjectType,
            FieldAttributes.Public, ownerType, 56);
        ownerType.Fields.Add(field);
        var owner = new LocalVariable("owner", new Register(null, "owner"), ownerType);
        var address = new LocalVariable("address", new Register(null, "address"));
        var alias = new LocalVariable("alias", new Register(null, "alias"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var add = new Instruction(0, OpCode.Add, address, owner, new Immediate(56));
        var copy = new Instruction(1, OpCode.Move, alias, address);
        var load = new Instruction(2, OpCode.Move, result, new MemoryOperand(alias, accessSize: 8));
        var method = new InjectedMethodAnalysisContext(ownerType, "Read",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        method.ControlFlowGraph = new ISILControlFlowGraph([add, copy, load, new(3, OpCode.Return)]);

        ArrayRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(add.OpCode, Is.EqualTo(OpCode.Nop));
            Assert.That(copy.OpCode, Is.EqualTo(OpCode.Nop));
            Assert.That(load.Operands[1], Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)load.Operands[1]).Field, Is.SameAs(field));
        });
    }

    [Test]
    public void RecoversNestedObjectValueFieldAddress()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var valueType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!;
        var pairType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Pair",
            valueType, TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout);
        var first = new InjectedFieldAnalysisContext("first", app.SystemTypes.SystemSingleType,
            FieldAttributes.Public, pairType, 0);
        var second = new InjectedFieldAnalysisContext("second", app.SystemTypes.SystemSingleType,
            FieldAttributes.Public, pairType, 4);
        pairType.Fields.Add(first);
        pairType.Fields.Add(second);
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var pair = new InjectedFieldAnalysisContext("pair", pairType, FieldAttributes.Public, ownerType, 24);
        ownerType.Fields.Add(pair);
        var owner = new LocalVariable("owner", new Register(null, "owner"), ownerType);
        var address = new LocalVariable("address", new Register(null, "address"), app.SystemTypes.SystemSingleType);
        var add = new Instruction(0, OpCode.Add, address, owner, new Immediate(28));
        var call = new Instruction(1, OpCode.CallVoid, new StringLiteral("consume"), address);
        var method = new InjectedMethodAnalysisContext(ownerType, "Read",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        method.ControlFlowGraph = new ISILControlFlowGraph([add, call, new(2, OpCode.Return)]);

        ArrayRecovery.Run(method);

        var fieldAddress = (FieldReference)((AddressOf)call.Operands[1]).Target;
        Assert.Multiple(() =>
        {
            Assert.That(add.OpCode, Is.EqualTo(OpCode.Nop));
            Assert.That(fieldAddress.Field, Is.SameAs(second));
            Assert.That(fieldAddress.Containers, Is.EqualTo(new[] { pair }));
        });
    }

    [Test]
    public void RecoversReferenceArrayStoreFromPairedByteOffsetInduction()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var arrayType = new SzArrayTypeAnalysisContext(app.SystemTypes.SystemStringType);
        var array = new LocalVariable("array", new Register(null, "array"), arrayType);
        var index = new LocalVariable("index", new Register(null, "index"));
        var offset = new LocalVariable("offset", new Register(null, "offset"), app.SystemTypes.SystemInt32Type);
        var value = new LocalVariable("value", new Register(null, "value"), app.SystemTypes.SystemStringType);
        var condition = new LocalVariable("condition", new Register(null, "condition"), app.SystemTypes.SystemBooleanType);
        var store = new Instruction(2, OpCode.Move,
            new MemoryOperand(array, offset, accessSize: 8), value);
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fill",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, offset, new Immediate(32)),
            new(1, OpCode.CheckLess, condition, index, new ArrayLength(array)),
            store,
            new(3, OpCode.Add, index, index, new Immediate(1)),
            new(4, OpCode.Add, offset, offset, new Immediate(8)),
            new(5, OpCode.Return)]);
        method.ParameterLocals = [];

        ArrayRecovery.Run(method);

        Assert.That(store.Operands[0], Is.TypeOf<ArrayAccess>());
        Assert.That(((ArrayAccess)store.Operands[0]).Index, Is.SameAs(index));
    }

    [Test]
    public void RecoversElementThroughScaledPointerAdd()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var arrayType = new SzArrayTypeAnalysisContext(app.SystemTypes.SystemStringType);
        var array = new LocalVariable("array", new Register(null, "array"), arrayType);
        var index = new LocalVariable("index", new Register(null, "index"), app.SystemTypes.SystemInt32Type);
        var extended = new LocalVariable("extended", new Register(null, "extended"));
        var scaled = new LocalVariable("scaled", new Register(null, "scaled"));
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var load = new Instruction(4, OpCode.Move, result, new MemoryOperand(pointer, addend: 32, accessSize: 8));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.SignExtend32, extended, index),
            new(1, OpCode.ShiftLeft, scaled, extended, new Immediate(3)),
            new(2, OpCode.Add, pointer, array, scaled),
            load,
            new(5, OpCode.Return)]);

        ArrayRecovery.Run(method);

        Assert.That(load.Operands[1], Is.TypeOf<ArrayAccess>());
        var access = (ArrayAccess)load.Operands[1];
        Assert.That(access.Array, Is.SameAs(array));
        Assert.That(access.Index, Is.SameAs(index));
    }

    [Test]
    public void RecoversStructArrayPointerWalkerFields()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var valueType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!;
        var elementType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Pair",
            valueType, TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout);
        var first = new InjectedFieldAnalysisContext("first", app.SystemTypes.SystemInt32Type,
            FieldAttributes.Public, elementType, 0);
        var second = new InjectedFieldAnalysisContext("second", app.SystemTypes.SystemInt32Type,
            FieldAttributes.Public, elementType, 4);
        elementType.Fields.Add(first);
        elementType.Fields.Add(second);
        var array = new LocalVariable("array", new Register(null, "array"), new SzArrayTypeAnalysisContext(elementType));
        var index = new LocalVariable("index", new Register(null, "index"), app.SystemTypes.SystemInt32Type);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"), app.SystemTypes.SystemInt32Type);
        var loaded = new LocalVariable("loaded", new Register(null, "loaded"));
        var condition = new LocalVariable("condition", new Register(null, "condition"), app.SystemTypes.SystemBooleanType);
        var length = new ArrayLength(array);
        var initial = new Instruction(1, OpCode.Add, pointer, array, new Immediate(36));
        var load = new Instruction(3, OpCode.Move, loaded, new MemoryOperand(pointer, addend: -4, accessSize: 4));
        var call = new Instruction(4, OpCode.CallVoid, new StringLiteral("consume"), pointer);
        var incrementPointer = new Instruction(5, OpCode.Add, pointer, pointer, new Immediate(8));
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Walk",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, index, new Immediate(0)),
            initial,
            new(2, OpCode.CheckLess, condition, index, length),
            load,
            call,
            incrementPointer,
            new(6, OpCode.Add, index, index, new Immediate(1)),
            new(7, OpCode.Return)]);

        ArrayRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(initial.OpCode, Is.EqualTo(OpCode.Nop));
            Assert.That(incrementPointer.OpCode, Is.EqualTo(OpCode.Nop));
            Assert.That(load.Operands[1], Is.TypeOf<ArrayElementFieldReference>());
            Assert.That(((ArrayElementFieldReference)load.Operands[1]).Field, Is.SameAs(first));
            Assert.That(call.Operands[1], Is.TypeOf<AddressOf>());
            Assert.That(((AddressOf)call.Operands[1]).Target, Is.TypeOf<ArrayElementFieldReference>());
            Assert.That(((ArrayElementFieldReference)((AddressOf)call.Operands[1]).Target).Field, Is.SameAs(second));
        });
    }
}
