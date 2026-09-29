using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: unmanaged loads through untyped base registers whose SSA
// defs prove they hold a managed address (castle-recovery#140).
//   * [&t + 0] is a plain `t` read when t is not a wide struct.
//   * [&t + k] reaches the sibling frame slot at that exact fp offset.
//   * [&f + k] reaches the field of f's host at f's absolute offset + k.
//   * [this + k] on a struct method is interior `this` addressing (ldarg.0 = &T).
//   * A local loaded from a field/element/cast carries that value's type, so
//     [v + off] is a field read once the producer type is known.
// Sites whose storage cannot be proven keep their MemoryOperand.
public class AddressedStorageReadTests
{
    private static InjectedMethodAnalysisContext Method(TypeAnalysisContext ownerType,
        ApplicationAnalysisContext app, List<Instruction> instructions,
        List<LocalVariable>? locals = null)
    {
        var method = new InjectedMethodAnalysisContext(ownerType, "Read",
            app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        method.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        if (locals != null)
            method.Locals = locals;
        return method;
    }

    [Test]
    public void DereferenceOfSlotAddressReadsLocal()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var slot = new LocalVariable("cell", new Register(null, "stack_-98"),
            app.SystemTypes.SystemObjectType);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var result = new LocalVariable("result", new Register(null, "result"));
        // pointer = &cell; result = *pointer  ==  result = cell
        var load = new Instruction(1, OpCode.Move, result,
            new MemoryOperand(pointer, addend: 0, accessSize: 8));
        var method = Method(ownerType, app, [
            new(0, OpCode.Move, pointer, new AddressOf(slot)), load, new(2, OpCode.Return)],
            [slot, pointer, result]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.That(load.Operands[1], Is.SameAs(slot),
            () => load.Operands[1]?.ToString() ?? "<null>");
    }

    [Test]
    public void DereferenceOfUntypedSlotAddressReadsLocal()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var slot = new LocalVariable("cell", new Register(null, "stack_-98"));
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var load = new Instruction(1, OpCode.Move, result,
            new MemoryOperand(pointer, addend: 0, accessSize: 8));
        var method = Method(ownerType, app, [
            new(0, OpCode.Move, pointer, new AddressOf(slot)), load, new(2, OpCode.Return)],
            [slot, pointer, result]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.That(load.Operands[1], Is.SameAs(slot),
            () => load.Operands[1]?.ToString() ?? "<null>");
    }

    [Test]
    public void SubPointerDereferenceOfSlotAddressKeepsMemoryOperand()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var slot = new LocalVariable("cell", new Register(null, "stack_-98"));
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var result = new LocalVariable("result", new Register(null, "result"));
        // A 4-byte read through &cell is not the 8-byte slot: no proven meaning.
        var load = new Instruction(1, OpCode.Move, result,
            new MemoryOperand(pointer, addend: 0, accessSize: 4));
        var method = Method(ownerType, app, [
            new(0, OpCode.Move, pointer, new AddressOf(slot)), load, new(2, OpCode.Return)],
            [slot, pointer, result]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>(),
            () => load.Operands[1]?.ToString() ?? "<null>");
    }

    [Test]
    public void DisplacedSlotAddressReadsSiblingFrameSlot()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var slot = new LocalVariable("cell", new Register(null, "stack_-98"));
        var sibling = new LocalVariable("sibling", new Register(null, "stack_-90"),
            app.SystemTypes.SystemObjectType);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var result = new LocalVariable("result", new Register(null, "result"));
        // &stack_-98 + 8 addresses stack_-90; the load reads that slot.
        var load = new Instruction(1, OpCode.Move, result,
            new MemoryOperand(pointer, addend: 8, accessSize: 8));
        var method = Method(ownerType, app, [
            new(0, OpCode.Move, pointer, new AddressOf(slot)), load, new(2, OpCode.Return)],
            [slot, sibling, pointer, result]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.That(load.Operands[1], Is.SameAs(sibling),
            () => load.Operands[1]?.ToString() ?? "<null>");
    }

    [Test]
    public void DisplacedSlotAddressWithoutSiblingKeepsMemoryOperand()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var slot = new LocalVariable("cell", new Register(null, "stack_-98"));
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var result = new LocalVariable("result", new Register(null, "result"));
        // &stack_-98 + 8 hits padding - no stack_-90 local exists.
        var load = new Instruction(1, OpCode.Move, result,
            new MemoryOperand(pointer, addend: 8, accessSize: 8));
        var method = Method(ownerType, app, [
            new(0, OpCode.Move, pointer, new AddressOf(slot)), load, new(2, OpCode.Return)],
            [slot, pointer, result]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>(),
            () => load.Operands[1]?.ToString() ?? "<null>");
    }

    [Test]
    public void SubtractedSlotAddressAliasReadsSiblingFrameSlot()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var slot = new LocalVariable("cell", new Register(null, "stack_-98"));
        var sibling = new LocalVariable("sibling", new Register(null, "stack_-90"),
            app.SystemTypes.SystemObjectType);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var result = new LocalVariable("result", new Register(null, "result"));
        // pointer = &stack_-98 - 16; [pointer + 24] is stack_-98 - 16 + 24 = stack_-90.
        var load = new Instruction(1, OpCode.Move, result,
            new MemoryOperand(pointer, addend: 24, accessSize: 8));
        var method = Method(ownerType, app, [
            new(0, OpCode.Subtract, pointer, new AddressOf(slot), new Immediate(16)),
            load, new(2, OpCode.Return)],
            [slot, sibling, pointer, result]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.That(load.Operands[1], Is.SameAs(sibling),
            () => load.Operands[1]?.ToString() ?? "<null>");
    }

    [Test]
    public void DisplacedVersionedSlotAddressReadsSingleVersionSibling()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var slot = new LocalVariable("cell", new Register(null, "stack_-98", version: 2));
        // stack_-90 is versioned too, but is the only local naming that cell: the
        // read is unambiguous because the cell has a single SSA version.
        var sibling = new LocalVariable("sibling", new Register(null, "stack_-90", version: 1),
            app.SystemTypes.SystemObjectType);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var load = new Instruction(1, OpCode.Move, result,
            new MemoryOperand(pointer, addend: 8, accessSize: 8));
        var method = Method(ownerType, app, [
            new(0, OpCode.Move, pointer, new AddressOf(slot)), load, new(2, OpCode.Return)],
            [slot, sibling, pointer, result]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.That(load.Operands[1], Is.SameAs(sibling),
            () => load.Operands[1]?.ToString() ?? "<null>");
    }

    [Test]
    public void MultiVersionSiblingKeepsMemoryOperand()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var slot = new LocalVariable("cell", new Register(null, "stack_-98", version: 2));
        // stack_-90 has two SSA versions; the address cannot pick the live one.
        var v1 = new LocalVariable("siblingV1", new Register(null, "stack_-90", version: 1),
            app.SystemTypes.SystemObjectType);
        var v2 = new LocalVariable("siblingV2", new Register(null, "stack_-90", version: 2),
            app.SystemTypes.SystemObjectType);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var load = new Instruction(1, OpCode.Move, result,
            new MemoryOperand(pointer, addend: 8, accessSize: 8));
        var method = Method(ownerType, app, [
            new(0, OpCode.Move, pointer, new AddressOf(slot)), load, new(2, OpCode.Return)],
            [slot, v1, v2, pointer, result]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>(),
            () => load.Operands[1]?.ToString() ?? "<null>");
    }

    [Test]
    public void FieldAddressOffsetReachesSiblingHostField()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var first = new InjectedFieldAnalysisContext("first", app.SystemTypes.SystemObjectType,
            FieldAttributes.Public, ownerType, 16);
        var second = new InjectedFieldAnalysisContext("second", app.SystemTypes.SystemObjectType,
            FieldAttributes.Public, ownerType, 24);
        ownerType.Fields.Add(first);
        ownerType.Fields.Add(second);
        var owner = new LocalVariable("owner", new Register(null, "owner"), ownerType);
        var fieldRef = new FieldReference(first, owner, 16);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var result = new LocalVariable("result", new Register(null, "result"));
        // &owner.first + 8 reaches owner.second.
        var load = new Instruction(1, OpCode.Move, result,
            new MemoryOperand(pointer, addend: 8, accessSize: 8));
        var method = Method(ownerType, app, [
            new(0, OpCode.Move, pointer, new AddressOf(fieldRef)), load, new(2, OpCode.Return)],
            [owner, pointer, result]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.Multiple(() =>
        {
            Assert.That(load.Operands[1], Is.TypeOf<FieldReference>(),
                () => load.Operands[1]?.ToString() ?? "<null>");
            var reference = (FieldReference)load.Operands[1];
            Assert.That(reference.Field, Is.SameAs(second));
            Assert.That(reference.Local, Is.SameAs(owner));
        });
    }

    [Test]
    public void FieldAddressZeroDereferenceReadsField()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("value", app.SystemTypes.SystemObjectType,
            FieldAttributes.Public, ownerType, 16);
        ownerType.Fields.Add(field);
        var owner = new LocalVariable("owner", new Register(null, "owner"), ownerType);
        var fieldRef = new FieldReference(field, owner, 16);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var result = new LocalVariable("result", new Register(null, "result"));
        // *(&owner.value) is owner.value itself.
        var load = new Instruction(1, OpCode.Move, result,
            new MemoryOperand(pointer, addend: 0, accessSize: 8));
        var method = Method(ownerType, app, [
            new(0, OpCode.Move, pointer, new AddressOf(fieldRef)), load, new(2, OpCode.Return)],
            [owner, pointer, result]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.That(load.Operands[1], Is.SameAs(fieldRef),
            () => load.Operands[1]?.ToString() ?? "<null>");
    }

    [Test]
    public void StructThisAliasReadsInteriorField()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemValueTypeType, TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("inner", app.SystemTypes.SystemInt32Type,
            FieldAttributes.Public, ownerType, 8);
        ownerType.Fields.Add(field);
        var thisLocal = new LocalVariable("this", new Register(null, "this"), ownerType) { IsThis = true };
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var result = new LocalVariable("result", new Register(null, "result"));
        // ldarg.0 on a struct is &T: [this + 8] reads this.inner.
        var load = new Instruction(1, OpCode.Move, result,
            new MemoryOperand(pointer, addend: 0, accessSize: 4));
        var method = Method(ownerType, app, [
            new(0, OpCode.Add, pointer, thisLocal, new Immediate(8)), load, new(2, OpCode.Return)],
            [thisLocal, pointer, result]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.Multiple(() =>
        {
            Assert.That(load.Operands[1], Is.TypeOf<FieldReference>(),
                () => load.Operands[1]?.ToString() ?? "<null>");
            Assert.That(((FieldReference)load.Operands[1]).Field, Is.SameAs(field));
        });
    }

    [Test]
    public void FieldLoadResultTypesBaseForNextLoad()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var innerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Inner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var outerField = new InjectedFieldAnalysisContext("inner", innerType,
            FieldAttributes.Public, ownerType, 16);
        var innerField = new InjectedFieldAnalysisContext("value", app.SystemTypes.SystemInt32Type,
            FieldAttributes.Public, innerType, 8);
        ownerType.Fields.Add(outerField);
        innerType.Fields.Add(innerField);
        var owner = new LocalVariable("owner", new Register(null, "owner"), ownerType);
        var fieldRef = new FieldReference(outerField, owner, 16);
        // type propagation declares value Inner: ldloc supplies the `ref Inner`
        // base ldfld needs, so the produced reference emits legally.
        var value = new LocalVariable("value", new Register(null, "value"), innerType);
        var result = new LocalVariable("result", new Register(null, "result"));
        // value = owner.inner; [value + 8] is owner.inner.value.
        var load = new Instruction(1, OpCode.Move, result,
            new MemoryOperand(value, addend: 8, accessSize: 4));
        var method = Method(ownerType, app, [
            new(0, OpCode.Move, value, fieldRef), load, new(2, OpCode.Return)],
            [owner, value, result]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.Multiple(() =>
        {
            Assert.That(load.Operands[1], Is.TypeOf<FieldReference>(),
                () => load.Operands[1]?.ToString() ?? "<null>");
            var reference = (FieldReference)load.Operands[1];
            Assert.That(reference.Field, Is.SameAs(innerField));
            Assert.That(reference.Local, Is.SameAs(value));
        });
    }

    [Test]
    public void FieldLoadResultTypesBaseForNextLoadWhenSlotUntyped()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var innerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Inner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var outerField = new InjectedFieldAnalysisContext("inner", innerType,
            FieldAttributes.Public, ownerType, 16);
        var innerField = new InjectedFieldAnalysisContext("value", app.SystemTypes.SystemInt32Type,
            FieldAttributes.Public, innerType, 8);
        ownerType.Fields.Add(outerField);
        innerType.Fields.Add(innerField);
        var owner = new LocalVariable("owner", new Register(null, "owner"), ownerType);
        var fieldRef = new FieldReference(outerField, owner, 16);
        // The slot stays unannotated - the `value = owner.inner` producer alone
        // proves `value` carries Inner, so [value + 8] is still owner.inner.value.
        var value = new LocalVariable("value", new Register(null, "value"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var load = new Instruction(1, OpCode.Move, result,
            new MemoryOperand(value, addend: 8, accessSize: 4));
        var method = Method(ownerType, app, [
            new(0, OpCode.Move, value, fieldRef), load, new(2, OpCode.Return)],
            [owner, value, result]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.Multiple(() =>
        {
            Assert.That(load.Operands[1], Is.TypeOf<FieldReference>(),
                () => load.Operands[1]?.ToString() ?? "<null>");
            var reference = (FieldReference)load.Operands[1];
            Assert.That(reference.Field, Is.SameAs(innerField));
            Assert.That(reference.Local, Is.SameAs(value));
        });
    }

    [Test]
    public void FieldAddressOffsetOnObjectOwnerKeepsMemoryOperand()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemValueTypeType, TypeAttributes.Public);
        var first = new InjectedFieldAnalysisContext("first", app.SystemTypes.SystemInt32Type,
            FieldAttributes.Public, ownerType, 8);
        var second = new InjectedFieldAnalysisContext("second", app.SystemTypes.SystemInt32Type,
            FieldAttributes.Public, ownerType, 12);
        ownerType.Fields.Add(first);
        ownerType.Fields.Add(second);
        // The field's owner is declared `object` (its Owner-typed value reaches it
        // through a cast): a produced FieldReference would push `ref object` where
        // stfld/ldfld needs `&Owner` - invalid IL. Keep the diagnostic.
        var source = new LocalVariable("source", new Register(null, "source"),
            app.SystemTypes.SystemObjectType);
        var owner = new LocalVariable("owner", new Register(null, "owner"),
            app.SystemTypes.SystemObjectType);
        var fieldRef = new FieldReference(first, owner, 8);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var load = new Instruction(2, OpCode.Move, result,
            new MemoryOperand(pointer, addend: 4, accessSize: 4));
        var method = Method(ownerType, app, [
            new(0, OpCode.Move, owner, new ReferenceCast(source, ownerType)),
            new(1, OpCode.Move, pointer, new AddressOf(fieldRef)), load, new(3, OpCode.Return)],
            [source, owner, pointer, result]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>(),
            () => load.Operands[1]?.ToString() ?? "<null>");
    }

    [Test]
    public void SlotAddressInMemorySetKeepsMemoryOperand()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var slot = new LocalVariable("cell", new Register(null, "stack_-98"),
            app.SystemTypes.SystemObjectType);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var fill = new LocalVariable("fill", new Register(null, "fill"),
            app.SystemTypes.SystemInt32Type);
        var count = new LocalVariable("count", new Register(null, "count"),
            app.SystemTypes.SystemInt32Type);
        // initblk wants an address on the stack; `cell` is an object reference -
        // memset(cell) is invalid IL, so the site keeps its diagnostic.
        var memset = new Instruction(1, OpCode.MemorySet,
            new MemoryOperand(pointer, addend: 0, accessSize: 8), fill, count);
        var method = Method(ownerType, app, [
            new(0, OpCode.Move, pointer, new AddressOf(slot)), memset, new(2, OpCode.Return)],
            [slot, pointer, fill, count]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.That(memset.Operands[0], Is.TypeOf<MemoryOperand>(),
            () => memset.Operands[0]?.ToString() ?? "<null>");
    }

    [Test]
    public void UnprovenBaseKeepsMemoryOperand()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var opaque = new LocalVariable("opaque", new Register(null, "opaque"));
        var result = new LocalVariable("result", new Register(null, "result"));
        var load = new Instruction(1, OpCode.Move, result,
            new MemoryOperand(opaque, addend: 8, accessSize: 8));
        var method = Method(ownerType, app, [
            new(0, OpCode.Move, opaque, new Immediate(0x1234)), load, new(2, OpCode.Return)],
            [opaque, result]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.That(load.Operands[1], Is.TypeOf<MemoryOperand>(),
            () => load.Operands[1]?.ToString() ?? "<null>");
    }

    // Copy propagation forwards `x := y` into a FieldReference receiver slot, but the
    // receiver feeds ldfld/stfld's type contract: the emitted `&T` must be able to
    // supply the field's declaring type. The lane-split pass builds FieldReference
    // receivers from `Move`-copied scalars whose slot types do not always satisfy
    // that contract (`&v1422 @ Vector2` cannot feed `ldfld Vector3::x`).
    [Test]
    public void CopyPropagationKeepsFieldReceiverWhoseSlotTypeCannotSupplyHost()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var host = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Host",
            app.SystemTypes.SystemValueTypeType, TypeAttributes.Public);
        var other = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Other",
            app.SystemTypes.SystemValueTypeType, TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("lane", app.SystemTypes.SystemSingleType,
            FieldAttributes.Public, host, offset: 0);
        var x = new LocalVariable("x", new Register(null, "x")) { Type = host };
        var y = new LocalVariable("y", new Register(null, "y")) { Type = other };
        var result = new LocalVariable("result", new Register(null, "result"));
        var copy = new Instruction(0, OpCode.Move, x, y);
        var receiver = new FieldReference(field, x, offset: 0);
        var method = Method(ownerType, app, [
            copy, new(1, OpCode.Move, result, receiver),
            new(2, OpCode.CallVoid, Str("sink"), result), new(3, OpCode.Return)],
            [x, y, result]);

        Simplifier.Simplify(method);

        Assert.Multiple(() =>
        {
            Assert.That(receiver.Local, Is.SameAs(x),
                "a slot that cannot supply the field's declaring type keeps the receiver");
            Assert.That(copy.OpCode, Is.EqualTo(OpCode.Move),
                "the copy must survive while the receiver still reads its destination");
            Assert.That(method.Locals, Has.Member(x));
        });
    }

    [Test]
    public void CopyPropagationForwardsFieldReceiverWhoseSlotTypeSuppliesHost()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var host = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Host",
            app.SystemTypes.SystemValueTypeType, TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("lane", app.SystemTypes.SystemSingleType,
            FieldAttributes.Public, host, offset: 0);
        var x = new LocalVariable("x", new Register(null, "x")) { Type = host };
        var y = new LocalVariable("y", new Register(null, "y")) { Type = host };
        var result = new LocalVariable("result", new Register(null, "result"));
        var copy = new Instruction(0, OpCode.Move, x, y);
        var receiver = new FieldReference(field, x, offset: 0);
        var method = Method(ownerType, app, [
            copy, new(1, OpCode.Move, result, receiver),
            new(2, OpCode.CallVoid, Str("sink"), result), new(3, OpCode.Return)],
            [x, y, result]);

        Simplifier.Simplify(method);

        Assert.Multiple(() =>
        {
            Assert.That(receiver.Local, Is.SameAs(y),
                "a compatible slot type forwards into the receiver");
            Assert.That(copy.OpCode, Is.EqualTo(OpCode.Nop),
                "the dead copy is dropped once the receiver no longer reads it");
        });
    }

    // The same receiver contract binds call operands: an instance method's `this`
    // emits `readonly &T` for a value-type callee, so a forwarded local whose slot
    // type is not T makes the emitted call unverifiable. A byref parameter is
    // invariant the same way (`in Vector3` needs exactly `&Vector3`).
    [Test]
    public void CopyPropagationKeepsCallReceiverWhoseSlotTypeCannotSupplyDeclaringType()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var host = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Host",
            app.SystemTypes.SystemValueTypeType, TypeAttributes.Public);
        var other = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Other",
            app.SystemTypes.SystemValueTypeType, TypeAttributes.Public);
        var callee = new InjectedMethodAnalysisContext(host, "Length",
            app.SystemTypes.SystemSingleType, MethodAttributes.Public, []);
        var x = new LocalVariable("x", new Register(null, "x")) { Type = host };
        var y = new LocalVariable("y", new Register(null, "y")) { Type = other };
        var copy = new Instruction(0, OpCode.Move, x, y);
        var call = new Instruction(1, OpCode.CallVoid, callee, x);
        var method = Method(ownerType, app, [copy, call, new(2, OpCode.Return)], [x, y]);

        Simplifier.Simplify(method);

        Assert.Multiple(() =>
        {
            Assert.That(call.Operands[1], Is.SameAs(x),
                "a slot that cannot supply the callee's declaring type keeps the `this` operand");
            Assert.That(copy.OpCode, Is.EqualTo(OpCode.Move),
                "the copy must survive while `this` still reads its destination");
        });
    }

    [Test]
    public void CopyPropagationForwardsCallReceiverWhoseSlotTypeSuppliesDeclaringType()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var host = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Host",
            app.SystemTypes.SystemValueTypeType, TypeAttributes.Public);
        var callee = new InjectedMethodAnalysisContext(host, "Length",
            app.SystemTypes.SystemSingleType, MethodAttributes.Public, []);
        var x = new LocalVariable("x", new Register(null, "x")) { Type = host };
        var y = new LocalVariable("y", new Register(null, "y")) { Type = host };
        var copy = new Instruction(0, OpCode.Move, x, y);
        var call = new Instruction(1, OpCode.CallVoid, callee, x);
        var method = Method(ownerType, app, [copy, call, new(2, OpCode.Return)], [x, y]);

        Simplifier.Simplify(method);

        Assert.Multiple(() =>
        {
            Assert.That(call.Operands[1], Is.SameAs(y),
                "a compatible slot type forwards into `this`");
            Assert.That(copy.OpCode, Is.EqualTo(OpCode.Nop),
                "the dead copy is dropped once `this` no longer reads it");
        });
    }

    // A chained field access `v.a.b` needs the receiver to supply `a`'s owner,
    // not `b`'s - a `v.inner.lane` store kept the copy alive when the leaf field's
    // declaring type was compared instead of the container's.
    [Test]
    public void CopyPropagationKeepsChainedFieldReceiverWhoseSlotTypeCannotSupplyContainerOwner()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var outer = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Outer",
            app.SystemTypes.SystemValueTypeType, TypeAttributes.Public);
        var inner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Inner",
            app.SystemTypes.SystemValueTypeType, TypeAttributes.Public);
        var other = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Other",
            app.SystemTypes.SystemValueTypeType, TypeAttributes.Public);
        var container = new InjectedFieldAnalysisContext("inner", inner,
            FieldAttributes.Public, outer, offset: 0);
        var leaf = new InjectedFieldAnalysisContext("lane", app.SystemTypes.SystemSingleType,
            FieldAttributes.Public, inner, offset: 0);
        var x = new LocalVariable("x", new Register(null, "x")) { Type = outer };
        var y = new LocalVariable("y", new Register(null, "y")) { Type = other };
        var result = new LocalVariable("result", new Register(null, "result"));
        var copy = new Instruction(0, OpCode.Move, x, y);
        var receiver = new FieldReference(leaf, x, offset: 0, containers: [container]);
        var method = Method(ownerType, app, [
            copy, new(1, OpCode.Move, result, receiver),
            new(2, OpCode.CallVoid, Str("sink"), result), new(3, OpCode.Return)],
            [x, y, result]);

        Simplifier.Simplify(method);

        Assert.Multiple(() =>
        {
            Assert.That(receiver.Local, Is.SameAs(x),
                "a slot that cannot supply the container's declaring type keeps the receiver");
            Assert.That(copy.OpCode, Is.EqualTo(OpCode.Move),
                "the copy must survive while the receiver still reads its destination");
        });
    }

    [Test]
    public void CopyPropagationForwardsChainedFieldReceiverWhoseSlotTypeSuppliesContainerOwner()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var outer = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Outer",
            app.SystemTypes.SystemValueTypeType, TypeAttributes.Public);
        var inner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Inner",
            app.SystemTypes.SystemValueTypeType, TypeAttributes.Public);
        var container = new InjectedFieldAnalysisContext("inner", inner,
            FieldAttributes.Public, outer, offset: 0);
        var leaf = new InjectedFieldAnalysisContext("lane", app.SystemTypes.SystemSingleType,
            FieldAttributes.Public, inner, offset: 0);
        var x = new LocalVariable("x", new Register(null, "x")) { Type = outer };
        var y = new LocalVariable("y", new Register(null, "y")) { Type = outer };
        var result = new LocalVariable("result", new Register(null, "result"));
        var copy = new Instruction(0, OpCode.Move, x, y);
        var receiver = new FieldReference(leaf, x, offset: 0, containers: [container]);
        var method = Method(ownerType, app, [
            copy, new(1, OpCode.Move, result, receiver),
            new(2, OpCode.CallVoid, Str("sink"), result), new(3, OpCode.Return)],
            [x, y, result]);

        Simplifier.Simplify(method);

        Assert.Multiple(() =>
        {
            Assert.That(receiver.Local, Is.SameAs(y),
                "a slot typed for the container's owner forwards into the receiver");
            Assert.That(copy.OpCode, Is.EqualTo(OpCode.Nop),
                "the dead copy is dropped once the receiver no longer reads it");
        });
    }

    [Test]
    public void CopyPropagationKeepsByRefCallArgWhoseSlotTypeCannotSupplyElement()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var host = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Host",
            app.SystemTypes.SystemValueTypeType, TypeAttributes.Public);
        var other = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Other",
            app.SystemTypes.SystemValueTypeType, TypeAttributes.Public);
        var callee = new InjectedMethodAnalysisContext(host, "Distance",
            app.SystemTypes.SystemSingleType, MethodAttributes.Static,
            [new ByRefTypeAnalysisContext(host), new ByRefTypeAnalysisContext(host)]);
        var x = new LocalVariable("x", new Register(null, "x")) { Type = host };
        var y = new LocalVariable("y", new Register(null, "y")) { Type = other };
        var w = new LocalVariable("w", new Register(null, "w")) { Type = host };
        var copy = new Instruction(0, OpCode.Move, x, y);
        var call = new Instruction(1, OpCode.CallVoid, callee, x, w);
        var method = Method(ownerType, app, [copy, call, new(2, OpCode.Return)], [x, y, w]);

        Simplifier.Simplify(method);

        Assert.Multiple(() =>
        {
            Assert.That(call.Operands[1], Is.SameAs(x),
                "a slot that cannot supply the byref element type keeps the argument");
            Assert.That(copy.OpCode, Is.EqualTo(OpCode.Move),
                "the copy must survive while the argument still reads its destination");
        });
    }

    // A memset/cpblk whose destination is a literal constant has no provable
    // managed meaning - pushing it as a native-int address lowers initblk to
    // unverifiable IL. The emission keeps the named diagnostic instead.
    [Test]
    public void BlockMemoryWriteToLiteralAddressKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("BlockLiteral.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType);
        var content = new LocalVariable("content", new Register(null, "content"))
            { Type = app.SystemTypes.SystemInt32Type };
        var count = new LocalVariable("count", new Register(null, "count"))
            { Type = app.SystemTypes.SystemInt32Type };
        var (caller, method) = ForeignCaller(app, module,
        [
            new(0, OpCode.MemorySet, new Immediate(0x2000), content, count),
            new(1, OpCode.Return)
        ], [content, count]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initblk || i.OpCode == CilOpCodes.Cpblk),
                Is.False, "a literal destination must not lower to block IL\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand?.ToString().Contains("block memory") == true), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }
}
