using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;
using F = AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes;
using T = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: ISIL→IL emission — stores through unmanaged [base + offset]
// memory operands (#97). A Move into [local + N] where the local's type names a
// field at offset N is a field store the lifter never expressed; it lowers to
// stfld. Offsets that name no field, mismatched widths, and bases with no
// managed type keep the explicit drop diagnostic.
public class UnmanagedStoreTests
{
    private static FieldAnalysisContext SeedField(ModuleDefinition module, TypeAnalysisContext owner,
        string name, TypeAnalysisContext fieldType, int offset)
    {
        var field = new InjectedFieldAnalysisContext(name, fieldType,
            System.Reflection.FieldAttributes.Public, owner, offset);
        owner.Fields.Add(field);
        var definition = owner.GetExtraData<TypeDefinition>("AsmResolverType")!;
        var fieldDefinition = new FieldDefinition(name, F.Public,
            new FieldSignature(fieldType.GetExtraData<TypeSignature>("AsmResolverSignature")
                ?? module.CorLibTypeFactory.CorLibScope.CreateTypeReference(fieldType.Namespace, fieldType.Name)
                    .ToTypeSignature(fieldType.IsValueType)));
        definition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        return field;
    }

    private static TypeAnalysisContext SeededOwner(ApplicationAnalysisContext app,
        ModuleDefinition module, string name, TypeAnalysisContext baseType)
    {
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", name,
            baseType, System.Reflection.TypeAttributes.Public);
        var definition = new TypeDefinition("Tests", name,
            T.Public | (baseType.IsValueType ? T.Sealed | T.SequentialLayout : T.Class),
            baseType.IsValueType
                ? module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType")
                : module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(definition);
        owner.PutExtraData("AsmResolverType", definition);
        return owner;
    }

    [Test]
    public void StoreAtFieldOffsetOnTypedLocalEmitsStfld()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var module = new ModuleDefinition("FieldStore.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);
        var owner = SeededOwner(app, module, "Holder", app.SystemTypes.SystemObjectType);
        var field = SeedField(module, owner, "payload", int32, 0x10);
        var holder = new LocalVariable("holder", new Register(null, "holder")) { Type = owner };
        var value = new LocalVariable("value", new Register(null, "value")) { Type = int32 };
        var (caller, method) = ForeignCaller(app, module, [
            new(-1, OpCode.Move, value, new Immediate(7)),
            new(0, OpCode.Move, new MemoryOperand(holder, addend: 0x10, accessSize: 4), value),
            new(1, OpCode.Return)], [holder, value]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld
                    && i.Operand?.ToString().Contains("payload") == true), Is.True,
                "[holder + 0x10] where holder: Holder has field payload @0x10 lowers to stfld\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void StoreAtFieldOffsetInStructLocalEmitsStfld()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var module = new ModuleDefinition("StructFieldStore.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemValueTypeType,
            app.SystemTypes.SystemVoidType);
        var owner = SeededOwner(app, module, "Aggregate", app.SystemTypes.SystemValueTypeType);
        var field = SeedField(module, owner, "second", int32, 4);
        var buffer = new LocalVariable("buffer", new Register(null, "buffer")) { Type = owner };
        var value = new LocalVariable("value", new Register(null, "value")) { Type = int32 };
        var (caller, method) = ForeignCaller(app, module, [
            new(-1, OpCode.Move, value, new Immediate(7)),
            new(0, OpCode.Move, new MemoryOperand(buffer, addend: 4, accessSize: 4), value),
            new(1, OpCode.Return)], [buffer, value]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldloca), Is.True,
                "a value-typed base is addressed through its local slot\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld
                    && i.Operand?.ToString().Contains("second") == true), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void StoreAtOffsetWithNoMatchingFieldKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var module = new ModuleDefinition("NoFieldStore.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);
        var owner = SeededOwner(app, module, "Holder", app.SystemTypes.SystemObjectType);
        SeedField(module, owner, "payload", int32, 0x10);
        var holder = new LocalVariable("holder", new Register(null, "holder")) { Type = owner };
        var value = new LocalVariable("value", new Register(null, "value")) { Type = int32 };
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(holder, addend: 0x14, accessSize: 4), value),
            new(1, OpCode.Return)], [holder, value]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld), Is.False,
                "an offset that names no field must not guess one");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text
                    && text.Contains("unmanaged memory form")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void StoreAtFieldOffsetWithWrongWidthKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var int64 = app.SystemTypes.SystemInt64Type;
        var module = new ModuleDefinition("WidthStore.dll");
        SeedCorLibTypes(app, module, int32, int64, app.SystemTypes.SystemVoidType);
        var owner = SeededOwner(app, module, "Holder", app.SystemTypes.SystemObjectType);
        SeedField(module, owner, "payload", int32, 0x10);
        var holder = new LocalVariable("holder", new Register(null, "holder")) { Type = owner };
        var value = new LocalVariable("value", new Register(null, "value")) { Type = int64 };
        // An 8-byte native store at the offset of a 4-byte field would clobber
        // the next field if lowered to stfld; it must stay diagnosed.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(holder, addend: 0x10, accessSize: 8), value),
            new(1, OpCode.Return)], [holder, value]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld), Is.False);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text
                    && text.Contains("unmanaged memory form")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void StoreToFramePointerSlotEmitsStloc()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var module = new ModuleDefinition("FrameSlotStore.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);
        var frame = new LocalVariable("frame", new Register(null, "X29_v1"));
        var value = new LocalVariable("value", new Register(null, "value")) { Type = int32 };
        // [x29 - 0x18] = a write into a frame slot; the slot becomes a local and
        // the store lowers to stloc.
        var (caller, method) = ForeignCaller(app, module, [
            new(-1, OpCode.Move, value, new Immediate(7)),
            new(0, OpCode.Move, new MemoryOperand(frame, addend: -0x18, accessSize: 4), value),
            new(1, OpCode.Return)], [frame, value]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stloc), Is.True,
                "a frame-slot store must emit stloc into the slot's local\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(method.CilMethodBody.LocalVariables.Any(v =>
                    v.VariableType?.FullName.Contains("Int32") == true), Is.True);
        });
    }

    [Test]
    public void StoreToFrameSlotWithConflictingTypeKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var int64 = app.SystemTypes.SystemInt64Type;
        var module = new ModuleDefinition("ConflictingFrameSlot.dll");
        SeedCorLibTypes(app, module, int32, int64, app.SystemTypes.SystemVoidType);
        var frame = new LocalVariable("frame", new Register(null, "X29_v1"));
        var intValue = new LocalVariable("intValue", new Register(null, "intValue")) { Type = int32 };
        var wideValue = new LocalVariable("wideValue", new Register(null, "wideValue")) { Type = int64 };
        // The slot is typed by the first store (int32). The second store writes
        // an int64 to the same slot - a real spill conflict that managed locals
        // cannot express; it keeps the explicit drop diagnostic.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(frame, addend: -0x18, accessSize: 4), intValue),
            new(1, OpCode.Move, new MemoryOperand(frame, addend: -0x18, accessSize: 8), wideValue),
            new(2, OpCode.Return)], [frame, intValue, wideValue]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Stloc), Is.EqualTo(1),
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text
                    && text.Contains("unmanaged memory form")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void StoreThroughUntypedLocalWithNoTypeEvidenceKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var frame = new LocalVariable("frame", new Register(null, "frame"));
        var value = new LocalVariable("value", new Register(null, "value")) { Type = int32 };
        var module = new ModuleDefinition("FrameStore.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);
        // A frame-pointer-relative slot with no call or allocation to name its
        // type has no managed slot; the store stays explicitly diagnosed.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(frame, addend: -0x18, accessSize: 4), value),
            new(1, OpCode.Return)], [frame, value]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld), Is.False);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text
                    && text.Contains("unmanaged memory form")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }
}
