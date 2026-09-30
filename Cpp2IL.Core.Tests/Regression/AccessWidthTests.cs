using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.NestedFieldPathLoadTests;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery mechanism: the bytes an access covers decide which fields it names
// (castle-recovery#211). Native code moves bytes: one store can cover the end of
// one field and the start of the next, several fields, or a whole struct. Each
// covered field gets its own bytes; a field cut in half has no managed spelling.
public class AccessWidthTests
{
    private static bool Stores(MethodDefinition method, string field)
        => method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Stfld
            && i.Operand is IFieldDescriptor f && f.Name == field);

    private static bool Diagnoses(MethodDefinition method, string text)
        => method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr
            && i.Operand is string message && message.Contains(text));

    // Point3 { float x @0; float y @4; float z @8 }
    private static InjectedTypeAnalysisContext Point3(ApplicationAnalysisContext app)
    {
        var type = InjectStruct(app, "Point3");
        InjectField("x", app.SystemTypes.SystemSingleType, type, 0);
        InjectField("y", app.SystemTypes.SystemSingleType, type, 4);
        InjectField("z", app.SystemTypes.SystemSingleType, type, 8);
        return type;
    }

    [Test]
    public void ZeroStoreSpanningTwoStructFieldsStoresEachCoveredMember()
    {
        // Box { Point3 low @0x10; Point3 high @0x1C }. Eight zero bytes at 0x18 are
        // low.z and high.x: no field starts there with that width.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var point = Point3(app);
        var box = InjectClass(app, "Box");
        InjectField("low", point, box, 0x10);
        InjectField("high", point, box, 0x1C);
        var module = new ModuleDefinition("Width.dll");
        Seed(module, app, point, box);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemSingleType, app.SystemTypes.SystemObjectType);

        var receiver = Local("box", box);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(receiver, null, 0x18, 0, 8), new Immediate(0)),
            new(1, OpCode.Return)], [receiver]);

        MetadataResolver.ResolveFieldOffsets(caller);
        IlGenerator.GenerateIl(caller, method);

        Assert.Multiple(() =>
        {
            Assert.That(Stores(method, "z"), Is.True, () => Dump(method));
            Assert.That(Stores(method, "x"), Is.True, () => Dump(method));
            Assert.That(Stores(method, "y"), Is.False, () => Dump(method));
            Assert.That(Diagnoses(method, "could not be emitted"), Is.False, () => Dump(method));
        });
    }

    [Test]
    public void ConstantOverTwoFieldsGivesEachItsOwnBytes()
    {
        // Holder { int first @0x10; int second @0x14 }: one 8-byte store of
        // 0x00000002_00000001 is first = 1 and second = 2. Narrowing it to the field
        // at the offset would lose `second` without a word.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var holder = InjectClass(app, "Holder");
        InjectField("first", app.SystemTypes.SystemInt32Type, holder, 0x10);
        InjectField("second", app.SystemTypes.SystemInt32Type, holder, 0x14);
        var module = new ModuleDefinition("Width.dll");
        Seed(module, app, holder);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemObjectType);

        var receiver = Local("holder", holder);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(receiver, null, 0x10, 0, 8), new Immediate(0x0000000200000001)),
            new(1, OpCode.Return)], [receiver]);

        MetadataResolver.ResolveFieldOffsets(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        int Stored(string field)
        {
            var store = il.First(i => i.OpCode == CilOpCodes.Stfld && i.Operand is IFieldDescriptor f && f.Name == field);
            return il[il.IndexOf(store) - 1].GetLdcI4Constant();
        }
        Assert.Multiple(() =>
        {
            Assert.That(Stores(method, "first") && Stores(method, "second"), Is.True, () => Dump(method));
            Assert.That(Stored("first"), Is.EqualTo(1), () => Dump(method));
            Assert.That(Stored("second"), Is.EqualTo(2), () => Dump(method));
        });
    }

    [Test]
    public void StoreCuttingAFieldInHalfKeepsDiagnostic()
    {
        // Four bytes at 0x12 are the upper half of `first` and the lower half of
        // `second`: neither field is written whole, so nothing is spelled.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var holder = InjectClass(app, "Holder");
        InjectField("first", app.SystemTypes.SystemInt32Type, holder, 0x10);
        InjectField("second", app.SystemTypes.SystemInt32Type, holder, 0x14);
        var module = new ModuleDefinition("Width.dll");
        Seed(module, app, holder);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemObjectType);

        var receiver = Local("holder", holder);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(receiver, null, 0x12, 0, 4), new Immediate(0)),
            new(1, OpCode.Return)], [receiver]);

        MetadataResolver.ResolveFieldOffsets(caller);
        IlGenerator.GenerateIl(caller, method);

        Assert.Multiple(() =>
        {
            Assert.That(Stores(method, "first") || Stores(method, "second"), Is.False, () => Dump(method));
            Assert.That(Diagnoses(method, "could not be emitted"), Is.True, () => Dump(method));
        });
    }

    [Test]
    public void AdjacentZeroStoresOverAWholeStructFieldStoreItsDefault()
    {
        // Panel { Quad rect @0x10 }, Quad = four floats. `STP XZR, XZR` is two 8-byte
        // stores; together they zero the field, which is `rect = default`.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var quad = InjectStruct(app, "Quad");
        foreach (var (name, offset) in new[] { ("a", 0), ("b", 4), ("c", 8), ("d", 12) })
            InjectField(name, app.SystemTypes.SystemSingleType, quad, offset);
        var panel = InjectClass(app, "Panel");
        InjectField("rect", quad, panel, 0x10);
        var module = new ModuleDefinition("Width.dll");
        Seed(module, app, quad, panel);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemSingleType, app.SystemTypes.SystemObjectType);

        var receiver = Local("panel", panel);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(receiver, null, 0x10, 0, 8), new Immediate(0)),
            new(1, OpCode.Move, new MemoryOperand(receiver, null, 0x18, 0, 8), new Immediate(0)),
            new(2, OpCode.Return)], [receiver]);

        MetadataResolver.ResolveFieldOffsets(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Stfld && i.Operand is IFieldDescriptor f
                && f.Name == "rect"), Is.EqualTo(1), () => Dump(method));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initobj), Is.True, () => Dump(method));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False, () => Dump(method));
        });
    }

    [Test]
    public void VectorLiteralOverFourIntFieldsGivesEachItsBits()
    {
        // `LDR Q0, [literal]; STR Q0, [obj + 0x10]` over four ints. The register is a
        // float vector, the fields are ints: each field takes its own four bytes as an
        // integer. Treating the literal as floats would store 0 into the first field
        // and drop the other three.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var config = InjectClass(app, "Config");
        foreach (var (name, offset) in new[] { ("a", 0x10), ("b", 0x14), ("c", 0x18), ("d", 0x1C) })
            InjectField(name, app.SystemTypes.SystemInt32Type, config, offset);
        var module = new ModuleDefinition("Width.dll");
        Seed(module, app, config);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemObjectType);

        static float Bits(int value) => System.BitConverter.Int32BitsToSingle(value);
        var receiver = Local("config", config);
        var vector = Local("v0");
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, vector, new Vector128Literal(Bits(1), Bits(50), Bits(10), Bits(7))),
            new(1, OpCode.Move, new MemoryOperand(receiver, null, 0x10, 0, 0), vector) { NativeStoreWidthBytes = 16 },
            new(2, OpCode.Return)], [receiver, vector]);

        MetadataResolver.ResolveFieldOffsets(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        int Stored(string field)
        {
            var store = il.First(i => i.OpCode == CilOpCodes.Stfld && i.Operand is IFieldDescriptor f && f.Name == field);
            return il[il.IndexOf(store) - 1].GetLdcI4Constant();
        }
        Assert.That(new[] { "a", "b", "c", "d" }.All(field => Stores(method, field)), Is.True, () => Dump(method));
        Assert.That(new[] { Stored("a"), Stored("b"), Stored("c"), Stored("d") }, Is.EqualTo(new[] { 1, 50, 10, 7 }),
            () => Dump(method));
    }

    [Test]
    public void DoubleLiteralLanesAreTwoFloats()
    {
        // `LDR D0, [literal]; STR D0, [obj + 0x10]` over two floats, already split into
        // lanes: the low lane is the register, the high lane a shift of it. The literal
        // read as a double is 2.0000004…; its halves are 10f and 2f.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var range = InjectClass(app, "Range");
        InjectField("low", app.SystemTypes.SystemSingleType, range, 0x10);
        InjectField("high", app.SystemTypes.SystemSingleType, range, 0x14);
        var module = new ModuleDefinition("Width.dll");
        Seed(module, app, range);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemSingleType, app.SystemTypes.SystemObjectType);

        var pair = System.BitConverter.Int64BitsToDouble(
            (long)(uint)System.BitConverter.SingleToInt32Bits(2f) << 32 | (uint)System.BitConverter.SingleToInt32Bits(10f));
        var receiver = Local("range", range);
        var register = Local("d0");
        var upper = Local("upper");
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, register, new DoubleLiteral(pair)),
            new(1, OpCode.Move, new MemoryOperand(receiver, null, 0x10, 0, 4), register),
            new(2, OpCode.ShiftRight, upper, register, new Immediate(32)),
            new(3, OpCode.Move, new MemoryOperand(receiver, null, 0x14, 0, 4), upper),
            new(4, OpCode.Return)], [receiver, register, upper]);

        MetadataResolver.ResolveFieldOffsets(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        float Stored(string field)
        {
            var store = il.First(i => i.OpCode == CilOpCodes.Stfld && i.Operand is IFieldDescriptor f && f.Name == field);
            return (float)il[il.IndexOf(store) - 1].Operand!;
        }
        Assert.That(Stores(method, "low") && Stores(method, "high"), Is.True, () => Dump(method));
        Assert.That(new[] { Stored("low"), Stored("high") }, Is.EqualTo(new[] { 10f, 2f }), () => Dump(method));
    }

    [Test]
    public void FieldsOfAClassWithAGenericBaseAreStillSplit()
    {
        // Derived : Base<int>, own fields past the base's. The base's layout is
        // computed elsewhere; a range that touches none of its fields is unaffected.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var listOfInt = list.MakeGenericInstanceType([app.SystemTypes.SystemInt32Type]);
        var derived = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Derived",
            listOfInt, System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        InjectField("first", app.SystemTypes.SystemInt32Type, derived, 0x40);
        InjectField("second", app.SystemTypes.SystemInt32Type, derived, 0x44);

        var parts = MetadataResolver.CoveredFields(derived, 0x40, 8, wholeStructs: false);

        Assert.That(parts?.Select(part => part.Field.Name), Is.EqualTo(new[] { "first", "second" }));
        // ...but a range inside the generic base has no answer here.
        Assert.That(MetadataResolver.CoveredFields(derived, 0x10, 8, wholeStructs: false), Is.Null);
    }

    [Test]
    public void StaticStorageIsSplitOverTheTypesOwnStaticFields()
    {
        // Static storage of Sizes { static Point3 banner @0; static float scale @0xC; int instance @0x10 }:
        // eight bytes at 8 are banner.z and scale. Instance fields are not in it.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var point = Point3(app);
        var sizes = InjectClass(app, "Sizes");
        foreach (var (name, type, offset) in new[] { ("banner", (TypeAnalysisContext)point, 0), ("scale", app.SystemTypes.SystemSingleType, 0xC) })
            sizes.Fields.Add(new InjectedFieldAnalysisContext(name, type,
                System.Reflection.FieldAttributes.Public | System.Reflection.FieldAttributes.Static, sizes, offset));
        InjectField("instance", app.SystemTypes.SystemInt32Type, sizes, 0x10);

        var parts = MetadataResolver.CoveredFields(sizes, 8, 8, wholeStructs: false, statics: true);

        Assert.That(parts?.Select(part => string.Join(".", part.Containers.Select(c => c.Name).Append(part.Field.Name))),
            Is.EqualTo(new[] { "banner.z", "scale" }));
    }

    [Test]
    public void StoreThroughRefToPrimitiveIsADereference()
    {
        // `out long value`: [value] = 0 is `value = 0`, not a store to Int64's
        // private m_value field.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int64 = app.SystemTypes.SystemInt64Type;
        var module = new ModuleDefinition("Width.dll");
        SeedCorLibTypes(app, module, int64, app.SystemTypes.SystemVoidType);

        var pointer = Local("value", new ByRefTypeAnalysisContext(int64));
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(pointer, accessSize: 8), new Immediate(0)),
            new(1, OpCode.Return)], [pointer]);

        MetadataResolver.ResolveFieldOffsets(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stobj || i.OpCode == CilOpCodes.Stind_I8), Is.True,
                () => Dump(method));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False, () => Dump(method));
        });
    }

    [Test]
    public void PrimitiveFieldIsALeafWhateverTheAccessWidth()
    {
        // Gauge { float level @0x10 }: a store recorded wider than the field is still a
        // store to the field. A primitive has no member to descend into.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var gauge = InjectClass(app, "Gauge");
        InjectField("level", app.SystemTypes.SystemSingleType, gauge, 0x10);
        var module = new ModuleDefinition("Width.dll");
        Seed(module, app, gauge);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemSingleType, app.SystemTypes.SystemObjectType);

        var receiver = Local("gauge", gauge);
        var value = Local("value", app.SystemTypes.SystemSingleType);
        var (caller, method) = ForeignCaller(app, module, [
            new(-1, OpCode.Move, value, new FloatLiteral(2f)),
            new(0, OpCode.Move, new MemoryOperand(receiver, null, 0x10, 0, 8), value),
            new(1, OpCode.Return)], [receiver, value]);

        MetadataResolver.ResolveFieldOffsets(caller);
        IlGenerator.GenerateIl(caller, method);

        Assert.Multiple(() =>
        {
            Assert.That(Stores(method, "level"), Is.True, () => Dump(method));
            Assert.That(Diagnoses(method, "m_value"), Is.False, () => Dump(method));
        });
    }
}
