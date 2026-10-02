using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL.BinaryStructures;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.NestedFieldPathLoadTests;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: a small struct carried in one integer register
// (castle-recovery#216). A mask, shift or extension of the register reads the
// layout field at those bits: `And x,0xFF` on a packed Nullable<int> is
// hasValue, `LSR #32` is the second of two int fields, and a whole-register
// compare is a zero-test of the field above the bound. Reads whose bits land
// off a field keep the diagnostic.
public class PackedRegisterFieldTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static GenericInstanceTypeAnalysisContext NullableOf(ApplicationAnalysisContext app,
        TypeAnalysisContext element)
        => new(NullableDefinition(app), [element]);

    private static InjectedTypeAnalysisContext NullableDefinition(ApplicationAnalysisContext app)
    {
        var definition = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "System", "Nullable`1", app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        var t = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            R.GenericParameterAttributes.None, definition);
        definition.GenericParameters.Add(t);
        definition.Fields.Add(new InjectedFieldAnalysisContext("hasValue",
            app.SystemTypes.SystemBooleanType, R.FieldAttributes.Public, definition, 0));
        definition.Fields.Add(new InjectedFieldAnalysisContext("value",
            t, R.FieldAttributes.Public, definition, 4));
        return definition;
    }

    private static GenericInstanceTypeAnalysisContext TupleOf(ApplicationAnalysisContext app,
        TypeAnalysisContext first, TypeAnalysisContext second)
    {
        var definition = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "System", "ValueTuple`2", app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        var t1 = new GenericParameterTypeAnalysisContext("T1", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            R.GenericParameterAttributes.None, definition);
        var t2 = new GenericParameterTypeAnalysisContext("T2", 1, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            R.GenericParameterAttributes.None, definition);
        definition.GenericParameters.Add(t1);
        definition.GenericParameters.Add(t2);
        definition.Fields.Add(new InjectedFieldAnalysisContext("Item1",
            t1, R.FieldAttributes.Public, definition, 0));
        definition.Fields.Add(new InjectedFieldAnalysisContext("Item2",
            t2, R.FieldAttributes.Public, definition, 4));
        return new GenericInstanceTypeAnalysisContext(definition, [first, second]);
    }

    private static List<Instruction> Instructions(MethodAnalysisContext caller)
        => caller.ControlFlowGraph!.Blocks.SelectMany(b => b.Instructions).ToList();

    private static FieldReference ProjectedSource(Instruction instruction)
        => (FieldReference)instruction.Operands[1];

    private static void AssertNoUnrecoverable(MethodDefinition method)
    {
        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                && i.Operand is string text && text.Contains("Unrecoverable")), Is.False,
            () => "every read must lift clean:\n" + Dump(method));
    }

    [Test]
    public void NullableIntMaskReadsHasValueAndShiftReadsValue()
    {
        // ands w8, x0, #0xFF ; lsr x9, x0, #32 on a packed Nullable<int>
        var app = Cpp2IlApi.CurrentAppContext!;
        var nullableInt = NullableOf(app, app.SystemTypes.SystemInt32Type);
        var module = new ModuleDefinition("Packed.dll");
        Seed(module, app, nullableInt.GenericType);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemBooleanType, app.SystemTypes.SystemVoidType);

        var packed = new LocalVariable("packed", new Register(null, "X0"), nullableInt);
        var flag = Local("flag", app.SystemTypes.SystemBooleanType);
        var val = Local("val");
        var mask = new Instruction(0, OpCode.And, flag, packed, new Immediate(0xFF));
        var shift = new Instruction(1, OpCode.ShiftRight, val, packed, new Immediate(32));
        var (caller, method) = ForeignCaller(app, module,
            [mask, shift, new Instruction(2, OpCode.Return)], [packed, flag, val]);
        caller.ParameterLocals = [packed];

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(mask.OpCode, Is.EqualTo(OpCode.Move));
            Assert.That(ProjectedSource(mask).Field.Name, Is.EqualTo("hasValue"));
            Assert.That(shift.OpCode, Is.EqualTo(OpCode.Move));
            Assert.That(ProjectedSource(shift).Field.Name, Is.EqualTo("value"));
        });

        IlGenerator.GenerateIl(caller, method);
        AssertNoUnrecoverable(method);
    }

    [Test]
    public void NullableBoolBoundCheckIsHighFieldNullTest()
    {
        // `cmp x0, #256` on a packed Nullable<bool> asks whether any byte above
        // hasValue is nonzero: with padding zero it is `value == 0`.
        var app = Cpp2IlApi.CurrentAppContext!;
        var nullableBool = NullableOf(app, app.SystemTypes.SystemBooleanType);
        var module = new ModuleDefinition("Packed.dll");
        Seed(module, app, nullableBool.GenericType);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemBooleanType,
            app.SystemTypes.SystemVoidType);

        var packed = new LocalVariable("packed", new Register(null, "X0"), nullableBool);
        var result = Local("result", app.SystemTypes.SystemBooleanType);
        var check = new Instruction(0, OpCode.CheckLess, result, packed, new Immediate(256));
        var (caller, method) = ForeignCaller(app, module,
            [check, new Instruction(1, OpCode.Return)], [packed, result]);
        caller.ParameterLocals = [packed];

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(check.OpCode, Is.EqualTo(OpCode.CheckEqual));
            Assert.That(check.Operands[1], Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)check.Operands[1]).Field.Name, Is.EqualTo("value"));
            Assert.That(check.Operands[2], Is.EqualTo(new Immediate(0)));
        });

        IlGenerator.GenerateIl(caller, method);
        AssertNoUnrecoverable(method);
    }

    [Test]
    public void TupleSecondIntReadsThroughSignShift()
    {
        // asr x8, x0, #32 on a packed ValueTuple<int,int> is Item2.
        var app = Cpp2IlApi.CurrentAppContext!;
        var pair = TupleOf(app, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemInt32Type);
        var module = new ModuleDefinition("Packed.dll");
        Seed(module, app, pair.GenericType);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType);

        var packed = new LocalVariable("packed", new Register(null, "X0"), pair);
        var second = Local("second");
        var shift = new Instruction(0, OpCode.ShiftRight, second, packed, new Immediate(32));
        var (caller, method) = ForeignCaller(app, module,
            [shift, new Instruction(1, OpCode.Return)], [packed, second]);
        caller.ParameterLocals = [packed];

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(shift.OpCode, Is.EqualTo(OpCode.Move));
            Assert.That(ProjectedSource(shift).Field.Name, Is.EqualTo("Item2"));
        });

        IlGenerator.GenerateIl(caller, method);
        AssertNoUnrecoverable(method);
    }

    [Test]
    public void WidthlessAddOfPackedPairReadsTheLowField()
    {
        // `add w10, w9, w2` with a Vector2Int in x2 lifts with no width: a 64-bit add has no
        // meaning on two packed ints, so the 32-bit result reads `v.x`. A result typed as an
        // eight-byte integer keeps the whole-register read diagnosed. A W-source conversion
        // reads the low field too.
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var vector2Int = InjectStruct(app, "Vector2Int");
        InjectField("x", int32, vector2Int, 0);
        InjectField("y", int32, vector2Int, 4);
        var module = new ModuleDefinition("Packed.dll");
        Seed(module, app, vector2Int);
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemInt64Type, app.SystemTypes.SystemVoidType);

        var packed = new LocalVariable("packed", new Register(null, "X2"), vector2Int);
        var other = Local("other", int32);
        var sum = Local("sum");
        var wide = Local("wide", app.SystemTypes.SystemInt64Type);
        var add = new Instruction(0, OpCode.Add, sum, other, packed);
        var wideAdd = new Instruction(1, OpCode.Add, wide, other, packed);
        // `scvtf s0, w2` converts the same low word.
        var converted = Local("converted", app.SystemTypes.SystemSingleType);
        var convert = new Instruction(2, OpCode.Convert, converted, packed) { ConversionSourceWidthBits = 32 };
        var (caller, _) = ForeignCaller(app, module,
            [add, wideAdd, convert, new Instruction(3, OpCode.Return)], [packed, other, sum, wide, converted]);
        caller.ParameterLocals = [packed, other];

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(add.Operands[2], Is.InstanceOf<FieldReference>());
            Assert.That(((FieldReference)add.Operands[2]).Field.Name, Is.EqualTo("x"));
            Assert.That(wideAdd.Operands[2], Is.SameAs(packed));
            Assert.That(convert.Operands[1], Is.InstanceOf<FieldReference>());
            Assert.That(((FieldReference)convert.Operands[1]).Field.Name, Is.EqualTo("x"));
        });
    }

    [Test]
    public void Vector2IntYLaneIndexesTwoDimensionalArray()
    {
        // lsr w8, x0, #32 (Vector2Int.y) as the second index of grid[x, y]:
        // the lane is a field read and the access lifts to T[,]::Get.
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var vector2Int = InjectStruct(app, "Vector2Int");
        InjectField("x", int32, vector2Int, 0);
        InjectField("y", int32, vector2Int, 4);
        var module = new ModuleDefinition("Packed.dll");
        Seed(module, app, vector2Int);
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemBooleanType,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);

        var grid = Local("grid", new ArrayTypeAnalysisContext(int32, 2));
        var packed = new LocalVariable("packed", new Register(null, "X8"), vector2Int);
        var bounds = Local("bounds");
        var x = Local("x", int32);
        var y = Local("y");
        var cx = Local("cx", app.SystemTypes.SystemBooleanType);
        var cy = Local("cy", app.SystemTypes.SystemBooleanType);
        var product = Local("product");
        var flat = Local("flat");
        var scaled = Local("scaled");
        var pointer = Local("pointer");
        var value = Local("value", int32);
        var shift = new Instruction(0, OpCode.ShiftRight, y, packed, new Immediate(32))
        {
            NativeIntegerWidthBits = 32,
        };
        var access = new Instruction(8, OpCode.Move, value,
            new MemoryOperand(pointer, null, 0x20, 0, 4));
        var (caller, method) = ForeignCaller(app, module, [
            shift,
            new(1, OpCode.Move, bounds, new MemoryOperand(grid, null, 0x10, 0, 8)),
            new(2, OpCode.CheckLess, cx, x, new MemoryOperand(bounds, null, 0, 0, 4)),
            new(3, OpCode.CheckLess, cy, y, new MemoryOperand(bounds, null, 0x10, 0, 4)),
            new(4, OpCode.Multiply, product, new MemoryOperand(bounds, null, 0x10, 0, 4), x),
            new(5, OpCode.Add, flat, y, product),
            new(6, OpCode.ShiftLeft, scaled, flat, new Immediate(2)),
            new(7, OpCode.Add, pointer, grid, scaled),
            access,
            new(9, OpCode.Return, value),
        ], [grid, packed, bounds, x, y, cx, cy, product, flat, scaled, pointer, value]);
        caller.ParameterLocals = [grid, packed, x];

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(shift.OpCode, Is.EqualTo(OpCode.Move));
            Assert.That(ProjectedSource(shift).Field.Name, Is.EqualTo("y"));
        });

        ArrayRecovery.RecoverMultiDimensionalAccesses(caller);

        var get = Instructions(caller).Single(i => i.Operands.FirstOrDefault()
            is MethodAnalysisContext { Name: "Get" });
        Assert.Multiple(() =>
        {
            Assert.That(get.Operands.Skip(2), Is.EqualTo(new IOperand[] { grid, x, y }));
            Assert.That(y.Type, Is.SameAs(int32),
                "the y lane reads as the field's own type");
        });

        // System.Array::GetLength needs its AsmResolver definition for the
        // bounds checks to emit.
        var arrayType = app.SystemTypes.SystemArrayType!;
        SeedCorLibTypes(app, module, arrayType);
        var getLength = arrayType.Methods.Single(m => m.Name == "GetLength" && m.Parameters.Count == 1);
        var getLengthDefinition = new MethodDefinition("GetLength",
            AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public,
            AsmResolver.DotNet.Signatures.MethodSignature.CreateInstance(module.CorLibTypeFactory.Int32,
                [module.CorLibTypeFactory.Int32]));
        arrayType.GetExtraData<TypeDefinition>("AsmResolverType")!.Methods.Add(getLengthDefinition);
        getLength.PutExtraData("AsmResolverMethod", getLengthDefinition);

        IlGenerator.GenerateIl(caller, method);
        AssertNoUnrecoverable(method);
    }

    [Test]
    public void TopMaskReadsSignedHighField()
    {
        // `ands x8, x0, #0xFFFFFFFF00000000` keeps the y lane's raw bits exactly:
        // the field is signed, but a ShiftLeft result ends at bit 63 so the
        // sign extension shifts out of the register - the read is still y.
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var vector2Int = InjectStruct(app, "Vector2Int");
        InjectField("x", int32, vector2Int, 0);
        InjectField("y", int32, vector2Int, 4);
        var module = new ModuleDefinition("Packed.dll");
        Seed(module, app, vector2Int);
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemInt64Type,
            app.SystemTypes.SystemVoidType);

        var packed = new LocalVariable("packed", new Register(null, "X0"), vector2Int);
        var masked = Local("masked");
        var mask = new Instruction(0, OpCode.And, masked, packed,
            new Immediate(unchecked((long)0xFFFFFFFF00000000)));
        var (caller, method) = ForeignCaller(app, module,
            [mask, new Instruction(1, OpCode.Return)], [packed, masked]);
        caller.ParameterLocals = [packed];

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(mask.OpCode, Is.EqualTo(OpCode.ShiftLeft));
            Assert.That(ProjectedSource(mask).Field.Name, Is.EqualTo("y"));
            Assert.That(mask.Operands[2], Is.EqualTo(new Immediate(32)));
        });

        IlGenerator.GenerateIl(caller, method);
        AssertNoUnrecoverable(method);
    }

    [Test]
    public void LowMaskReadsSignedLowFieldIntoWideDestination()
    {
        // `ands w8, x0, #0xFFFFFFFF` keeps the x lane's raw bits in a 32-bit
        // destination: the field's signedness is invisible at that width, so
        // the read is x even though Int32 is signed.
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var vector2Int = InjectStruct(app, "Vector2Int");
        InjectField("x", int32, vector2Int, 0);
        InjectField("y", int32, vector2Int, 4);
        var module = new ModuleDefinition("Packed.dll");
        Seed(module, app, vector2Int);
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemInt64Type,
            app.SystemTypes.SystemVoidType);

        var packed = new LocalVariable("packed", new Register(null, "X0"), vector2Int);
        var masked32 = Local("masked32", int32);
        var masked64 = Local("masked64", app.SystemTypes.SystemInt64Type);
        var narrow = new Instruction(0, OpCode.And, masked32, packed,
            new Immediate(0xFFFFFFFF));
        var wide = new Instruction(1, OpCode.And, masked64, packed,
            new Immediate(0xFFFFFFFF));
        var (caller, method) = ForeignCaller(app, module,
            [narrow, wide, new Instruction(2, OpCode.Return)],
            [packed, masked32, masked64]);
        caller.ParameterLocals = [packed];

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(narrow.OpCode, Is.EqualTo(OpCode.Move));
            Assert.That(ProjectedSource(narrow).Field.Name, Is.EqualTo("x"),
                "a 32-bit destination stores the lane's bits exactly");
            Assert.That(wide.OpCode, Is.EqualTo(OpCode.And),
                "a 64-bit destination would see the mask's zero extension: stays diagnosed");
        });
    }

    [Test]
    public void AwaiterChainRestampedAfterEarlyPassStaysDiagnosed()
    {
        // An awaiter register local looks like `Awaiter` while the in-SSA pass
        // runs and `object` once a later inference settles the slot: a
        // `slot.task.source` read projected on the early view emits
        // `ldloc;unbox;ldflda`, which does not verify. The read stays a
        // diagnosed integer op.
        var app = Cpp2IlApi.CurrentAppContext!;
        var inner = InjectStruct(app, "InnerTask");
        InjectField("source", app.SystemTypes.SystemObjectType, inner, 0);
        var outer = InjectStruct(app, "AwaiterShell");
        var task = InjectField("task", inner, outer, 0);
        var module = new ModuleDefinition("Packed.dll");
        Seed(module, app, inner, outer);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemBooleanType, app.SystemTypes.SystemVoidType);

        var slot = new LocalVariable("slot", new Register(null, "X8"), outer);
        var result = Local("result", app.SystemTypes.SystemBooleanType);
        var fill = new Instruction(0, OpCode.Move, slot, new Immediate(0));
        var check = new Instruction(1, OpCode.CheckEqual, result,
            new FieldReference(task, slot, 0), new Immediate(0));
        var (caller, method) = ForeignCaller(app, module,
            [fill, check, new Instruction(2, OpCode.Return)], [slot, result]);

        LocalVariables.ResolveTypesAndFields(caller);
        // The restamp a later pass performs on the same local.
        slot.Type = app.SystemTypes.SystemObjectType;
        IlGenerator.GenerateIl(caller, method);

        Assert.That(check.Operands[1], Is.TypeOf<FieldReference>()
                .And.Matches((FieldReference? reference) => reference is { Field.Name: "task" }),
            "a container hop taken on the early emitted type emits `unbox;ldflda` - stays");
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Ldflda),
            Is.False, () => "no readonly-& field address may reach the emitted body:\n" + Dump(method));
    }

    [Test]
    public void AwaiterChainOnStructSlotProjectsInFinalPass()
    {
        // The same chain on a root whose emitted slot stays the struct projects
        // at the final pass - `ldloca`/`ldflda` verifies there.
        var app = Cpp2IlApi.CurrentAppContext!;
        var inner = InjectStruct(app, "InnerTask");
        InjectField("source", app.SystemTypes.SystemObjectType, inner, 0);
        var outer = InjectStruct(app, "AwaiterShell");
        var task = InjectField("task", inner, outer, 0);
        var module = new ModuleDefinition("Packed.dll");
        Seed(module, app, inner, outer);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemBooleanType, app.SystemTypes.SystemVoidType);

        var slot = new LocalVariable("slot", new Register(null, "X8"), outer);
        var result = Local("result", app.SystemTypes.SystemBooleanType);
        var check = new Instruction(0, OpCode.CheckEqual, result,
            new FieldReference(task, slot, 0), new Immediate(0));
        var (caller, method) = ForeignCaller(app, module,
            [check, new Instruction(1, OpCode.Return)], [slot, result]);

        LocalVariables.ResolveTypesAndFields(caller);
        PackedRegisterFields.Run(caller, finalPass: true);

        Assert.That(check.Operands[1], Is.TypeOf<FieldReference>()
                .And.Matches((FieldReference? reference) =>
                    reference is { Field.Name: "source", Containers.Count: 1 }),
            "a settled struct slot keeps the recovered read");

        IlGenerator.GenerateIl(caller, method);
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Ldflda),
            Is.True, () => "the writable-address hop reaches the emitted body:\n" + Dump(method));
    }

    [Test]
    public void FieldReadOnRestampedPrimitiveSlotStaysDiagnosed()
    {
        // `Move i32dest, v` whole-reads the low four bytes of an 8-byte struct
        // - the Single field at offset 0. The root local is defined by an
        // arithmetic op, so its emitted slot is not provable early; a later
        // inference restamps the register guess to `System.Single`. Single's
        // own offset-0 field is private to the corlib, so `ldfld` cannot be
        // spelled from the caller and the emitter would substitute `ldc.r4 0`
        // where control read `ldloc; conv.i4`. The read must stay the register
        // operand in both passes.
        var app = Cpp2IlApi.CurrentAppContext!;
        var pack = InjectStruct(app, "FloatPack");
        InjectField("m_value", app.SystemTypes.SystemSingleType, pack, 0);
        InjectField("pad", app.SystemTypes.SystemInt32Type, pack, 4);
        var module = new ModuleDefinition("Packed.dll");
        Seed(module, app, pack);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemBooleanType,
            app.SystemTypes.SystemVoidType);

        var slot = new LocalVariable("slot", new Register(null, "X8"), pack);
        var operand = new LocalVariable("operand", new Register(null, "X9"), pack);
        var dest = Local("dest", app.SystemTypes.SystemInt32Type);
        var sub = new Instruction(0, OpCode.Subtract, slot, operand, new Immediate(1));
        var move = new Instruction(1, OpCode.Move, dest, slot);
        var (caller, method) = ForeignCaller(app, module,
            [sub, move, new Instruction(2, OpCode.Return)], [slot, operand, dest]);

        LocalVariables.ResolveTypesAndFields(caller);
        Assert.That(move.Operands[1], Is.SameAs(slot),
            "an unprovable arithmetic root keeps its register read until its slot type settles");

        // The restamp a later inference performs on the same register local.
        slot.Type = app.SystemTypes.SystemSingleType;
        PackedRegisterFields.Run(caller, finalPass: true);

        Assert.That(move.Operands[1], Is.SameAs(slot),
            "a private corlib member is unspellable from the caller; the whole read stays");
    }

    [Test]
    public void PointerLocalMethodKeepsReadsDiagnosed()
    {
        // `ldloc` on an unmanaged-pointer local is not a verifiable type. A
        // rewrite here would remove the diagnostic that keeps such code dead,
        // so every rewrite in the method is declined.
        var app = Cpp2IlApi.CurrentAppContext!;
        var nullableInt = NullableOf(app, app.SystemTypes.SystemInt32Type);
        var module = new ModuleDefinition("Packed.dll");
        Seed(module, app, nullableInt.GenericType);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemBooleanType, app.SystemTypes.SystemVoidType);

        var packed = new LocalVariable("packed", new Register(null, "X0"), nullableInt);
        var pointer = new LocalVariable("pointer", new Register(null, "X9"),
            new PointerTypeAnalysisContext(app.SystemTypes.SystemInt32Type));
        var flag = Local("flag", app.SystemTypes.SystemBooleanType);
        var mask = new Instruction(0, OpCode.And, flag, packed, new Immediate(0xFF));
        var (caller, method) = ForeignCaller(app, module,
            [mask, new Instruction(1, OpCode.Move, pointer, new Immediate(0)),
                new Instruction(2, OpCode.Return)],
            [packed, pointer, flag]);
        caller.ParameterLocals = [packed];

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.That(mask.OpCode, Is.EqualTo(OpCode.And),
            "a method reading a pointer-typed local declines packed rewrites");
    }

    [Test]
    public void PartialByteMaskStaysDiagnosed()
    {
        // `ands x8, x0, #0x0F00000000` selects four bits of `value` - a bit
        // range that is not a field's: the read stays an unrecoverable integer
        // operation.
        var app = Cpp2IlApi.CurrentAppContext!;
        var nullableInt = NullableOf(app, app.SystemTypes.SystemInt32Type);
        var module = new ModuleDefinition("Packed.dll");
        Seed(module, app, nullableInt.GenericType);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemInt64Type,
            app.SystemTypes.SystemBooleanType, app.SystemTypes.SystemVoidType);

        var packed = new LocalVariable("packed", new Register(null, "X0"), nullableInt);
        var masked = Local("masked");
        var mask = new Instruction(0, OpCode.And, masked, packed, new Immediate(0x0F00000000));
        var (caller, method) = ForeignCaller(app, module,
            [mask, new Instruction(1, OpCode.Return)], [packed, masked]);
        caller.ParameterLocals = [packed];

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.That(mask.OpCode, Is.EqualTo(OpCode.And));

        IlGenerator.GenerateIl(caller, method);
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr
                && i.Operand is string text && text.Contains("Unrecoverable integer operation")),
            Is.True, () => "the non-field mask keeps its diagnostic:\n" + Dump(method));
    }
}
