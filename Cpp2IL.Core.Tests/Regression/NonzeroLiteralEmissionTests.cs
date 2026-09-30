using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: nonzero literals into typed slots (castle-recovery#177).
// A slot's declared type can prove how the binary encodes the constant - a
// float slot proves a bit pattern, a small plain-data struct proves whole
// bytes - and the emission must spell exactly that value. Anything the slot
// cannot prove keeps the named substitution diagnostic.
public class NonzeroLiteralEmissionTests
{
    private static InjectedTypeAnalysisContext InjectStruct(ApplicationAnalysisContext app, string name) =>
        new(app.AssembliesByName["mscorlib"], "Tests", name,
            app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);

    private static void AddField(InjectedTypeAnalysisContext owner, string name,
        TypeAnalysisContext type, int offset)
    {
        var field = new InjectedFieldAnalysisContext(name, type, R.FieldAttributes.Public, owner, offset);
        owner.Fields.Add(field);
        // stfld needs a real metadata token: back the injected field with a
        // FieldDefinition on the owner's seeded TypeDefinition.
        var ownerDefinition = owner.GetExtraData<TypeDefinition>("AsmResolverType")
            ?? throw new System.InvalidOperationException("seed the owner before AddField");
        var definition = new FieldDefinition(name, AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public,
            new AsmResolver.DotNet.Signatures.FieldSignature(type.ToTypeSignature()));
        ownerDefinition.Fields.Add(definition);
        field.PutExtraData("AsmResolverField", definition);
    }

    private static (MethodAnalysisContext caller, MethodDefinition method) Build(
        ApplicationAnalysisContext app, ModuleDefinition module,
        TypeAnalysisContext slotType, IOperand source)
    {
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = slotType };
        return ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, source),
            new(1, OpCode.Return)], [slot]);
    }

    private static void AssertNoDiagnostic(MethodDefinition method)
    {
        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("substituting")), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call), Is.False,
                "a proven literal needs no diagnostic call");
        });
    }

    private static void AssertDiagnosticSubstitution(MethodDefinition method)
    {
        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                && i.Operand is string text && text.Contains("substituting")), Is.True,
            () => string.Join("\n", il.Select(i => i.ToString())));
    }

    [Test]
    public void NonzeroLiteralIntoSingleSlotEmitsBitPattern()
    {
        // mov w8, #0x3f800000 into a Single slot encodes 1.0f - the register's
        // bits, not the integer value 1065353216.0f a (float) cast would make.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("FloatSlot.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemSingleType, app.SystemTypes.SystemVoidType);
        var (caller, method) = Build(app, module, app.SystemTypes.SystemSingleType,
            new Immediate(0x3F800000));

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_R4
                    && i.Operand is float f && f == 1f), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_R4
                    && i.Operand is float f && f == 1065353216f), Is.False,
                "the literal must be reinterpreted as bits, not re-typed as a value");
        });
        AssertNoDiagnostic(method);
    }

    [Test]
    public void NonzeroLiteralIntoDoubleSlotEmitsBitPattern()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("DoubleSlot.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemVoidType);
        var (caller, method) = Build(app, module, app.SystemTypes.SystemDoubleType,
            new Immediate(0x3FF0000000000000));

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_R8
                && i.Operand is double d && d == 1d), Is.True,
            () => string.Join("\n", il.Select(i => i.ToString())));
        AssertNoDiagnostic(method);
    }

    [Test]
    public void NarrowNonzeroLiteralIntoDoubleSlotKeepsDiagnostic()
    {
        // Only an X-register write proves 8 bytes; a value any W register
        // could have made may be a folded movk's residue, so a narrow
        // immediate into a Double slot keeps its named note.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("NarrowDoubleSlot.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemVoidType);
        var (caller, method) = Build(app, module, app.SystemTypes.SystemDoubleType,
            new Immediate(0x3F800000));

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_R8), Is.False,
            () => string.Join("\n", il.Select(i => i.ToString())));
        AssertDiagnosticSubstitution(method);
    }

    [Test]
    public void ZeroLiteralIntoDoubleSlotEmitsZeroBits()
    {
        // Zero is the all-zero value under either width reading, so it still
        // emits the bit pattern without a diagnostic.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("ZeroDoubleSlot.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemVoidType);
        var (caller, method) = Build(app, module, app.SystemTypes.SystemDoubleType,
            new Immediate(0));

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_R8
                && i.Operand is double d && d == 0d), Is.True,
            () => string.Join("\n", il.Select(i => i.ToString())));
    }

    [Test]
    public void NonzeroLiteralIntoWordSizedPlainStructSpillsBits()
    {
        // A struct the size of one register is proven byte-for-byte by the
        // literal: emit its raw bits rather than a substituted default.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var plain = InjectStruct(app, "Plain4");
        var module = new ModuleDefinition("PlainSlot.dll");
        SeedCorLibTypes(app, module, plain, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemVoidType);
        AddField(plain, "raw", app.SystemTypes.SystemInt32Type, 0);
        var (caller, method) = Build(app, module, plain, new Immediate(0x01020304));

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Stfld), Is.EqualTo(1),
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_I4
                    && i.Operand is int v && v == 0x01020304), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initobj), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldflda), Is.False,
                "a top-level leaf needs no address hop - ldflda of the leaf itself "
                + "would type the address &Int32 where stfld wants &Plain4");
            Assert.That(il.Any(i => i.OpCode.ToString().StartsWith("stind")), Is.False,
                "stind on a managed & is unverifiable - stfld spells the same store");
        });
        AssertNoDiagnostic(method);
    }

    [Test]
    public void WideLiteralIntoTwoWordPlainStructSpillsBits()
    {
        // A value no W register could have produced proves the whole 8-byte
        // register, covering an 8-byte plain struct one field at a time.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var plain = InjectStruct(app, "Plain8");
        var module = new ModuleDefinition("WidePlainSlot.dll");
        SeedCorLibTypes(app, module, plain, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemVoidType);
        AddField(plain, "x", app.SystemTypes.SystemInt32Type, 0);
        AddField(plain, "y", app.SystemTypes.SystemInt32Type, 4);
        var (caller, method) = Build(app, module, plain, new Immediate(0x0000000200000001));

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Stfld), Is.EqualTo(2),
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_I4
                    && i.Operand is int v && v == 1), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_I4
                    && i.Operand is int v && v == 2), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initobj), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldflda), Is.False,
                "top-level leaves need no address hops");
            Assert.That(il.Any(i => i.OpCode.ToString().StartsWith("stind")), Is.False,
                "stind on a managed & is unverifiable - stfld spells the same store");
        });
        AssertNoDiagnostic(method);
    }

    [Test]
    public void FloatLiteralIntoPlainStructSpillsBits()
    {
        // `ldr s0, =1.5f` proves the register's low four bytes are 1.5f's IEEE
        // pattern: a same-sized plain struct takes them as a field store.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var plain = InjectStruct(app, "Plain4");
        var module = new ModuleDefinition("FloatPlainSlot.dll");
        SeedCorLibTypes(app, module, plain, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemVoidType);
        AddField(plain, "raw", app.SystemTypes.SystemInt32Type, 0);
        var (caller, method) = Build(app, module, plain, new FloatLiteral(1.5f));

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Stfld), Is.EqualTo(1),
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_I4
                    && i.Operand is int v && v == 0x3FC00000), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initobj), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldflda), Is.False,
                "a top-level leaf needs no address hop");
        });
        AssertNoDiagnostic(method);
    }

    [Test]
    public void NestedPlainStructSpillsBitsThroughIntermediateHop()
    {
        // Outer { inner: Inner } where Inner { raw: int }: the literal's slice
        // reaches the leaf through exactly one ldflda hop - the leaf itself is
        // written by stfld, never addressed.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var inner = InjectStruct(app, "Inner");
        var outer = InjectStruct(app, "Outer");
        var module = new ModuleDefinition("NestedPlainSlot.dll");
        SeedCorLibTypes(app, module, inner, outer, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType);
        AddField(inner, "raw", app.SystemTypes.SystemInt32Type, 0);
        AddField(outer, "inner", inner, 0);
        var (caller, method) = Build(app, module, outer, new Immediate(0x01020304));

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Stfld), Is.EqualTo(1),
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldflda), Is.EqualTo(1),
                "only the intermediate field is addressed");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_I4
                    && i.Operand is int v && v == 0x01020304), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initobj), Is.True);
        });
        AssertNoDiagnostic(method);
    }

    [Test]
    public void NarrowLiteralIntoTwoWordPlainStructKeepsDiagnostic()
    {
        // The same 8-byte struct with a value any W register could have made:
        // the upper word is unproven, so the diagnostic stays.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var plain = InjectStruct(app, "Plain8");
        var module = new ModuleDefinition("UnprovenWideSlot.dll");
        SeedCorLibTypes(app, module, plain, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemVoidType);
        AddField(plain, "x", app.SystemTypes.SystemInt32Type, 0);
        AddField(plain, "y", app.SystemTypes.SystemInt32Type, 4);
        var (caller, method) = Build(app, module, plain, new Immediate(4));

        IlGenerator.GenerateIl(caller, method);

        AssertDiagnosticSubstitution(method);
    }

    [Test]
    public void NonzeroLiteralIntoPointerCarryingStructKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var holder = InjectStruct(app, "PointerHolder");
        var module = new ModuleDefinition("PointerHolderSlot.dll");
        SeedCorLibTypes(app, module, holder, app.SystemTypes.SystemIntPtrType, app.SystemTypes.SystemVoidType);
        AddField(holder, "raw", app.SystemTypes.SystemIntPtrType, 0);
        var (caller, method) = Build(app, module, holder, new Immediate(0x01020304));

        IlGenerator.GenerateIl(caller, method);

        AssertDiagnosticSubstitution(method);
    }

    [Test]
    public void NonzeroLiteralIntoReferenceFieldStructKeepsDiagnostic()
    {
        // A struct holding a managed reference is not bit-plain: the literal
        // cannot prove what the reference field's bits mean.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var holder = InjectStruct(app, "RefHolder");
        var module = new ModuleDefinition("RefHolderSlot.dll");
        SeedCorLibTypes(app, module, holder, app.SystemTypes.SystemStringType, app.SystemTypes.SystemVoidType);
        AddField(holder, "text", app.SystemTypes.SystemStringType, 0);
        var (caller, method) = Build(app, module, holder, new Immediate(0x0102030405060708));

        IlGenerator.GenerateIl(caller, method);

        AssertDiagnosticSubstitution(method);
    }

    [Test]
    public void LiteralIntoEnumFieldStructKeepsDiagnostic()
    {
        // An enum-typed leaf cannot be written through stfld from an Int32
        // constant, so the whole contract stays unproven and keeps its note.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var enumType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests",
            "SmallEnum", app.SystemTypes.EnumType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed);
        var holder = InjectStruct(app, "EnumHolder");
        var module = new ModuleDefinition("EnumHolderSlot.dll");
        SeedCorLibTypes(app, module, holder, enumType, app.SystemTypes.SystemVoidType);
        AddField(holder, "kind", enumType, 0);
        var (caller, method) = Build(app, module, holder, new Immediate(2));

        IlGenerator.GenerateIl(caller, method);

        AssertDiagnosticSubstitution(method);
    }
}
