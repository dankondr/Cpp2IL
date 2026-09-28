using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Model.CustomAttributes;
using LibCpp2IL.BinaryStructures;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: all-zero literals into value slots (castle-recovery#136).
// A zero literal carries the all-zero bit pattern the binary proves the slot
// held, so default(contract) fills the slot honestly - the exact value a real
// conversion would produce - and no substitution diagnostic is needed.
public class ZeroLiteralSlotDefaultTests
{
    private static InjectedTypeAnalysisContext InjectStruct(ApplicationAnalysisContext app, string name) =>
        new(app.AssembliesByName["mscorlib"], "Tests", name,
            app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);

    private static InjectedFieldAnalysisContext AddField(InjectedTypeAnalysisContext owner, string name,
        TypeAnalysisContext type, int offset)
    {
        var field = new InjectedFieldAnalysisContext(name, type, R.FieldAttributes.Public, owner, offset);
        owner.Fields.Add(field);
        return field;
    }

    private static void AssertDiagnosticSubstitution(MethodDefinition method)
    {
        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("substituting")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call), Is.True,
                "the diagnostic must be an emitted call, not just a string");
        });
    }

    [Test]
    public void ZeroLiteralIntoStructSlotEmitsDefaultWithoutDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var structType = InjectStruct(app, "Point");
        AddField(structType, "x", app.SystemTypes.SystemInt32Type, 0);
        AddField(structType, "y", app.SystemTypes.SystemInt32Type, 4);
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = structType };
        var module = new ModuleDefinition("StructSlot.dll");
        SeedCorLibTypes(app, module, structType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, new Immediate(0)),
            new(1, OpCode.Return)], [slot]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initobj), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call), Is.False,
                "a proven-zero slot needs no conversion - the diagnostic call must be gone");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("substituting")), Is.False,
                "the binary proves the slot is zero - no value is being substituted");
        });
    }

    [Test]
    public void NonzeroLiteralIntoStructSlotKeepsSubstitutionDiagnostic()
    {
        // A nonzero literal is not the value the slot proves; the substitution
        // must stay diagnosed.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var structType = InjectStruct(app, "Point");
        AddField(structType, "x", app.SystemTypes.SystemInt32Type, 0);
        AddField(structType, "y", app.SystemTypes.SystemInt32Type, 4);
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = structType };
        var module = new ModuleDefinition("StructSlot.dll");
        SeedCorLibTypes(app, module, structType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, new Immediate(4)),
            new(1, OpCode.Return)], [slot]);

        IlGenerator.GenerateIl(caller, method);

        AssertDiagnosticSubstitution(method);
    }

    [Test]
    public void ZeroLiteralIntoByRefLikeSlotKeepsSubstitutionDiagnostic()
    {
        // A ref-struct slot is built on a native data pointer: `Move := 0` is
        // ambiguous with a lifted data-pointer store whose `add` emits as a
        // dead sibling, so the diagnostic stays.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var mscorlib = app.AssembliesByName["mscorlib"];
        var attribute = new InjectedTypeAnalysisContext(mscorlib,
            "System.Runtime.CompilerServices", "IsByRefLikeAttribute",
            app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class | R.TypeAttributes.Sealed);
        var attributeCtor = attribute.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig
                | R.MethodAttributes.SpecialName | R.MethodAttributes.RTSpecialName);
        var spanDef = new InjectedTypeAnalysisContext(mscorlib, "System", "ReadOnlySpan`1",
            app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        var t = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            R.GenericParameterAttributes.None, spanDef);
        spanDef.GenericParameters.Add(t);
        spanDef.CustomAttributes = [new AnalyzedCustomAttribute(attributeCtor)];
        AddField(spanDef, "_pointer", app.SystemTypes.SystemIntPtrType, 0);
        AddField(spanDef, "_length", app.SystemTypes.SystemIntPtrType, 8);
        var spanType = new GenericInstanceTypeAnalysisContext(spanDef,
            [app.SystemTypes.SystemByteType]);
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = spanType };
        var module = new ModuleDefinition("SpanSlot.dll");
        SeedCorLibTypes(app, module, spanDef, app.SystemTypes.SystemByteType,
            app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, new Immediate(0)),
            new(1, OpCode.Return)], [slot]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("Ref struct cannot cross")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call), Is.True,
                "the diagnostic must be an emitted call, not just a string");
        });
    }

    [Test]
    public void ZeroLiteralIntoPointerCarryingStructSlotKeepsSubstitutionDiagnostic()
    {
        // A struct holding a raw pointer has the same ambiguity even without
        // the by-ref-like marker: the zero may be a pointer store.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var holder = InjectStruct(app, "PointerHolder");
        AddField(holder, "raw", app.SystemTypes.SystemIntPtrType, 0);
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = holder };
        var module = new ModuleDefinition("HolderSlot.dll");
        SeedCorLibTypes(app, module, holder, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, new Immediate(0)),
            new(1, OpCode.Return)], [slot]);

        IlGenerator.GenerateIl(caller, method);

        AssertDiagnosticSubstitution(method);
    }

    [Test]
    public void ZeroLiteralIntoWideStructSlotKeepsSubstitutionDiagnostic()
    {
        // One zero register proves one native word: a 16-byte struct needs a
        // second register or a register-pair store the lifter did not see.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var wide = InjectStruct(app, "WidePoint");
        AddField(wide, "x", app.SystemTypes.SystemInt64Type, 0);
        AddField(wide, "y", app.SystemTypes.SystemInt64Type, 8);
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = wide };
        var module = new ModuleDefinition("WideSlot.dll");
        SeedCorLibTypes(app, module, wide, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, new Immediate(0)),
            new(1, OpCode.Return)], [slot]);

        IlGenerator.GenerateIl(caller, method);

        AssertDiagnosticSubstitution(method);
    }
}
