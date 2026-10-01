using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using Disarm;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: proven byte width of immediates through FMOV / MOVZ+MOVK /
// MOVI writes into SIMD-FP registers (castle-recovery#248). A register write
// records how many bytes of the source the destination actually took - an S
// or W write claims only its own bytes, so a wider slot read stays diagnosed;
// a D or X write, or a movz/movk chain that proves all eight, fills it. The
// S/D width rides on the emitted Move and the count rides on the immediate,
// so a slot that needs a whole Double or Single is filled by the literal only
// when the producing write was at least as wide.
public class ProvenWidthLiteralTests
{
    private static List<Instruction> Lift(params uint[] words)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Test",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public | MethodAttributes.Static, []);
        return new NewArmV8InstructionSet().ConvertInstructions(
            Disassembler.Disassemble(words.SelectMany(BitConverter.GetBytes).ToArray(), 0), context);
    }

    private static (MethodAnalysisContext caller, MethodDefinition method) Build(
        ApplicationAnalysisContext app, ModuleDefinition module,
        TypeAnalysisContext slotType, IOperand source)
    {
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = slotType };
        var move = new Instruction(0, OpCode.Move, slot, source);
        return ForeignCaller(app, module, [move, new(1, OpCode.Return)], [slot]);
    }

    // The fmov the lifter emitted, retargeted so its operand lands in a synthetic
    // slot local: the S/D write mark it carries is the real lifter annotation.
    // keepOperand simulates an immediate the lifter itself spelled; replacing it
    // simulates the immediate a pass substitutes in for the source register.
    private static (MethodAnalysisContext caller, MethodDefinition method) BuildFromLiftedMove(
        ApplicationAnalysisContext app, ModuleDefinition module,
        TypeAnalysisContext slotType, uint fmovWord, long? value = null)
    {
        var move = Lift(fmovWord).Single(i => i.OpCode == OpCode.Move);
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = slotType };
        move.SetOperand(0, slot);
        if (value is { } v)
            move.SetOperand(1, new Immediate(v));
        return ForeignCaller(app, module, [move, new(1, OpCode.Return)], [slot]);
    }

    private static void AssertNoDiagnostic(MethodDefinition method)
    {
        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                && i.Operand is string text && text.Contains("substituting")), Is.False,
            () => string.Join("\n", il.Select(i => i.ToString())));
    }

    private static void AssertDiagnosticSubstitution(MethodDefinition method)
    {
        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                && i.Operand is string text && text.Contains("substituting")), Is.True,
            () => string.Join("\n", il.Select(i => i.ToString())));
    }

    [Test]
    public void FmovSImmediateLiftsAsProvenBitPattern()
    {
        // fmov s0, #1.0 writes a 32-bit single-precision pattern into the low
        // lane: the operand is the untyped bit pattern with its four proven
        // bytes, and the move carries the S write's width.
        var move = Lift(0x1E2E1000).Single(i => i.OpCode == OpCode.Move);
        var operand = (Immediate)move.Operands[1];
        Assert.Multiple(() =>
        {
            Assert.That(operand.Value, Is.EqualTo(0x3F800000));
            Assert.That(operand.ProvenBytes, Is.EqualTo(4));
            Assert.That(move.NativeFloatWriteBits, Is.EqualTo(32));
        });
    }

    [Test]
    public void FmovSImmediateReadAsDoubleSlotStaysDiagnosed()
    {
        // fmov s0,#imm wrote four bytes: a slot read as Double has a defect in
        // its type and must stay diagnosed rather than take the zero-extended
        // pattern as a double literal.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("FmovSDoubleSlot.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemVoidType);
        var (caller, method) = BuildFromLiftedMove(app, module, app.SystemTypes.SystemDoubleType,
            0x1E2E1000); // fmov s0, #1.0

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_R8), Is.False,
            () => string.Join("\n", il.Select(i => i.ToString())));
        AssertDiagnosticSubstitution(method);
    }

    [Test]
    public void MovzMovkThenFmovSMarksTheWriteWidth()
    {
        // movz w8,#0 ; movk w8,#0x7fc0,lsl 16 ; fmov s0,w8 - the GPR->FP move
        // records that only the low word of X8 became the register.
        var move = Lift(0x52800008, 0x72AFF808, 0x1E270100).Last(i => i.OpCode == OpCode.Move);
        Assert.Multiple(() =>
        {
            Assert.That(move.Operands[0].ToString(), Is.EqualTo("V0"));
            Assert.That(move.Operands[1].ToString(), Is.EqualTo("X8"));
            Assert.That(move.NativeFloatWriteBits, Is.EqualTo(32));
        });
    }

    [Test]
    public void MovzMovkChainThenFmovDMarksTheWriteWidth()
    {
        // movz x8,#0x1111 ; movk x8,#0x2222,lsl 16 ; movk x8,#0x3333,lsl 32 ;
        // movk x8,#0x4444,lsl 48 ; fmov d0,x8 - a full-width write marks 64.
        var move = Lift(0xD2822228, 0xF2A44448, 0xF2C66668, 0xF2E88888, 0x9E670100)
            .Last(i => i.OpCode == OpCode.Move);
        Assert.Multiple(() =>
        {
            Assert.That(move.Operands[1].ToString(), Is.EqualTo("X8"));
            Assert.That(move.NativeFloatWriteBits, Is.EqualTo(64));
        });
    }

    [Test]
    public void LiftedMovzXImmediateFillsDoubleSlot()
    {
        // movz x8 wrote all eight bytes of the register, so the immediate it
        // produced carries proven byte count 8 and a Double slot emits the
        // literal without any write mark on the move.
        var lifted = (Immediate)Lift(0xD2824688) // movz x8, #0x1234
            .Single(i => i.OpCode == OpCode.Move).Operands[1];
        Assert.That(lifted.ProvenBytes, Is.EqualTo(8));

        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("LiftedMovzSlot.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemVoidType);
        var (caller, method) = Build(app, module, app.SystemTypes.SystemDoubleType, lifted);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_R8
                && i.Operand is double d && d == BitConverter.Int64BitsToDouble(0x1234)), Is.True,
            () => string.Join("\n", il.Select(i => i.ToString())));
        AssertNoDiagnostic(method);
    }

    [Test]
    public void LiftedMovzWImmediateIntoDoubleSlotStaysDiagnosed()
    {
        // movz w8 is a W write: it proves four bytes, so the immediate cannot
        // fill a Double slot even though the register zero-extended.
        var lifted = (Immediate)Lift(0x52824688) // movz w8, #0x1234
            .Single(i => i.OpCode == OpCode.Move).Operands[1];
        Assert.That(lifted.ProvenBytes, Is.EqualTo(4));

        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("LiftedMovzWSlot.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemVoidType);
        var (caller, method) = Build(app, module, app.SystemTypes.SystemDoubleType, lifted);

        IlGenerator.GenerateIl(caller, method);

        Assert.That(method.CilMethodBody!.Instructions
            .Any(i => i.OpCode == CilOpCodes.Ldc_R8), Is.False,
            () => string.Join("\n", method.CilMethodBody.Instructions.Select(i => i.ToString())));
        AssertDiagnosticSubstitution(method);
    }

    [Test]
    public void SWriteImmediateIntoDoubleSlotStaysDiagnosed()
    {
        // A pass-substituted immediate behind an S write keeps only the write's
        // four proven bytes: a Double slot stays diagnosed - the
        // zero-extension of the register is not the slot's bytes.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("SWriteDoubleSlot.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemVoidType);
        var (caller, method) = BuildFromLiftedMove(app, module, app.SystemTypes.SystemDoubleType,
            0x1E270100, 0x7FC00000); // fmov s0, w8

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_R8), Is.False,
            () => string.Join("\n", il.Select(i => i.ToString())));
        AssertDiagnosticSubstitution(method);
    }

    [Test]
    public void NarrowWriteKeepsOnlyItsOwnBytes()
    {
        // The lifter-side resolution masks an immediate to the write's width
        // and caps its proven count at the write's extent: an S write of a
        // wider source keeps only the low word and four proven bytes.
        var written = ImmediateWriteWidth.ForWrite(
            new Immediate(unchecked((long)0xDEADBEEF7FC00000), 8), 32, "V0");
        Assert.Multiple(() =>
        {
            Assert.That(written.Value, Is.EqualTo(0x7FC00000L));
            Assert.That(written.ProvenBytes, Is.EqualTo(4));
        });
    }

    [Test]
    public void MarkedSinglePrecisionCallResultFillsFloatSlot()
    {
        // castle-recovery#262: a helper bridged onto a Double-declared method
        // whose native write was single-precision produces four bytes. The
        // declared return type does not widen it, so a comparison against a
        // 4-byte fmov literal fills a System.Single slot with ldc.r4.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var dbl = app.SystemTypes.SystemDoubleType;
        var mathType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "Tests", "Math", app.SystemTypes.SystemObjectType,
            TypeAttributes.Public | TypeAttributes.Class);
        var sqrt = mathType.InjectMethodContext("Sqrt", dbl,
            MethodAttributes.Public | MethodAttributes.Static, dbl);
        var module = new ModuleDefinition("MarkedWidth.dll");
        SeedCorLibTypes(app, module, dbl, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemBooleanType,
            app.SystemTypes.SystemVoidType);
        var mathDefinition = new TypeDefinition("Tests", "Math",
            AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(mathDefinition);
        mathType.PutExtraData("AsmResolverType", mathDefinition);
        var sqrtDefinition = new MethodDefinition("Sqrt",
            AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Double,
                [module.CorLibTypeFactory.Double]));
        mathDefinition.Methods.Add(sqrtDefinition);
        sqrt.PutExtraData("AsmResolverMethod", sqrtDefinition);
        var arg = new LocalVariable("arg", new Register(null, "arg")) { Type = dbl };
        var result = new LocalVariable("result", new Register(null, "result"));
        var cond = new LocalVariable("cond", new Register(null, "cond"),
            app.SystemTypes.SystemBooleanType);
        var call = new Instruction(0, OpCode.Call, sqrt, result, arg)
        {
            NativeFloatWidthBits = 32,
        };
        var (caller, method) = ForeignCaller(app, module, [
            new(-1, OpCode.Move, arg, new Immediate(0)),
            call,
            new(1, OpCode.CheckLess, cond, result, new Immediate(0x3F800000, 4)),
            new(2, OpCode.Return)], [arg, result, cond]);

        IlGenerator.GenerateIl(caller, method);

        Assert.That(method.CilMethodBody!.Instructions
            .Any(i => i.OpCode == CilOpCodes.Ldc_R4), Is.True,
            () => string.Join("\n", method.CilMethodBody.Instructions.Select(i => i.ToString())));
        AssertNoDiagnostic(method);
    }

    [Test]
    public void NarrowProvenLiteralIntoDoubleSlotKeepsDiagnostic()
    {
        // A D-width write whose source only proved four bytes cannot fill the
        // slot: the folded-movk residue case stays diagnosed.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("NarrowProvenSlot.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemVoidType);
        var (caller, method) = BuildFromLiftedMove(app, module, app.SystemTypes.SystemDoubleType,
            0x9E670100, 0x7FC00000); // fmov d0, x8

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_R8), Is.False,
            () => string.Join("\n", il.Select(i => i.ToString())));
        AssertDiagnosticSubstitution(method);
    }
}
