using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
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
// or W write zero-extends the register, so the whole 64-bit value is proven
// even when the immediate itself only spells four bytes. The S/D width rides
// on the emitted Move and the count rides on the immediate, so a slot that
// needs a whole Double or Single is filled by the literal instead of being
// diagnosed.
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
    private static (MethodAnalysisContext caller, MethodDefinition method) BuildFromLiftedMove(
        ApplicationAnalysisContext app, ModuleDefinition module,
        TypeAnalysisContext slotType, uint fmovWord, long value)
    {
        var move = Lift(fmovWord).Single(i => i.OpCode == OpCode.Move);
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = slotType };
        move.SetOperand(0, slot);
        move.SetOperand(1, new Immediate(value));
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
    public void FmovSImmediateLiftsAsSingleLiteral()
    {
        // fmov s0, #1.0 writes a 32-bit single-precision pattern into the low
        // lane: the operand is a Single literal and the move carries the S
        // write's width.
        var move = Lift(0x1E2E1000).Single(i => i.OpCode == OpCode.Move);
        Assert.Multiple(() =>
        {
            Assert.That(move.Operands[1], Is.EqualTo(new FloatLiteral(1f)));
            Assert.That(move.NativeFloatWriteBits, Is.EqualTo(32));
        });
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
    public void LiftedMovzImmediateFillsDoubleSlot()
    {
        // The immediate the movz produced carries its own proven byte count:
        // movz wrote the whole register, so a Double slot sees all eight
        // bytes and emits the literal without any write mark on the move.
        var lifted = Lift(0x52824688) // movz w8, #0x1234
            .Single(i => i.OpCode == OpCode.Move).Operands[1];

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
    public void SWriteZeroExtensionFillsDoubleSlot()
    {
        // fmov s0,w8 zero-extends into V0: a downstream Double read sees the
        // source's low word padded with machine zeros, and all eight bytes
        // are proven.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("SWriteDoubleSlot.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemVoidType);
        var (caller, method) = BuildFromLiftedMove(app, module, app.SystemTypes.SystemDoubleType,
            0x1E270100, 0x7FC00000); // fmov s0, w8

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_R8
                && i.Operand is double d && d == BitConverter.Int64BitsToDouble(0x7FC00000)), Is.True,
            () => string.Join("\n", il.Select(i => i.ToString())));
        AssertNoDiagnostic(method);
    }

    [Test]
    public void SWriteMasksSourceAboveWriteWidth()
    {
        // The same S write on a source that spelled more than a word: only the
        // low 32 bits become the register - the recorded value is masked to
        // the write's width, not widened to the source's.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("SWriteMaskSlot.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemVoidType);
        var (caller, method) = BuildFromLiftedMove(app, module, app.SystemTypes.SystemDoubleType,
            0x1E270100, unchecked((long)0xDEADBEEF7FC00000)); // fmov s0, w8

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_R8
                    && i.Operand is double d && d == BitConverter.Int64BitsToDouble(0x7FC00000)),
                Is.True, () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_R8
                    && i.Operand is double d && d == BitConverter.Int64BitsToDouble(unchecked((long)0xDEADBEEF7FC00000))),
                Is.False, "the write only took the source's low word");
        });
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
