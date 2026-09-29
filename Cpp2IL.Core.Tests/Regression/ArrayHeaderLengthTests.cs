using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: unmanaged loads of the array header's length word
// (+0x18 for 64-bit) through an address chain - the binary materializes
// `array + 0x18` into its own register (pre-index writeback, or a hoisted
// header address) and dereferences `[p]` or `[p + k]`. When the base's
// definition chain is provably `array + constant` through copies and
// add/subtract immediates only, and the touched word lands exactly on
// max_length, the load is the array's Length and emits ldlen (+ conv.i4).
// Every other header-word read - klass +0, monitor +8, bounds +0x10 - keeps
// its unmanaged-memory diagnostic, as do stores to the length word (#169).
public class ArrayHeaderLengthTests
{
    private static string Emit(IEnumerable<CilInstruction> il) => string.Join("\n", il.Select(i => i.ToString()));

    private static MethodDefinition HeaderReader(ApplicationAnalysisContext app, ModuleDefinition module,
        int pointerDelta, int addend, bool store = false)
    {
        var int32 = app.SystemTypes.SystemInt32Type;
        var array = new LocalVariable("array", new Register(null, "array"))
            { Type = new SzArrayTypeAnalysisContext(int32) };
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var value = new LocalVariable("value", new Register(null, "value")) { Type = int32 };
        var memory = new MemoryOperand(pointer, addend: addend);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Add, pointer, array, new Immediate(pointerDelta)),
            store
                ? new Instruction(1, OpCode.Move, memory, value)
                : new Instruction(1, OpCode.Move, value, memory),
            new(2, OpCode.Return)
        };
        var locals = new List<LocalVariable> { array, pointer, value };
        var (caller, method) = ForeignCaller(app, module, instructions, locals);
        caller.ParameterLocals = locals;
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph!);
        ArrayRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);
        return method;
    }

    [Test]
    public void DerivedLengthWordLoadEmitsLdlen()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("LengthWord.dll");
        var int32 = app.SystemTypes.SystemInt32Type;
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);

        // `pointer = array + 0x18; length = [pointer]` - the pre-index writeback
        // shape for `array->max_length`.
        var method = HeaderReader(app, module, pointerDelta: 0x18, addend: 0);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldlen), Is.EqualTo(1),
                () => Emit(il));
            Assert.That(il.Where(i => i.OpCode == CilOpCodes.Ldstr).All(i =>
                    i.Operand?.ToString()?.Contains("operand to System.Object slot") == true), Is.True,
                () => Emit(il));
        });
    }

    [Test]
    public void FoldedLengthWordLoadEmitsLdlen()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("FoldedLength.dll");
        var int32 = app.SystemTypes.SystemInt32Type;
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);

        // `pointer = array + 0x10; length = [pointer + 8]` - the hoisted bounds
        // address folded with a remaining immediate lands on the same word.
        var method = HeaderReader(app, module, pointerDelta: 0x10, addend: 8);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldlen), Is.EqualTo(1),
                () => Emit(il));
            Assert.That(il.Where(i => i.OpCode == CilOpCodes.Ldstr).All(i =>
                    i.Operand?.ToString()?.Contains("operand to System.Object slot") == true), Is.True,
                () => Emit(il));
        });
    }

    [Test]
    public void KlassWordLoadKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("KlassWord.dll");
        var int32 = app.SystemTypes.SystemInt32Type;
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);
        var array = new LocalVariable("array", new Register(null, "array"))
            { Type = new SzArrayTypeAnalysisContext(int32) };
        var klass = new LocalVariable("klass", new Register(null, "klass")) { Type = int32 };
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, klass, new MemoryOperand(array)),
            new(1, OpCode.Return)], [array, klass]);
        caller.ParameterLocals = [array, klass];
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph!);

        ArrayRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.True,
                () => Emit(il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldlen), Is.False,
                () => Emit(il));
        });
    }

    [Test]
    public void BoundsWordLoadKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("BoundsWord.dll");
        var int32 = app.SystemTypes.SystemInt32Type;
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);

        // `pointer = array + 0x10; bounds = [pointer]` - the bounds word is not
        // the length word.
        var method = HeaderReader(app, module, pointerDelta: 0x10, addend: 0);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.True,
                () => Emit(il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldlen), Is.False,
                () => Emit(il));
        });
    }

    [Test]
    public void LengthWordStoreKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("LengthStore.dll");
        var int32 = app.SystemTypes.SystemInt32Type;
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);

        // `pointer = array + 0x18; [pointer] = value` - a store to the length
        // word has no ldlen spelling; the write must never turn into a load
        // of the array's length.
        var method = HeaderReader(app, module, pointerDelta: 0x18, addend: 0, store: true);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldlen), Is.False,
            () => Emit(il));
    }
}
