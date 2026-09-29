using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: reads of locals no instruction ever defines
// (castle-recovery#145). An entry-version register (Version -1) that is not a
// parameter and is never stored has no value a managed read can spell - the
// old emitter still emitted ldloc, so the decompiler reported the local as
// unassigned (CS0165). The emitter now substitutes the documented default and
// leaves a decompiler-issue note that names the missing value; locals whose
// address is taken keep ldloc because a `&` write can still define them.
public class UndefinedLocalReadTests
{
    [Test]
    public void UndefinedEntryRegisterReadSubstitutesDocumentedDefault()
    {
        // Move dest, entry where `entry` is an entry-version register that no
        // instruction defines: the read has no proven value, so it must carry
        // the diagnostic default rather than an unassigned ldloc.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var intType = app.SystemTypes.SystemInt32Type;
        var dest = new LocalVariable("dest", new Register(null, "dest")) { Type = intType };
        var entry = new LocalVariable("entry", new Register(8, "X8")) { Type = intType };
        var module = new ModuleDefinition("UndefinedRead.dll");
        SeedCorLibTypes(app, module, intType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, dest, entry),
            new(1, OpCode.Return)], [dest, entry]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("Undefined local")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call), Is.True,
                "the substitution must emit the decompiler-issue call, not just a string");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldloc), Is.False,
                "a never-stored local must not be read with ldloc - that is the CS0165 shape");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stloc), Is.True,
                "the destination keeps its real store");
        });
    }

    [Test]
    public void EscapedEntryRegisterReadKeepsLdloc()
    {
        // Taking a local's address makes its storage writable through the
        // pointer, so the substitution must not fire for it: the & write can
        // be the local's real definition even with no visible store.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var intType = app.SystemTypes.SystemInt32Type;
        var entry = new LocalVariable("entry", new Register(8, "X8")) { Type = intType };
        var dest = new LocalVariable("dest", new Register(null, "dest")) { Type = intType };
        var addressTaker = new LocalVariable("taker", new Register(null, "taker"))
            { Type = new ByRefTypeAnalysisContext(intType) };
        var module = new ModuleDefinition("EscapedRead.dll");
        SeedCorLibTypes(app, module, intType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, addressTaker, new AddressOf(entry)),
            new(1, OpCode.Move, dest, entry),
            new(2, OpCode.Return)], [entry, dest, addressTaker]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldloc), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("Undefined local")), Is.False,
                "an escaped local may hold a `&`-written value; its read must not be substituted");
        });
    }

    [Test]
    public void UnspellableMoveSourceSkipsTheStore()
    {
        // A Move from an unspellable unmanaged memory operand emits only a
        // throwing stub - the old emitter still added the stloc after it, so
        // the store popped a phantom value the verifier rejects. The store is
        // now skipped when the load leaves nothing on the stack.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var intType = app.SystemTypes.SystemInt32Type;
        var dest = new LocalVariable("dest", new Register(null, "dest")) { Type = intType };
        var source = new MemoryOperand(new Register(9, "X9"), addend: 24, accessSize: 8);
        var module = new ModuleDefinition("UnspellableMove.dll");
        SeedCorLibTypes(app, module, intType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, dest, source),
            new(1, OpCode.Return)], [dest]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var throwIndex = il.ToList().FindIndex(i => i.OpCode == CilOpCodes.Throw);
        Assert.Multiple(() =>
        {
            Assert.That(throwIndex, Is.GreaterThanOrEqualTo(0),
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stloc), Is.False,
                "no value reached the stack; the store must not pop a phantom");
        });
    }
}
