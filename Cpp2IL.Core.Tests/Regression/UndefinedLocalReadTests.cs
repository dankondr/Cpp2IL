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
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initobj), Is.True,
                "the placeholder is a typed default, not an untyped ldnull");
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldloc),
                Is.EqualTo(il.Count(i => i.OpCode == CilOpCodes.Initobj)),
                "every ldloc must be a typed-default temp, never the never-stored local");
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
    public void SelfCopyMoveLeavesTheLocalUndefined()
    {
        // `Move L, L` is not a definition: the register's only write is its own
        // read, so it still holds no proven value. The source read substitutes
        // the documented default rather than ldloc - the `x = x` shape that
        // reported the self-init sites (castle-recovery#145).
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var intType = app.SystemTypes.SystemInt32Type;
        var entry = new LocalVariable("entry", new Register(8, "X8")) { Type = intType };
        var module = new ModuleDefinition("SelfCopy.dll");
        SeedCorLibTypes(app, module, intType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, entry, entry),
            new(1, OpCode.Return)], [entry]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("Undefined local")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initobj), Is.True,
                "the substituted read is a typed default");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stloc), Is.True,
                "the self-copy's store side is still emitted");
        });
    }

    [Test]
    public void PhiEdgeWithNoLegalCopyStoresDocumentedDefault()
    {
        // A bit-pattern phi whose incoming edge merges an incompatible managed
        // reference: the edge has no legal copy, but skipping it leaves the
        // merged local without a store on that path (CS0165). The edge copies
        // from a never-stored register, which the emitter spells as the
        // documented default, so every incoming path carries a store.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var laneType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "Edge", "Lane", app.SystemTypes.SystemObjectType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        var otherType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "Edge", "Other", app.SystemTypes.SystemObjectType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        var stringType = app.SystemTypes.SystemStringType;
        var boolType = app.SystemTypes.SystemBooleanType;
        var condLocal = new LocalVariable("cond", new Register(0, "X0"), boolType);
        var paramS = new LocalVariable("ps", new Register(1, "X1"), stringType);
        var paramV = new LocalVariable("pv", new Register(2, "X2"), otherType);
        var dest = new LocalVariable("dest", new Register(8, "X8", 1), laneType);
        var stringSlot = new LocalVariable("sslot", new Register(8, "X8", 2), stringType);
        var otherSlot = new LocalVariable("oslot", new Register(8, "X8", 3), otherType);
        var outLocal = new LocalVariable("out", new Register(8, "X8", 4), laneType);
        var module = new ModuleDefinition("PhiEdge.dll");
        SeedCorLibTypes(app, module, laneType, otherType, stringType, boolType,
            app.SystemTypes.SystemVoidType);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.ConditionalJump, new Immediate(0), condLocal),
            new(1, OpCode.Move, stringSlot, paramS),
            new(2, OpCode.Jump, new Immediate(0)),
            new(3, OpCode.Move, otherSlot, paramV),
            new(4, OpCode.Phi, dest, stringSlot, otherSlot),
            new(5, OpCode.Move, outLocal, dest),
            new(6, OpCode.Return),
        };
        instructions[0].SetOperand(0, instructions[3]);
        instructions[2].SetOperand(0, instructions[4]);
        var (caller, method) = ForeignCaller(app, module, instructions,
            [condLocal, paramS, paramV, stringSlot, otherSlot, dest, outLocal]);
        caller.ParameterLocals = [condLocal, paramS, paramV];

        SsaForm.Remove(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Initobj), Is.EqualTo(2),
                () => "each unspellable edge stores one typed default\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("Undefined local")),
                Is.EqualTo(2), "each edge names its missing value");
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Stloc),
                Is.GreaterThanOrEqualTo(3), "both edge stores plus the merge read");
        });
    }

    [Test]
    public void ByRefPhiEdgeSkipsTheUnstoreableCopy()
    {
        // The unspellable-edge default does not apply to managed-pointer
        // destinations: a `ref` to a block-scoped temp breaks the escape rules
        // and a null managed pointer is not verifier-legal, so the edge stays
        // unstoreable rather than inventing a `&` value.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var laneType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "Edge", "Lane", app.SystemTypes.SystemObjectType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        var otherType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "Edge", "Other", app.SystemTypes.SystemObjectType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        var laneRef = new ByRefTypeAnalysisContext(laneType);
        var otherRef = new ByRefTypeAnalysisContext(otherType);
        var boolType = app.SystemTypes.SystemBooleanType;
        var condLocal = new LocalVariable("cond", new Register(0, "X0"), boolType);
        var paramA = new LocalVariable("pa", new Register(1, "X1"), laneRef);
        var paramB = new LocalVariable("pb", new Register(2, "X2"), otherRef);
        var laneSlot = new LocalVariable("lslot", new Register(8, "X8", 2), laneRef);
        var otherSlot = new LocalVariable("oslot", new Register(8, "X8", 3), otherRef);
        var dest = new LocalVariable("dest", new Register(8, "X8", 1), laneRef);
        var outLocal = new LocalVariable("out", new Register(8, "X8", 4), laneRef);
        var module = new ModuleDefinition("ByRefPhiEdge.dll");
        SeedCorLibTypes(app, module, laneType, otherType, boolType,
            app.SystemTypes.SystemVoidType);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.ConditionalJump, new Immediate(0), condLocal),
            new(1, OpCode.Move, laneSlot, paramA),
            new(2, OpCode.Jump, new Immediate(0)),
            new(3, OpCode.Move, otherSlot, paramB),
            new(4, OpCode.Phi, dest, laneSlot, otherSlot),
            new(5, OpCode.Move, outLocal, dest),
            new(6, OpCode.Return),
        };
        instructions[0].SetOperand(0, instructions[3]);
        instructions[2].SetOperand(0, instructions[4]);
        var (caller, method) = ForeignCaller(app, module, instructions,
            [condLocal, paramA, paramB, laneSlot, otherSlot, dest, outLocal]);
        caller.ParameterLocals = [condLocal, paramA, paramB];

        SsaForm.Remove(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("unspellable_edge")), Is.False,
                () => "a byref edge must not materialize a phantom source\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initobj), Is.False,
                "no `&` temp default is invented for the skipped edge");
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Stloc), Is.EqualTo(4),
                "each slot and the spellable edge store once; the skipped edge adds none");
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
