using System.Linq;
using AsmResolver.DotNet;
using Cpp2IL.Core.Graphs;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: aggregate lane reads (castle-recovery#272).
// A 4- or 8-byte read of a local whose type is an aggregate names the field
// covering exactly those bytes - flat or nested - at the lane's offset, so a
// proven member read emits instead of an aggregate->scalar conversion
// diagnostic. An unspellable covered field (private leaf, unreachable hop)
// keeps the named diagnostic: nothing is invented where the covered member
// cannot be read.
public class AggregateLaneReadTests
{
    private static InjectedTypeAnalysisContext InjectStruct(ApplicationAnalysisContext app, string name) =>
        new(app.AssembliesByName["mscorlib"], "Tests", name,
            app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);

    private static InjectedFieldAnalysisContext AddField(InjectedTypeAnalysisContext owner, string name,
        TypeAnalysisContext type, int offset, R.FieldAttributes attributes = R.FieldAttributes.Public)
    {
        var field = new InjectedFieldAnalysisContext(name, type, attributes, owner, offset);
        owner.Fields.Add(field);
        return field;
    }

    private static void SeedField(FieldAnalysisContext field)
    {
        var definition = new FieldDefinition(field.Name, FieldAttributes.Public,
            new FieldSignature(field.FieldType.ToTypeSignature()));
        field.DeclaringType!.GetExtraData<TypeDefinition>("AsmResolverType")!.Fields.Add(definition);
        field.PutExtraData("AsmResolverField", definition);
    }

    private static bool HasDiagnostic(MethodDefinition method)
        => method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr
            && i.Operand is string text && text.Contains("synthetic default"));

    [Test]
    public void ScalarReadOfAggregateLocalNamesCoveredField()
    {
        // `Move dst <- src` with dst: Single and src: Outer (16 bytes) reads
        // only a field's width - it is `src.inner.x`, not `src`.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var inner = InjectStruct(app, "Inner");
        var x = AddField(inner, "x", app.SystemTypes.SystemSingleType, 0);
        AddField(inner, "y", app.SystemTypes.SystemSingleType, 4);
        var outer = InjectStruct(app, "Outer");
        var innerField = AddField(outer, "inner", inner, 0);
        AddField(outer, "state", app.SystemTypes.SystemInt64Type, 8);
        var module = new ModuleDefinition("Aggregate.dll");
        SeedCorLibTypes(app, module, inner, outer, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemInt64Type, app.SystemTypes.SystemVoidType);
        SeedField(innerField);
        SeedField(x);
        var src = new LocalVariable("src", new Register(null, "V0"), outer);
        var dst = new LocalVariable("dst", new Register(null, "V0"),
            app.SystemTypes.SystemSingleType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, dst, src),
            new(1, OpCode.Return)], [src, dst]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldflda
                    && i.Operand is IFieldDescriptor field && field.Name == "inner"), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldfld
                    && i.Operand is IFieldDescriptor field && field.Name == "x"), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(HasDiagnostic(method), Is.False,
                () => "the covered-field read must not be replaced by a diagnosed default:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void LaneViewReadAtOffsetNamesCoveredField()
    {
        // A `V0.S1` slot addresses bytes [4,8) of the register - the read is the
        // field covering that offset (`outer.inner.y`), not the offset-0 member.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var inner = InjectStruct(app, "Inner");
        AddField(inner, "x", app.SystemTypes.SystemSingleType, 0);
        var y = AddField(inner, "y", app.SystemTypes.SystemSingleType, 4);
        var outer = InjectStruct(app, "Outer");
        var innerField = AddField(outer, "inner", inner, 0);
        AddField(outer, "state", app.SystemTypes.SystemInt64Type, 8);
        var module = new ModuleDefinition("Aggregate.dll");
        SeedCorLibTypes(app, module, inner, outer, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemInt64Type, app.SystemTypes.SystemVoidType);
        SeedField(innerField);
        SeedField(y);
        var src = new LocalVariable("src", new Register(null, "V0"), outer);
        var dst = new LocalVariable("dst", new Register(null, "V0.S1"),
            app.SystemTypes.SystemSingleType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, dst, src),
            new(1, OpCode.Return)], [src, dst]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldflda
                    && i.Operand is IFieldDescriptor field && field.Name == "inner"), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldfld
                    && i.Operand is IFieldDescriptor field && field.Name == "y"), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(HasDiagnostic(method), Is.False,
                () => "the lane-offset read must not be replaced by a diagnosed default:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void ScalarStoreIntoAggregateNamesCoveredField()
    {
        // `Move dst <- src` with dst: Outer and src: Single writes only the
        // lane's width - it is `dst.inner.x = src`, not `dst = src` - when the
        // local's other bytes were already materialized (here by a whole copy).
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var inner = InjectStruct(app, "Inner");
        var x = AddField(inner, "x", app.SystemTypes.SystemSingleType, 0);
        AddField(inner, "y", app.SystemTypes.SystemSingleType, 4);
        var outer = InjectStruct(app, "Outer");
        var innerField = AddField(outer, "inner", inner, 0);
        AddField(outer, "state", app.SystemTypes.SystemInt64Type, 8);
        var module = new ModuleDefinition("Aggregate.dll");
        SeedCorLibTypes(app, module, inner, outer, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemInt64Type, app.SystemTypes.SystemVoidType);
        SeedField(innerField);
        SeedField(x);
        var dst = new LocalVariable("dst", new Register(null, "V0"), outer);
        var whole = new LocalVariable("whole", new Register(null, "V2"), outer);
        var src = new LocalVariable("src", new Register(null, "V1"),
            app.SystemTypes.SystemSingleType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, dst, whole),
            new(1, OpCode.Move, dst, src),
            new(2, OpCode.Return)], [dst, whole, src]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld
                    && i.Operand is IFieldDescriptor field && field.Name == "x"), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(HasDiagnostic(method), Is.False,
                () => "the covered-field store must not be replaced by a diagnosed default:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void UnspellableCoveredFieldKeepsDiagnostic()
    {
        // The covered field at the lane's offset is private - no member read
        // can name it, so the slot keeps its named default diagnostic.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var inner = InjectStruct(app, "Inner");
        AddField(inner, "x", app.SystemTypes.SystemSingleType, 0, R.FieldAttributes.Private);
        AddField(inner, "y", app.SystemTypes.SystemSingleType, 4);
        var outer = InjectStruct(app, "Outer");
        AddField(outer, "inner", inner, 0, R.FieldAttributes.Private);
        AddField(outer, "state", app.SystemTypes.SystemInt64Type, 8);
        var module = new ModuleDefinition("Aggregate.dll");
        SeedCorLibTypes(app, module, inner, outer, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemInt64Type, app.SystemTypes.SystemVoidType);
        var src = new LocalVariable("src", new Register(null, "V0"), outer);
        var dst = new LocalVariable("dst", new Register(null, "V0"),
            app.SystemTypes.SystemSingleType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, dst, src),
            new(1, OpCode.Return)], [src, dst]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(HasDiagnostic(method), Is.True,
            () => "an unspellable covered member must keep the diagnostic:\n"
                + string.Join("\n", il.Select(i => i.ToString())));
    }

    [Test]
    public void RegisterCopyOfWiderAggregateNamesCoveredSpan()
    {
        // `Move dst <- src` on one V register copies 16 bytes: `src` (24 bytes)
        // cannot arrive whole, so naming its whole type in the conversion
        // diagnostic is a smear. The note names the bytes the copy covers.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var wide = InjectStruct(app, "Wide");
        AddField(wide, "head", app.SystemTypes.SystemObjectType, 0);
        AddField(wide, "index", app.SystemTypes.SystemInt32Type, 8);
        AddField(wide, "version", app.SystemTypes.SystemInt32Type, 12);
        AddField(wide, "tail", app.SystemTypes.SystemObjectType, 16);
        var small = InjectStruct(app, "Small");
        AddField(small, "a", app.SystemTypes.SystemSingleType, 0);
        AddField(small, "b", app.SystemTypes.SystemSingleType, 4);
        AddField(small, "c", app.SystemTypes.SystemSingleType, 8);
        var module = new ModuleDefinition("Aggregate.dll");
        SeedCorLibTypes(app, module, wide, small, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemVoidType);
        var src = new LocalVariable("src", new Register(null, "V0"), wide);
        var dst = new LocalVariable("dst", new Register(null, "V0"), small);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, dst, src),
            new(1, OpCode.Return)], [src, dst]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var notes = method.CilMethodBody!.Instructions
            .Where(i => i.OpCode == CilOpCodes.Ldstr && i.Operand is string)
            .Select(i => (string)i.Operand)
            .ToList();
        Assert.Multiple(() =>
        {
            Assert.That(notes.Any(text => text.Contains("covers only part")
                    && text.Contains("Wide") && text.Contains("head")),
                Is.True,
                () => "the covered-span note must name the moved bytes:\n"
                    + string.Join("\n", notes));
            Assert.That(notes.Any(text => text.Contains("No legal conversion")),
                Is.False,
                () => "the whole-type conversion text must not appear:\n"
                    + string.Join("\n", notes));
        });
    }

    [Test]
    public void UnmarkedMoveWidthFallsBackToRegisterCoverage()
    {
        // `NativeMemoryAccessSize` 0 is the float/vector convention for an
        // unmarked move, not a proven zero-width copy: the copy's span falls
        // back to what the destination register carries.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var wide = InjectStruct(app, "Wide");
        AddField(wide, "head", app.SystemTypes.SystemObjectType, 0);
        AddField(wide, "index", app.SystemTypes.SystemInt32Type, 8);
        AddField(wide, "version", app.SystemTypes.SystemInt32Type, 12);
        AddField(wide, "tail", app.SystemTypes.SystemObjectType, 16);
        var small = InjectStruct(app, "Small");
        AddField(small, "a", app.SystemTypes.SystemSingleType, 0);
        AddField(small, "b", app.SystemTypes.SystemSingleType, 4);
        AddField(small, "c", app.SystemTypes.SystemSingleType, 8);
        var module = new ModuleDefinition("Aggregate.dll");
        SeedCorLibTypes(app, module, wide, small, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemVoidType);
        var src = new LocalVariable("src", new Register(null, "V0"), wide);
        var dst = new LocalVariable("dst", new Register(null, "V0"), small);
        var move = new Instruction(0, OpCode.Move, dst, src) { NativeMemoryAccessSize = 0 };
        var (caller, method) = ForeignCaller(app, module, [
            move,
            new(1, OpCode.Return)], [src, dst]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var notes = method.CilMethodBody!.Instructions
            .Where(i => i.OpCode == CilOpCodes.Ldstr && i.Operand is string)
            .Select(i => (string)i.Operand)
            .ToList();
        Assert.Multiple(() =>
        {
            Assert.That(notes.Any(text => text.Contains("16-byte move")),
                Is.True,
                () => "the unmarked move names the register's coverage, not 0 bytes:\n"
                    + string.Join("\n", notes));
            Assert.That(notes.Any(text => text.Contains("0-byte move")),
                Is.False,
                () => "NativeMemoryAccessSize 0 is a convention, not a width:\n"
                    + string.Join("\n", notes));
        });
    }

    [Test]
    public void ThreeLaneAggregateStoreStaysWholeStructStore()
    {
        // `this.backing.x = value`, `.y = value`, `.z = value` on a 12-byte
        // Vec: each leaf store reads the source's lane at its own offset, so
        // the sources narrow to value.x/y/z and inlined-member recovery
        // collapses the run into `this.backing = value` - one whole-struct
        // store, not three field stores.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var vec = InjectStruct(app, "Vec");
        var vx = AddField(vec, "x", app.SystemTypes.SystemSingleType, 0);
        var vy = AddField(vec, "y", app.SystemTypes.SystemSingleType, 4);
        var vz = AddField(vec, "z", app.SystemTypes.SystemSingleType, 8);
        var holder = NestedFieldPathLoadTests.InjectClass(app, "Holder");
        // The container is not writable from the caller - a private backing
        // field - so the run of lane stores is the shape inlined-member
        // recovery collapses to the whole-aggregate store.
        var backing = new InjectedFieldAnalysisContext("<F>k__BackingField", vec,
            R.FieldAttributes.Private, holder, 0x10);
        holder.Fields.Add(backing);
        var module = new ModuleDefinition("Aggregate.dll");
        SeedCorLibTypes(app, module, vec, holder, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemVoidType);
        NestedFieldPathLoadTests.Seed(module, app, holder, vec);
        var receiver = NestedFieldPathLoadTests.Local("receiver", holder);
        var value = NestedFieldPathLoadTests.Local("value", vec);
        // The private container only spells from a member of its own type -
        // the shape a property accessor on the holder has.
        var caller = holder.InjectMethodContext("Run", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            // The low lane arrives as the whole-register read decode spells;
            // the upper lanes already carry their covered-field sources.
            new Instruction(0, OpCode.Move, new FieldReference(vx, receiver, 0, [backing], 4), value),
            new Instruction(1, OpCode.Move, new FieldReference(vy, receiver, 0, [backing], 4),
                new FieldReference(vy, value, 0)),
            new Instruction(2, OpCode.Move, new FieldReference(vz, receiver, 0, [backing], 4),
                new FieldReference(vz, value, 0)),
            new Instruction(3, OpCode.Return)]);
        caller.Locals = [receiver, value];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        holder.GetExtraData<TypeDefinition>("AsmResolverType")!.Methods.Add(method);

        LocalVariables.ResolveTypesAndFields(caller);
        InlinedMemberRecovery.Run(caller);

        // The run collapses to one whole-struct store: the source's low lane
        // narrowed to `value.x`, so all three lanes read as covered fields of
        // `value` and inlined-member recovery emits `backing = value`.
        var moves = caller.ControlFlowGraph.Instructions
            .Where(i => i.OpCode == OpCode.Move).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(moves, Has.Count.EqualTo(1),
                () => "the lane run must collapse to one whole-struct store:\n"
                    + string.Join("\n", caller.ControlFlowGraph.Instructions.Select(i => i.ToString())));
            Assert.That(moves[0].Operands[0], Is.TypeOf<FieldReference>()
                    .And.Matches<FieldReference>(f => f.Field.Name == "<F>k__BackingField"),
                () => "the collapsed store's destination is the container, not a leaf:\n"
                    + string.Join("\n", caller.ControlFlowGraph.Instructions.Select(i => i.ToString())));
            Assert.That(moves[0].Operands[1], Is.SameAs((IOperand)value),
                () => "the collapsed store's source is the whole aggregate:\n"
                    + string.Join("\n", caller.ControlFlowGraph.Instructions.Select(i => i.ToString())));
        });
    }

    [Test]
    public void PartiallyMaterializedAggregateKeepsConversionDiagnostic()
    {
        // `Move color <- 1f` materializes only the low 4 bytes of a 16-byte
        // Color - the covered-field destination is honest only when the value
        // itself was fully written. The narrow store into a wider aggregate
        // keeps its conversion diagnostic instead of silently becoming
        // `default` plus a partial field store.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var color4 = InjectStruct(app, "Color4");
        AddField(color4, "r", app.SystemTypes.SystemSingleType, 0);
        AddField(color4, "g", app.SystemTypes.SystemSingleType, 4);
        AddField(color4, "b", app.SystemTypes.SystemSingleType, 8);
        AddField(color4, "a", app.SystemTypes.SystemSingleType, 12);
        var module = new ModuleDefinition("Aggregate.dll");
        SeedCorLibTypes(app, module, color4, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemVoidType);
        NestedFieldPathLoadTests.Seed(module, app, color4);
        var color = NestedFieldPathLoadTests.Local("color", color4);
        var sink = NestedFieldPathLoadTests.Local("sink", color4);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, color, new FloatLiteral(1f)),
            new(1, OpCode.Move, sink, color),
            new(2, OpCode.Return)], [color, sink]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        Assert.That(HasDiagnostic(method), Is.True,
            () => "a partially materialized aggregate must keep the conversion diagnostic:\n"
                + string.Join("\n", method.CilMethodBody!.Instructions.Select(i => i.ToString())));
    }

    [Test]
    public void SameTypeAggregateCopyStaysWholeCopy()
    {
        // `Move dst <- src` where both locals carry the same aggregate type is
        // a legal whole-value copy, not a lane read - no implicit fill.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var wide = InjectStruct(app, "Wide");
        AddField(wide, "head", app.SystemTypes.SystemObjectType, 0);
        AddField(wide, "index", app.SystemTypes.SystemInt32Type, 8);
        AddField(wide, "version", app.SystemTypes.SystemInt32Type, 12);
        AddField(wide, "tail", app.SystemTypes.SystemObjectType, 16);
        var module = new ModuleDefinition("Aggregate.dll");
        SeedCorLibTypes(app, module, wide, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemVoidType);
        var dst = new LocalVariable("dst", new Register(null, "V0"), wide);
        var src = new LocalVariable("src", new Register(null, "V1"), wide);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, dst, src),
            new(1, OpCode.Return)], [dst, src]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(HasDiagnostic(method), Is.False,
            () => "a same-type aggregate copy stays a whole copy:\n"
                + string.Join("\n", il.Select(i => i.ToString())));
    }
}
