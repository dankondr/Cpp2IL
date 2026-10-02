using System.Linq;
using AsmResolver.DotNet;
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
        // lane's width - it is `dst.inner.x = src`, not `dst = src`.
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
        var src = new LocalVariable("src", new Register(null, "V1"),
            app.SystemTypes.SystemSingleType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, dst, src),
            new(1, OpCode.Return)], [dst, src]);

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
