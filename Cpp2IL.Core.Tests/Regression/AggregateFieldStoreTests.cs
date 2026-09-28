using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using LibCpp2IL.BinaryStructures;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: ref-struct operand drops (castle-recovery#129).
// A Move that stores into a whole struct-typed local but records less than the
// struct's width is an interior store - `new T(field)` lowers to exactly those
// stores - so the destination rewrites to the covered field and the operand
// emits as a real stfld instead of a diagnosed synthetic default.
public class AggregateFieldStoreTests
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

    private static void AssertNoDiagnosticSubstitution(MethodDefinition method)
    {
        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                && i.Operand is string text && text.Contains("Ref struct cannot cross")), Is.False,
            () => "the store must not be replaced by a diagnosed default:\n"
                + string.Join("\n", il.Select(i => i.ToString())));
    }

    [Test]
    public void StructOperandStoresIntoUniquelyTypedField()
    {
        // `Move slot <- src` with slot: Outer (16 bytes) and src: Inner (8) writes
        // only a field's width - it is `slot.inner = src`, not `slot = src`.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var inner = InjectStruct(app, "Inner");
        AddField(inner, "x", app.SystemTypes.SystemInt32Type, 0);
        AddField(inner, "y", app.SystemTypes.SystemInt32Type, 4);
        var outer = InjectStruct(app, "Outer");
        var innerField = AddField(outer, "inner", inner, 0);
        AddField(outer, "state", app.SystemTypes.SystemInt64Type, 8);
        var module = new ModuleDefinition("Aggregate.dll");
        SeedCorLibTypes(app, module, inner, outer, app.SystemTypes.SystemVoidType);
        SeedField(innerField);
        var slot = new LocalVariable("slot", new Register(null, "slot"), outer);
        var src = new LocalVariable("src", new Register(null, "src"), inner);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, src),
            new(1, OpCode.Return)], [slot, src]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld
                    && i.Operand is IFieldDescriptor field && field.Name == "inner"), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            AssertNoDiagnosticSubstitution(method);
        });
    }

    [Test]
    public void ZeroIntoAggregateSlotStoresNullIntoLeadingReferenceField()
    {
        // A literal zero covering a struct slot's leading reference field is
        // `slot.field = null`, not a dropped whole-struct value.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var outer = InjectStruct(app, "Outer");
        var bufferField = AddField(outer, "buffer",
            new SzArrayTypeAnalysisContext(app.SystemTypes.SystemByteType), 0);
        AddField(outer, "state", app.SystemTypes.SystemInt64Type, 8);
        var module = new ModuleDefinition("Aggregate.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemByteType, outer,
            app.SystemTypes.SystemVoidType);
        SeedField(bufferField);
        var slot = new LocalVariable("slot", new Register(null, "slot"), outer);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, new Immediate(0)),
            new(1, OpCode.Return)], [slot]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld
                    && i.Operand is IFieldDescriptor field && field.Name == "buffer"), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            AssertNoDiagnosticSubstitution(method);
        });
    }

    [Test]
    public void ZeroIntoInitonlyFieldKeepsDiagnostic()
    {
        // The same store into a slot whose fields are all initonly cannot spell
        // a legal store outside the declaring .ctor - the named diagnostic stays.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var outer = InjectStruct(app, "Outer");
        AddField(outer, "buffer", new SzArrayTypeAnalysisContext(app.SystemTypes.SystemByteType),
            0, R.FieldAttributes.Public | R.FieldAttributes.InitOnly);
        AddField(outer, "state", app.SystemTypes.SystemInt64Type, 8);
        var module = new ModuleDefinition("Aggregate.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemByteType, outer,
            app.SystemTypes.SystemVoidType);
        var slot = new LocalVariable("slot", new Register(null, "slot"), outer);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, new Immediate(0)),
            new(1, OpCode.Return)], [slot]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("synthetic default")), Is.True,
                () => "the diagnostic must be kept when no field store can emit:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void ArrayDataPointerStoresIntoLeadingSpanField()
    {
        // `arr + 32` is `&arr[0]` (the il2cpp array-data offset). Stored into a
        // leading span field it is the span-of-array .ctor - `new Span(arr)` -
        // which writes the same pointer plus the array's own length.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var byteType = app.SystemTypes.SystemByteType;
        var byteArray = new SzArrayTypeAnalysisContext(byteType);
        var spanDefinition = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "System", "ReadOnlySpan`1", app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        var t = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            R.GenericParameterAttributes.None, spanDefinition);
        spanDefinition.GenericParameters.Add(t);
        AddField(spanDefinition, "_pointer", app.SystemTypes.SystemIntPtrType, 0);
        AddField(spanDefinition, "_length", app.SystemTypes.SystemIntPtrType, 8);
        spanDefinition.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.SpecialName | R.MethodAttributes.RTSpecialName,
            new SzArrayTypeAnalysisContext(t));
        var spanType = new GenericInstanceTypeAnalysisContext(spanDefinition, [byteType]);
        var outer = InjectStruct(app, "Outer");
        var bufferField = AddField(outer, "buffer", spanType, 0);
        AddField(outer, "state", app.SystemTypes.SystemInt64Type, 16);
        var module = new ModuleDefinition("Aggregate.dll");
        SeedCorLibTypes(app, module, byteType, spanDefinition, outer, app.SystemTypes.SystemVoidType);
        SeedField(bufferField);
        var array = new LocalVariable("array", new Register(null, "array"), byteArray);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"), byteArray);
        var slot = new LocalVariable("slot", new Register(null, "slot"), outer);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, pointer, array),
            new(1, OpCode.Add, pointer, pointer, new Immediate(32)),
            new(2, OpCode.Move, slot, pointer),
            new(3, OpCode.Return)], [array, pointer, slot]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Newobj), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld
                    && i.Operand is IFieldDescriptor field && field.Name == "buffer"), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            AssertNoDiagnosticSubstitution(method);
        });
    }

    [Test]
    public void ConcreteFieldOnStaleInstantiationRebindsToRefinedReceiver()
    {
        // Type inference refines a generic local after a concrete field
        // reference binds to it (here: bound on Pair<object,object>, refined to
        // Pair<string,object>). The store must emit the member that exists on
        // the receiver's live instantiation - `stfld` against the stale
        // instantiation produces invalid IL.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var objectType = app.SystemTypes.SystemObjectType;
        var stringType = app.SystemTypes.SystemStringType;
        var pairDefinition = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "Tests", "Pair`2", app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        var t1 = new GenericParameterTypeAnalysisContext("T1", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            R.GenericParameterAttributes.None, pairDefinition);
        var t2 = new GenericParameterTypeAnalysisContext("T2", 1, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            R.GenericParameterAttributes.None, pairDefinition);
        pairDefinition.GenericParameters.Add(t1);
        pairDefinition.GenericParameters.Add(t2);
        var item1 = AddField(pairDefinition, "Item1", t1, 0);
        AddField(pairDefinition, "Item2", t2, 8);
        var pairOfStringObject =
            new GenericInstanceTypeAnalysisContext(pairDefinition, [stringType, objectType]);
        var module = new ModuleDefinition("Aggregate.dll");
        SeedCorLibTypes(app, module, objectType, stringType, pairDefinition,
            app.SystemTypes.SystemVoidType);
        SeedField(item1);
        var staleItem1 = item1.MakeConcreteGenericField([objectType, objectType]);
        var slot = new LocalVariable("slot", new Register(null, "slot"), pairOfStringObject);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new FieldReference(staleItem1, slot, 0, [], 8), new Immediate(0)),
            new(1, OpCode.Return)], [slot]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld
                    && i.Operand is IFieldDescriptor field
                    && field.Name == "Item1"
                    && field.DeclaringType!.FullName.Contains("System.String")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            AssertNoDiagnosticSubstitution(method);
        });
    }

    [Test]
    public void PhidArrayDataPointersStoreIntoLeadingSpanField()
    {
        // Both branches compute `arr + 32` on the same array and the phi merges
        // them - the merged store is still `new Span(arr)`, not a dropped value.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var byteType = app.SystemTypes.SystemByteType;
        var byteArray = new SzArrayTypeAnalysisContext(byteType);
        var spanDefinition = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "System", "ReadOnlySpan`1", app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        var t = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            R.GenericParameterAttributes.None, spanDefinition);
        spanDefinition.GenericParameters.Add(t);
        AddField(spanDefinition, "_pointer", app.SystemTypes.SystemIntPtrType, 0);
        AddField(spanDefinition, "_length", app.SystemTypes.SystemIntPtrType, 8);
        spanDefinition.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.SpecialName | R.MethodAttributes.RTSpecialName,
            new SzArrayTypeAnalysisContext(t));
        var spanType = new GenericInstanceTypeAnalysisContext(spanDefinition, [byteType]);
        var outer = InjectStruct(app, "Outer");
        var bufferField = AddField(outer, "buffer", spanType, 0);
        AddField(outer, "state", app.SystemTypes.SystemInt64Type, 16);
        var module = new ModuleDefinition("Aggregate.dll");
        SeedCorLibTypes(app, module, byteType, spanDefinition, outer, app.SystemTypes.SystemVoidType);
        SeedField(bufferField);
        var array = new LocalVariable("array", new Register(null, "array"), byteArray);
        var left = new LocalVariable("left", new Register(null, "left"), byteArray);
        var right = new LocalVariable("right", new Register(null, "right"), byteArray);
        var merged = new LocalVariable("merged", new Register(null, "merged"), byteArray);
        var slot = new LocalVariable("slot", new Register(null, "slot"), outer);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, left, array),
            new(1, OpCode.Add, left, left, new Immediate(32)),
            new(2, OpCode.Move, right, array),
            new(3, OpCode.Add, right, right, new Immediate(32)),
            new(4, OpCode.Phi, merged, left, right),
            new(5, OpCode.Move, slot, merged),
            new(6, OpCode.Return)], [array, left, right, merged, slot]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Newobj), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld
                    && i.Operand is IFieldDescriptor field && field.Name == "buffer"), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            AssertNoDiagnosticSubstitution(method);
        });
    }
}
