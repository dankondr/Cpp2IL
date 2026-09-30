using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;
using F = AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes;
using T = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: ISIL->IL emission - dereferences past the header of a
// single-dimension managed array that land on a value-typed element (#149).
// A constant offset aligned to the element stride is a real element access;
// an offset inside a flat member is ldelema + ldfld/stfld. Offsets no member
// covers keep the unmanaged diagnostic.
public class ArrayElementFieldAccessTests
{
    private static TypeAnalysisContext SeedElement(ApplicationAnalysisContext app,
        ModuleDefinition module, string name, params (string Name, int Offset)[] fields)
    {
        var single = app.SystemTypes.SystemSingleType;
        var element = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", name,
            app.SystemTypes.SystemValueTypeType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Sealed
                | System.Reflection.TypeAttributes.SequentialLayout);
        var definition = new TypeDefinition("Tests", name,
            T.Public | T.Sealed | T.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(definition);
        element.PutExtraData("AsmResolverType", definition);
        foreach (var (fieldName, offset) in fields)
        {
            var field = new InjectedFieldAnalysisContext(fieldName, single,
                System.Reflection.FieldAttributes.Public, element, offset);
            element.Fields.Add(field);
            var fieldDefinition = new FieldDefinition(fieldName, F.Public,
                new FieldSignature(module.CorLibTypeFactory.Single));
            definition.Fields.Add(fieldDefinition);
            field.PutExtraData("AsmResolverField", fieldDefinition);
        }
        return element;
    }

    private static string Emit(MethodAnalysisContext caller, MethodDefinition method,
        IEnumerable<CilInstruction> il) => string.Join("\n", il.Select(i => i.ToString()));

    [Test]
    public void LoadOfElementFieldEmitsLdelemaLdfld()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var single = app.SystemTypes.SystemSingleType;
        var module = new ModuleDefinition("ElementFieldLoad.dll");
        SeedCorLibTypes(app, module, single, app.SystemTypes.SystemValueTypeType,
            app.SystemTypes.SystemVoidType);
        // stride 8, members at +0 and +4
        var element = SeedElement(app, module, "Pair", ("x", 0), ("y", 4));
        var array = new LocalVariable("array", new Register(null, "array"))
            { Type = new SzArrayTypeAnalysisContext(element) };
        var result = new LocalVariable("result", new Register(null, "result")) { Type = single };
        // [array + 36] = elements + 4 = array[0].y
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, result, new MemoryOperand(array, addend: 36, accessSize: 4)),
            new(1, OpCode.Return)], [array, result]);
        // The array models an entry-live value: nothing stores it in this body.
        caller.ParameterLocals = [array];

        ArrayRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldelema
                    && i.Operand?.ToString().Contains("Pair") == true), Is.True,
                () => Emit(caller, method, il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldfld
                    && i.Operand?.ToString().Contains("y") == true), Is.True,
                () => Emit(caller, method, il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => Emit(caller, method, il));
        });
    }

    [Test]
    public void StoreToElementFieldEmitsLdelemaStfld()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var single = app.SystemTypes.SystemSingleType;
        var module = new ModuleDefinition("ElementFieldStore.dll");
        SeedCorLibTypes(app, module, single, app.SystemTypes.SystemValueTypeType,
            app.SystemTypes.SystemVoidType);
        var element = SeedElement(app, module, "Pair", ("x", 0), ("y", 4));
        var array = new LocalVariable("array", new Register(null, "array"))
            { Type = new SzArrayTypeAnalysisContext(element) };
        var value = new LocalVariable("value", new Register(null, "value")) { Type = single };
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(array, addend: 36, accessSize: 4), value),
            new(1, OpCode.Return)], [array, value]);
        // The array and the stored value model entry-live values.
        caller.ParameterLocals = [array, value];

        ArrayRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldelema), Is.True,
                () => Emit(caller, method, il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld
                    && i.Operand?.ToString().Contains("y") == true), Is.True,
                () => Emit(caller, method, il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => Emit(caller, method, il));
        });
    }

    [Test]
    public void WholeElementLoadEmitsLdelem()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var single = app.SystemTypes.SystemSingleType;
        var module = new ModuleDefinition("WholeElement.dll");
        SeedCorLibTypes(app, module, single, app.SystemTypes.SystemValueTypeType,
            app.SystemTypes.SystemVoidType);
        var element = SeedElement(app, module, "Pair", ("x", 0), ("y", 4));
        var array = new LocalVariable("array", new Register(null, "array"))
            { Type = new SzArrayTypeAnalysisContext(element) };
        var result = new LocalVariable("result", new Register(null, "result")) { Type = element };
        // [array + 40] = elements + 8 = array[1] in a stride-8 array
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, result, new MemoryOperand(array, addend: 40, accessSize: 8)),
            new(1, OpCode.Return)], [array, result]);
        // The array models an entry-live value: nothing stores it in this body.
        caller.ParameterLocals = [array];

        ArrayRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldelem), Is.True,
                () => Emit(caller, method, il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => Emit(caller, method, il));
        });
    }

    [Test]
    public void MemberStoreBesideWholeElementStoreIsNotDropped()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var single = app.SystemTypes.SystemSingleType;
        var module = new ModuleDefinition("AdjacentElementStore.dll");
        SeedCorLibTypes(app, module, single, app.SystemTypes.SystemValueTypeType,
            app.SystemTypes.SystemVoidType);
        var element = SeedElement(app, module, "Pair", ("x", 0), ("y", 4));
        var array = new LocalVariable("array", new Register(null, "array"))
            { Type = new SzArrayTypeAnalysisContext(element) };
        var pair = new LocalVariable("pair", new Register(null, "pair")) { Type = element };
        var y = new LocalVariable("y", new Register(null, "y")) { Type = single };
        // array[0] = pair; array[0].y = y — the second store is a real write to
        // the same element span and must survive beside the whole-element store.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(array, addend: 32, accessSize: 8), pair),
            new(1, OpCode.Move, new MemoryOperand(array, addend: 36, accessSize: 4), y),
            new(2, OpCode.Return)], [array, pair, y]);

        ArrayRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldelema), Is.True,
                () => Emit(caller, method, il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld
                    && i.Operand?.ToString().Contains("y") == true), Is.True,
                () => Emit(caller, method, il));
        });
    }

    [Test]
    public void SliceStoreBesideWholeElementStoreIsDropped()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var single = app.SystemTypes.SystemSingleType;
        var module = new ModuleDefinition("SliceElementStore.dll");
        SeedCorLibTypes(app, module, single, app.SystemTypes.SystemValueTypeType,
            app.SystemTypes.SystemVoidType);
        var element = SeedElement(app, module, "Pair", ("x", 0), ("y", 4));
        var array = new LocalVariable("array", new Register(null, "array"))
            { Type = new SzArrayTypeAnalysisContext(element) };
        var pair = new LocalVariable("pair", new Register(null, "pair")) { Type = element };
        // array[0] = pair lowered to a whole store plus a leftover piece store of
        // the same value's second slice — the piece is redundant and must go.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(array, addend: 32, accessSize: 8), pair),
            new(1, OpCode.Move, new MemoryOperand(array, addend: 36, accessSize: 4),
                new MemoryOperand(pair, addend: 4, accessSize: 4)),
            new(2, OpCode.Return)], [array, pair]);

        ArrayRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stelem), Is.True,
                () => Emit(caller, method, il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld), Is.False,
                () => Emit(caller, method, il));
        });
    }

    [Test]
    public void InteriorOffsetWithoutMemberKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var single = app.SystemTypes.SystemSingleType;
        var module = new ModuleDefinition("ElementGap.dll");
        SeedCorLibTypes(app, module, single, app.SystemTypes.SystemValueTypeType,
            app.SystemTypes.SystemVoidType);
        var element = SeedElement(app, module, "Pair", ("x", 0), ("y", 4));
        var array = new LocalVariable("array", new Register(null, "array"))
            { Type = new SzArrayTypeAnalysisContext(element) };
        var result = new LocalVariable("result", new Register(null, "result")) { Type = single };
        // [array + 34] lands two bytes into array[0].x: unprovable
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, result, new MemoryOperand(array, addend: 34, accessSize: 4)),
            new(1, OpCode.Return)], [array, result]);

        ArrayRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.True);
    }
}
