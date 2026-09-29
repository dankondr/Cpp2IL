using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;
using F = AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes;
using T = AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: ISIL→IL emission — stores into fields nested inside a
// value-typed member (#142). A Move into [base + K] where K lands strictly
// inside a struct field is `base.outer.inner = v`: the lifter descends the
// value-typed containers to the member the binary actually writes. Interior
// offsets with no exact covering member keep the drop diagnostic.
public class NestedFieldStoreTests
{
    private static FieldAnalysisContext SeedField(ModuleDefinition module, TypeAnalysisContext owner,
        string name, TypeAnalysisContext fieldType, int offset)
    {
        var field = new InjectedFieldAnalysisContext(name, fieldType,
            System.Reflection.FieldAttributes.Public, owner, offset);
        owner.Fields.Add(field);
        var definition = owner.GetExtraData<TypeDefinition>("AsmResolverType")!;
        var fieldDefinition = new FieldDefinition(name, F.Public,
            new FieldSignature(fieldType.GetExtraData<TypeSignature>("AsmResolverSignature")
                ?? module.CorLibTypeFactory.CorLibScope.CreateTypeReference(fieldType.Namespace, fieldType.Name)
                    .ToTypeSignature(fieldType.IsValueType)));
        definition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        return field;
    }

    private static TypeAnalysisContext SeededOwner(ApplicationAnalysisContext app,
        ModuleDefinition module, string name, TypeAnalysisContext baseType)
    {
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", name,
            baseType, System.Reflection.TypeAttributes.Public);
        var definition = new TypeDefinition("Tests", name,
            T.Public | (baseType.IsValueType ? T.Sealed | T.SequentialLayout : T.Class),
            baseType.IsValueType
                ? module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType")
                : module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(definition);
        owner.PutExtraData("AsmResolverType", definition);
        return owner;
    }

    [Test]
    public void StoreToStructTypedMemberEmitsStfld()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var int64 = app.SystemTypes.SystemInt64Type;
        var module = new ModuleDefinition("NestedStore.dll");
        SeedCorLibTypes(app, module, int32, int64, app.SystemTypes.SystemValueTypeType,
            app.SystemTypes.SystemVoidType);
        var point = SeededOwner(app, module, "Point", app.SystemTypes.SystemValueTypeType);
        SeedField(module, point, "x", int32, 0);
        var wrapper = SeededOwner(app, module, "Wrapper", app.SystemTypes.SystemValueTypeType);
        SeedField(module, wrapper, "head", int64, 0);
        SeedField(module, wrapper, "point", point, 8);
        var owner = SeededOwner(app, module, "Machine", app.SystemTypes.SystemObjectType);
        SeedField(module, owner, "outer", wrapper, 0x10);
        var holder = new LocalVariable("holder", new Register(null, "holder")) { Type = owner };
        var value = new LocalVariable("value", new Register(null, "value")) { Type = point };
        // [holder + 0x18] covers holder.outer.point exactly; the source carries
        // a Point, so the whole member store is the faithful spelling.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(holder, addend: 0x18, accessSize: 4), value),
            new(1, OpCode.Return)], [holder, value]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldflda
                    && i.Operand?.ToString().Contains("outer") == true), Is.True,
                "the receiver of the nested store is &holder.outer\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld
                    && i.Operand?.ToString().Contains("point") == true), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void StoreToReadonlyStructMemberKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int64 = app.SystemTypes.SystemInt64Type;
        var module = new ModuleDefinition("ReadonlyStore.dll");
        SeedCorLibTypes(app, module, int64, app.SystemTypes.SystemValueTypeType,
            app.SystemTypes.SystemVoidType);
        var token = SeededOwner(app, module, "Token", app.SystemTypes.SystemValueTypeType);
        SeedField(module, token, "source", app.SystemTypes.SystemObjectType, 0);
        var wrapper = SeededOwner(app, module, "Wrapper", app.SystemTypes.SystemValueTypeType);
        var leaf = new InjectedFieldAnalysisContext("token", token,
            System.Reflection.FieldAttributes.Public | System.Reflection.FieldAttributes.InitOnly,
            wrapper, 8);
        wrapper.Fields.Add(leaf);
        var definition = wrapper.GetExtraData<TypeDefinition>("AsmResolverType")!;
        var leafDefinition = new FieldDefinition("token", F.Public | F.InitOnly,
            new FieldSignature(module.CorLibTypeFactory.CorLibScope
                .CreateTypeReference("Tests", "Token").ToTypeSignature(true)));
        definition.Fields.Add(leafDefinition);
        leaf.PutExtraData("AsmResolverField", leafDefinition);
        var owner = SeededOwner(app, module, "Machine", app.SystemTypes.SystemObjectType);
        SeedField(module, owner, "outer", wrapper, 0x10);
        var holder = new LocalVariable("holder", new Register(null, "holder")) { Type = owner };
        var value = new LocalVariable("value", new Register(null, "value")) { Type = token };
        // [holder + 0x18] covers holder.outer.token exactly, but token is
        // readonly: stfld is invalid outside the .ctor, and every
        // write-through-address spelling ilspy can render (a folded
        // ldflda + stobj store, a ref readonly local) still violates C#'s
        // readonly rule - the store keeps its named diagnostic.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(holder, addend: 0x18, accessSize: 8), value),
            new(1, OpCode.Return)], [holder, value]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stobj), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand?.ToString().Contains("unmanaged memory") == true), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void StoreInsideTwoStructLevelsEmitsNestedStfld()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var int64 = app.SystemTypes.SystemInt64Type;
        var module = new ModuleDefinition("DeepNestedStore.dll");
        SeedCorLibTypes(app, module, int32, int64, app.SystemTypes.SystemValueTypeType,
            app.SystemTypes.SystemVoidType);
        var leaf = SeededOwner(app, module, "Leaf", app.SystemTypes.SystemValueTypeType);
        SeedField(module, leaf, "value", int32, 0);
        var middle = SeededOwner(app, module, "Middle", app.SystemTypes.SystemValueTypeType);
        SeedField(module, middle, "inner", leaf, 8);
        var owner = SeededOwner(app, module, "Machine", app.SystemTypes.SystemObjectType);
        SeedField(module, owner, "outer", middle, 0x10);
        var holder = new LocalVariable("holder", new Register(null, "holder")) { Type = owner };
        var value = new LocalVariable("value", new Register(null, "value")) { Type = int32 };
        // [holder + 0x18] reaches holder.outer.inner.value.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(holder, addend: 0x18, accessSize: 4), value),
            new(1, OpCode.Return)], [holder, value]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldflda
                    && i.Operand?.ToString().Contains("outer") == true), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldflda
                    && i.Operand?.ToString().Contains("inner") == true), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld
                    && i.Operand?.ToString().Contains("value") == true), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void StoreInsideStructFieldWithWrongWidthKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var int64 = app.SystemTypes.SystemInt64Type;
        var module = new ModuleDefinition("NarrowNestedStore.dll");
        SeedCorLibTypes(app, module, int32, int64, app.SystemTypes.SystemValueTypeType,
            app.SystemTypes.SystemVoidType);
        var wrapper = SeededOwner(app, module, "Wrapper", app.SystemTypes.SystemValueTypeType);
        SeedField(module, wrapper, "payload", int64, 8);
        var owner = SeededOwner(app, module, "Machine", app.SystemTypes.SystemObjectType);
        SeedField(module, owner, "outer", wrapper, 0x10);
        var holder = new LocalVariable("holder", new Register(null, "holder")) { Type = owner };
        var value = new LocalVariable("value", new Register(null, "value")) { Type = int32 };
        // A 4-byte store at payload's boundary covers half the field; no
        // managed write can name it faithfully, so the diagnostic stays.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(holder, addend: 0x18, accessSize: 4), value),
            new(1, OpCode.Return)], [holder, value]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text
                    && text.Contains("unmanaged memory form")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void StoreInsideReferenceFieldKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var module = new ModuleDefinition("RefNestedStore.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);
        var owner = SeededOwner(app, module, "Machine", app.SystemTypes.SystemObjectType);
        SeedField(module, owner, "reference", app.SystemTypes.SystemObjectType, 0x10);
        var holder = new LocalVariable("holder", new Register(null, "holder")) { Type = owner };
        var value = new LocalVariable("value", new Register(null, "value")) { Type = int32 };
        // [holder + 0x14] is inside a reference-typed field's storage: pointer
        // interior, not a managed member.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(holder, addend: 0x14, accessSize: 4), value),
            new(1, OpCode.Return)], [holder, value]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text
                    && text.Contains("unmanaged memory form")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    // A nested store through a `ctx&` receiver spells `ctx.outer.point = v` —
    // its first ldflda reads `ctx.outer`, which C# only allows once ctx is
    // definitely assigned. On an `out` parameter it never is (CS0170), so the
    // store keeps the diagnostic; on `ref` the caller assigns it, so the same
    // shape still recovers.
    private static (MethodAnalysisContext caller, MethodDefinition method)
        ByRefCaller(ApplicationAnalysisContext app, ModuleDefinition module,
            List<Instruction> instructions, List<LocalVariable> locals,
            ByRefTypeAnalysisContext ctxByRef, System.Reflection.ParameterAttributes direction)
    {
        var callerType = new InjectedTypeAnalysisContext(
            app.AssembliesByName["UnityEngine.CoreModule"], "Tests", "ForeignCaller",
            app.SystemTypes.SystemObjectType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        var caller = new InjectedMethodAnalysisContext(callerType, "Run",
            app.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static,
            [ctxByRef], ["ctx"], [direction]);
        callerType.Methods.Add(caller);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        caller.Locals = locals;
        caller.ParameterLocals = [locals[0]];
        caller.ParameterOperands = [locals[0].Register];
        caller.AnalysisWarnings = [];
        var type = new TypeDefinition("Tests", "ForeignCaller",
            T.Public | T.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);
        return (caller, method);
    }

    private static (TypeAnalysisContext point, TypeAnalysisContext machine)
        NestedFixture(ApplicationAnalysisContext app, ModuleDefinition module)
    {
        var int32 = app.SystemTypes.SystemInt32Type;
        var int64 = app.SystemTypes.SystemInt64Type;
        SeedCorLibTypes(app, module, int32, int64, app.SystemTypes.SystemValueTypeType,
            app.SystemTypes.SystemVoidType);
        var point = SeededOwner(app, module, "Point", app.SystemTypes.SystemValueTypeType);
        SeedField(module, point, "x", int32, 0);
        var wrapper = SeededOwner(app, module, "Wrapper", app.SystemTypes.SystemValueTypeType);
        SeedField(module, wrapper, "point", point, 8);
        var machine = SeededOwner(app, module, "Machine", app.SystemTypes.SystemObjectType);
        SeedField(module, machine, "outer", wrapper, 0x10);
        return (point, machine);
    }

    [Test]
    public void StoreInsideOutParameterReceiverKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("OutParamStore.dll");
        var (point, machine) = NestedFixture(app, module);
        var ctxByRef = new ByRefTypeAnalysisContext(machine);
        var ctx = new LocalVariable("ctx", new Register(null, "ctx")) { Type = ctxByRef };
        var value = new LocalVariable("value", new Register(null, "value")) { Type = point };
        var (caller, method) = ByRefCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(ctx, addend: 0x18, accessSize: 4), value),
            new(1, OpCode.Return)], [ctx, value], ctxByRef,
            System.Reflection.ParameterAttributes.Out);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text
                    && text.Contains("managed-pointer store")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void StoreInsideRefParameterReceiverEmitsStfld()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("RefParamStore.dll");
        var (point, machine) = NestedFixture(app, module);
        var ctxByRef = new ByRefTypeAnalysisContext(machine);
        var ctx = new LocalVariable("ctx", new Register(null, "ctx")) { Type = ctxByRef };
        var value = new LocalVariable("value", new Register(null, "value")) { Type = point };
        var (caller, method) = ByRefCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(ctx, addend: 0x18, accessSize: 4), value),
            new(1, OpCode.Return)], [ctx, value], ctxByRef,
            System.Reflection.ParameterAttributes.None);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld
                    && i.Operand?.ToString().Contains("point") == true), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }
}
