using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: ISIL→IL emission — Object::Unbox helper calls (#74).
// il2cpp_vm_object_unbox takes only the boxed object and returns a pointer into the
// value data; the class the codegen loaded for the wrapper's element_class check is
// the evidence for the unbox type. When nothing resolves it the call keeps an
// explicit diagnostic instead of inventing a type.
public class UnboxEmissionTests
{
    [Test]
    public void UnboxCallWithResolvedValueTypeEmitsUnbox()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var valueType = app.SystemTypes.SystemInt32Type;
        var boxed = new LocalVariable("boxed", new Register(null, "boxed"))
            { Type = app.SystemTypes.SystemObjectType };
        var unboxedPointer = new LocalVariable("unboxedPtr", new Register(null, "unboxedPtr"));
        var value = new LocalVariable("value", new Register(null, "value")) { Type = valueType };
        var module = new ModuleDefinition("Unbox.dll");
        SeedCorLibTypes(app, module, valueType, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(-1, OpCode.Move, boxed, new Immediate(0)),
            new(0, OpCode.Call, new StringLiteral("il2cpp_vm_object_unbox"),
                unboxedPointer, boxed, valueType),
            new(1, OpCode.Move, value, new MemoryOperand(unboxedPointer)),
            new(2, OpCode.Return, value)], [boxed, unboxedPointer, value]);

        KeyFunctionRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Unbox_Any
                    && i.Operand?.ToString().Contains("System.Int32") == true), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldobj
                    && i.Operand?.ToString().Contains("System.Int32") == true), Is.True,
                "whole-value reads of the unbox result lower to ldobj T");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void UnboxCallGuardedByClassCheckResolvesFromTheCheck()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var valueType = app.SystemTypes.SystemInt32Type;
        var boxed = new LocalVariable("boxed", new Register(null, "boxed"))
            { Type = app.SystemTypes.SystemObjectType };
        var unboxedPointer = new LocalVariable("unboxedPtr", new Register(null, "unboxedPtr"));
        var value = new LocalVariable("value", new Register(null, "value")) { Type = valueType };
        var condition = new LocalVariable("cond", new Register(null, "cond"))
            { Type = app.SystemTypes.SystemBooleanType };
        var other = new LocalVariable("other", new Register(null, "other"));
        var module = new ModuleDefinition("UnboxGuard.dll");
        SeedCorLibTypes(app, module, valueType, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemBooleanType);
        // The x1 slot is stale (same local as the object); the evidence is the
        // element_class check the inlined wrapper emitted before the branch.
        var call = new Instruction(3, OpCode.Call, new StringLiteral("il2cpp_vm_object_unbox"),
            unboxedPointer, boxed, boxed);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.CheckEqual, condition, new MemoryOperand(boxed), valueType),
            new(1, OpCode.ConditionalJump, call, condition),
            new(2, OpCode.Move, other, new Immediate(0)),
            call,
            new(4, OpCode.Move, value, new MemoryOperand(unboxedPointer)),
            new(5, OpCode.Return, value)],
            [boxed, unboxedPointer, value, condition, other]);

        KeyFunctionRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Unbox_Any
                    && i.Operand?.ToString().Contains("System.Int32") == true), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldobj
                    && i.Operand?.ToString().Contains("System.Int32") == true), Is.True);
        });
    }

    [Test]
    public void UnboxCallWrittenThroughKeepsExplicitDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var valueType = app.SystemTypes.SystemInt32Type;
        var boxed = new LocalVariable("boxed", new Register(null, "boxed"))
            { Type = app.SystemTypes.SystemObjectType };
        var unboxedPointer = new LocalVariable("unboxedPtr", new Register(null, "unboxedPtr"));
        var value = new LocalVariable("value", new Register(null, "value")) { Type = valueType };
        var module = new ModuleDefinition("UnboxWriteThrough.dll");
        SeedCorLibTypes(app, module, valueType, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        // The lowered form (unbox.any + scratch local + ldloca) exposes a *copy* of
        // the boxed data, so a store through the pointer would silently write the
        // copy and not the box. The call must stay unlifted and diagnosed.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Call, new StringLiteral("il2cpp_vm_object_unbox"),
                unboxedPointer, boxed, valueType),
            new(1, OpCode.Move, new MemoryOperand(unboxedPointer), value),
            new(2, OpCode.Return)], [boxed, unboxedPointer, value]);

        KeyFunctionRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Unbox
                    || i.OpCode == CilOpCodes.Unbox_Any), Is.False,
                "a store through the result must not be lowered to unbox.any");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text
                    && text.Contains("Unknown call target operand")
                    && text.Contains("unbox")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void UnboxCallWithoutResolvableTypeKeepsExplicitDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var boxed = new LocalVariable("boxed", new Register(null, "boxed"))
            { Type = app.SystemTypes.SystemObjectType };
        var unboxedPointer = new LocalVariable("unboxedPtr", new Register(null, "unboxedPtr"));
        var module = new ModuleDefinition("UnboxUnresolved.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        // The x1 slot is a stale copy of the boxed object - not class evidence - and no
        // sibling check names a value type either.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Call, new StringLiteral("il2cpp_vm_object_unbox"),
                unboxedPointer, boxed, boxed),
            new(1, OpCode.Return)], [boxed, unboxedPointer]);

        KeyFunctionRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Unbox
                    || i.OpCode == CilOpCodes.Unbox_Any), Is.False,
                "no unbox may be emitted without a resolved value type");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text
                    && text.Contains("Unknown call target operand")
                    && text.Contains("unbox")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }
}
