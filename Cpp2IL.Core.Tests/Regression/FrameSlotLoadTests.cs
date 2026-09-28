using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: ISIL→IL emission — loads through [X29 ± N]/[stack_N + K]
// frame slots (#111 follow-up). A load of a slot that a store in the same
// method typed reads the slot's synthesized local (ldloc), completing the
// stloc dataflow the store side established. A slot no store typed, or a load
// whose recorded width disagrees with the slot's type, keeps the explicit
// unmanaged-load diagnostic.
public class FrameSlotLoadTests
{
    private static bool LoadsStoredSlot(CilMethodBody body)
    {
        // Some ldloc reads the very local a stloc wrote - the frame slot's
        // synthesized local round-trips store to load.
        var stores = body.Instructions.Where(i => i.OpCode == CilOpCodes.Stloc)
            .Select(i => i.Operand).ToList();
        return body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldloc
            && stores.Any(s => ReferenceEquals(s, i.Operand)));
    }

    private static bool HasUnmanagedLoadDiagnostic(CilMethodBody body) =>
        body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr
            && i.Operand is string text && text.Contains("Unmanaged memory load"));

    [Test]
    public void LoadFromStoredFrameSlotEmitsLdloc()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var module = new ModuleDefinition("FrameSlotLoad.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);
        var frame = new LocalVariable("frame", new Register(null, "X29_v1"));
        var value = new LocalVariable("value", new Register(null, "value")) { Type = int32 };
        var result = new LocalVariable("result", new Register(null, "result")) { Type = int32 };
        // [x29 - 0x18] = value; result = [x29 - 0x18] — a store then a load of
        // the same slot, both 4-byte: they share one synthesized local.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(frame, addend: -0x18, accessSize: 4), value),
            new(1, OpCode.Move, result, new MemoryOperand(frame, addend: -0x18, accessSize: 4)),
            new(2, OpCode.Return)], [frame, value, result]);

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        Assert.Multiple(() =>
        {
            Assert.That(LoadsStoredSlot(body), Is.True,
                "the load must emit ldloc on the same local the store wrote\n"
                    + string.Join("\n", body.Instructions.Select(i => i.ToString())));
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
        });
    }

    [Test]
    public void LoadFromStackSlotEmitsLdloc()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var module = new ModuleDefinition("StackSlotLoad.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);
        // Real stack-slot bases carry the SSA version suffix (stack_40_v2);
        // the version does not change the offset the register names.
        var stack = new LocalVariable("stack", new Register(null, "stack_40_v2"));
        var value = new LocalVariable("value", new Register(null, "value")) { Type = int32 };
        var result = new LocalVariable("result", new Register(null, "result")) { Type = int32 };
        // [stack_40_v2] — the real shape carries the slot offset in the
        // register name with no addend at all.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(stack, addend: 0, accessSize: 4), value),
            new(1, OpCode.Move, result, new MemoryOperand(stack, addend: 0, accessSize: 4)),
            new(2, OpCode.Return)], [stack, value, result]);

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        Assert.Multiple(() =>
        {
            Assert.That(LoadsStoredSlot(body), Is.True,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
        });
    }

    [Test]
    public void LoadFromUnstoredFrameSlotKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var module = new ModuleDefinition("UnstoredSlotLoad.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);
        var frame = new LocalVariable("frame", new Register(null, "X29_v1"));
        var result = new LocalVariable("result", new Register(null, "result")) { Type = int32 };
        // A slot no store typed (a callee-saved spill or incoming stack
        // argument) has no proven type; the load stays diagnosed.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, result, new MemoryOperand(frame, addend: -0x18, accessSize: 4)),
            new(1, OpCode.Return)], [frame, result]);

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        Assert.Multiple(() =>
        {
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldloc), Is.False);
            Assert.That(HasUnmanagedLoadDiagnostic(body), Is.True,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
        });
    }

    [Test]
    public void LoadWithWidthMismatchKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var module = new ModuleDefinition("WidthMismatchLoad.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);
        var frame = new LocalVariable("frame", new Register(null, "X29_v1"));
        var value = new LocalVariable("value", new Register(null, "value")) { Type = int32 };
        var result = new LocalVariable("result", new Register(null, "result")) { Type = int32 };
        // The slot is typed int32 by a 4-byte store; an 8-byte load of it would
        // read past the proven width, so it keeps the diagnostic.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(frame, addend: -0x18, accessSize: 4), value),
            new(1, OpCode.Move, result, new MemoryOperand(frame, addend: -0x18, accessSize: 8)),
            new(2, OpCode.Return)], [frame, value, result]);

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        Assert.Multiple(() =>
        {
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldloc
                && body.Instructions.Any(s => s.OpCode == CilOpCodes.Stloc
                    && ReferenceEquals(s.Operand, i.Operand))), Is.False);
            Assert.That(HasUnmanagedLoadDiagnostic(body), Is.True,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
        });
    }
}
