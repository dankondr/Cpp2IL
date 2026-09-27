using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: ISIL→IL emission — stores through managed-pointer locals (#86).
// A Move into [local] where the local is a T& lowers to stind/stobj; dropping the
// store leaves out parameters unassigned (CS0177 "out parameter must be assigned").
// A store whose value cannot satisfy the pointee contract keeps the explicit
// diagnostic instead of writing a synthetic default.
public class ManagedPointerStoreTests
{
    [Test]
    public void StoreOfValueTypeThroughManagedPointerEmitsStobj()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"))
            { Type = new ByRefTypeAnalysisContext(int32) };
        var value = new LocalVariable("value", new Register(null, "value")) { Type = int32 };
        var module = new ModuleDefinition("PtrStore.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(pointer, accessSize: 4), value),
            new(1, OpCode.Return)], [pointer, value]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stobj
                    && i.Operand?.ToString().Contains("System.Int32") == true), Is.True,
                "a whole-value store through a T& lowers to stobj T\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void StoreThroughManagedPointerAtOffsetKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"))
            { Type = new ByRefTypeAnalysisContext(int32) };
        var value = new LocalVariable("value", new Register(null, "value")) { Type = int32 };
        var module = new ModuleDefinition("PtrStoreOffset.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemVoidType);
        // [ptr+4] is a partial store - no honest stobj exists, so it stays diagnosed.
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(pointer, addend: 4, accessSize: 4), value),
            new(1, OpCode.Return)], [pointer, value]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stobj), Is.False,
                "a partial store must not be widened to a whole-value stobj");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text
                    && text.Contains("managed-pointer store")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void StoreOfUnsatisfiableValueKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"))
            { Type = new ByRefTypeAnalysisContext(int32) };
        // A struct value cannot honestly satisfy an Int32 store contract; the
        // alternative would be writing a synthetic default(int) - never emitted.
        var blob = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "Tests", "Blob", app.SystemTypes.SystemValueTypeType,
            System.Reflection.TypeAttributes.Public);
        var value = new LocalVariable("value", new Register(null, "value")) { Type = blob };
        var module = new ModuleDefinition("PtrStoreUnsat.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemValueTypeType,
            app.SystemTypes.SystemVoidType, blob);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, new MemoryOperand(pointer, accessSize: 4), value),
            new(1, OpCode.Return)], [pointer, value]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stobj), Is.False,
                "no store may be emitted when the value cannot satisfy the pointee");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text
                    && text.Contains("managed-pointer store")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }
}
