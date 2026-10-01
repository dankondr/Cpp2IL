using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.NestedFieldPathLoadTests;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery mechanism: a static field access goes through the class's static_fields
// pointer (castle-recovery#285). `Holder.point.X` is `klass = usage; statics =
// klass->static_fields; [statics + offsetof(point) + offsetof(X)]`. In IL that is
// just ldsflda point + ldfld X: the class pointer and the storage pointer are gone.
public class StaticStructMemberAccessTests
{
    // Holder { static int count @0; static P point @4 }, P { int X @0; int Y @4 }.
    private static (MethodAnalysisContext Caller, MethodDefinition Method) Read(long offset,
        string destination = "value")
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var point = InjectStruct(app, "P");
        InjectField("X", app.SystemTypes.SystemInt32Type, point, 0);
        InjectField("Y", app.SystemTypes.SystemInt32Type, point, 4);
        var holder = InjectClass(app, "Holder");
        foreach (var (name, type, at) in new[] { ("count", app.SystemTypes.SystemInt32Type, 0), ("point", (TypeAnalysisContext)point, 4) })
            holder.Fields.Add(new InjectedFieldAnalysisContext(name, type,
                R.FieldAttributes.Public | R.FieldAttributes.Static, holder, at));
        var module = new ModuleDefinition("Statics.dll");
        Seed(module, app, point, holder);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemIntPtrType);

        var klass = Local("klass", new RuntimeClassTypeAnalysisContext(holder, holder.DeclaringAssembly));
        var statics = Local("statics", new StaticFieldStorageTypeAnalysisContext(holder, holder.DeclaringAssembly));
        var value = Local(destination, app.SystemTypes.SystemInt32Type);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, klass, holder),
            new(1, OpCode.Move, statics, new MemoryOperand(klass, null, 0xB8, 0, 8)),
            new(2, OpCode.Move, value, new MemoryOperand(statics, null, offset, 0, 4)),
            new(3, OpCode.CallVoid, Imm(0x1000), value),
            new(4, OpCode.Return)], [klass, statics, value]);

        MetadataResolver.ResolveFieldOffsets(caller);
        DeadCodeEliminator.Run(caller);
        IlGenerator.GenerateIl(caller, method);
        return (caller, method);
    }

    private static Immediate Imm(long value) => new(value);

    private static bool Has(MethodDefinition method, CilOpCode opCode, string member)
        => method.CilMethodBody!.Instructions.Any(i => i.OpCode == opCode
            && i.Operand is IMemberDescriptor descriptor && descriptor.Name == member);

    [Test]
    public void NarrowReadAtTheStartOfAStaticStructIsItsFirstMember()
    {
        // Four bytes at 4 are point.X, not the eight-byte point.
        var (_, method) = Read(4);

        Assert.Multiple(() =>
        {
            Assert.That(Has(method, CilOpCodes.Ldsflda, "point") && Has(method, CilOpCodes.Ldfld, "X"),
                Is.True, () => Dump(method));
            Assert.That(Has(method, CilOpCodes.Ldsfld, "point"), Is.False, () => Dump(method));
        });
    }

    [Test]
    public void MemberOfAStaticStructLeavesNoClassPointer()
    {
        // point.Y is rooted in the static `point`: nothing reads the storage pointer,
        // so neither it nor the class pointer feeding it reaches IL as ldtoken + get_Value.
        var (caller, method) = Read(8);

        Assert.Multiple(() =>
        {
            Assert.That(Has(method, CilOpCodes.Ldsflda, "point") && Has(method, CilOpCodes.Ldfld, "Y"),
                Is.True, () => Dump(method));
            Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Ldtoken),
                Is.False, () => Dump(method));
            Assert.That(caller.ControlFlowGraph!.Instructions.Any(i => i.Destination is LocalVariable
                { Type: RuntimeClassTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext }),
                Is.False, () => string.Join("\n", caller.ControlFlowGraph!.Instructions));
        });
    }

    [Test]
    public void SimdLoadAtTheStartOfAStaticStructStaysItsLaneZeroView()
    {
        // `ldp s0, s1, [statics + 4]` loads a float aggregate argument: V0 stands for the
        // whole point until lane packing or the packed-register split runs.
        var (caller, _) = Read(4, "V0");

        Assert.That(caller.ControlFlowGraph!.Instructions.Select(i => i.Operands.ElementAtOrDefault(1))
                .OfType<FieldReference>().Any(f => f is { Field.Name: "point", Containers.Count: 0 }),
            Is.True, () => string.Join("\n", caller.ControlFlowGraph!.Instructions));
    }
}
