using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.NestedFieldPathLoadTests;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// `foreach (var x in list)`: il2cpp copies the enumerator into a frame slot word by word, the
// word at +0x10 (Current) into its own frame cell, passes &enumerator to MoveNext, then reloads
// that cell. The cell is the struct's Current: SSA must not hand the reload the pre-loop copy.
public class FrameStructFieldReadTests
{
    private static (MethodAnalysisContext Caller, Instruction Reload) Build(bool addressTaken, int cellOffset)
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var enumerator = InjectStruct(app, "Walker");
        InjectField("list", app.SystemTypes.SystemObjectType, enumerator, 0);
        InjectField("index", app.SystemTypes.SystemInt32Type, enumerator, 8);
        var current = InjectField("current", app.SystemTypes.SystemObjectType, enumerator, 0x10);
        var module = new ModuleDefinition("Frame.dll");
        Seed(module, app, enumerator);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemInt32Type);

        var slot = new LocalVariable("slot", new Register(null, "stack_-70"), enumerator);
        var copied = Local("copied", app.SystemTypes.SystemObjectType);
        var cell = new LocalVariable("cell", new Register(null, cellOffset < 0 ? $"stack_-{-cellOffset:X}" : $"stack_{cellOffset:X}"),
            app.SystemTypes.SystemObjectType);
        var item = Local("item", app.SystemTypes.SystemObjectType);
        var reload = new Instruction(3, OpCode.Move, item, cell);
        var (caller, _) = ForeignCaller(app, module, [
            new(0, OpCode.Move, copied, new FieldReference(current, slot, 0x10)),
            new(1, OpCode.Move, cell, copied),
            new(2, OpCode.CallVoid, new Immediate(0x1234), addressTaken ? new AddressOf(slot) : slot),
            reload,
            new(4, OpCode.Return, item)], [slot, copied, cell, item]);
        return (caller, reload);
    }

    [Test]
    public void CellCopyOfAnAddressTakenStructFieldReadsTheField()
    {
        var (caller, reload) = Build(addressTaken: true, cellOffset: -0x60);

        FrameStructFieldReads.Run(caller);

        Assert.That(reload.Operands[1], Is.InstanceOf<FieldReference>());
        Assert.That(((FieldReference)reload.Operands[1]).Field.Name, Is.EqualTo("current"));
    }

    [Test]
    public void StructWhoseAddressNeverEscapesKeepsTheCell()
    {
        var (caller, reload) = Build(addressTaken: false, cellOffset: -0x60);

        FrameStructFieldReads.Run(caller);

        Assert.That(reload.Operands[1], Is.InstanceOf<LocalVariable>());
    }

    [Test]
    public void CellAtAnotherOffsetKeepsTheCell()
    {
        // The copy of Current landed 8 bytes off: that cell is not Current's storage.
        var (caller, reload) = Build(addressTaken: true, cellOffset: -0x58);

        FrameStructFieldReads.Run(caller);

        Assert.That(reload.Operands[1], Is.InstanceOf<LocalVariable>());
    }

    // `var t = new (int, int, int, int)(…); return t;`: the tuple is zeroed in its frame slot,
    // filled by the constructor through &slot, then reloaded as `ldp x0, x1, [slot]; ret`.
    private static Instruction BuildReturn(int highCellOffset)
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        app.InstructionSet = new Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet();
        var quad = InjectStruct(app, "Quad");
        foreach (var (name, offset) in new[] { ("a", 0), ("b", 4), ("c", 8), ("d", 12) })
            InjectField(name, app.SystemTypes.SystemInt32Type, quad, offset);

        var slot = new LocalVariable("slot", new Register(null, "stack_-58"), quad);
        var high = new LocalVariable("high", new Register(null, $"stack_-{0x58 - highCellOffset:X}"), app.SystemTypes.SystemInt64Type);
        var x0 = Local("x0", quad);
        var x1 = Local("x1", app.SystemTypes.SystemInt64Type);
        var ret = new Instruction(4, OpCode.Return, x0, x1);
        var callerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Prices",
            app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        var caller = callerType.InjectMethodContext("Get", quad,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static);
        caller.ControlFlowGraph = new Cpp2IL.Core.Graphs.ISILControlFlowGraph([
            new(0, OpCode.Move, high, new Immediate(0)),
            new(1, OpCode.CallVoid, new Immediate(0x1234), new AddressOf(slot)),
            new(2, OpCode.Move, x0, slot),
            new(3, OpCode.Move, x1, high),
            ret]);
        caller.Locals = [slot, high, x0, x1];
        FrameStructFieldReads.Run(caller);
        return ret;
    }

    [Test]
    public void StructReturnedFromItsFrameSlotReturnsTheSlot()
    {
        var ret = BuildReturn(highCellOffset: 8);

        Assert.That(ret.Operands, Has.Count.EqualTo(1));
        Assert.That(((LocalVariable)ret.Operands[0]).Name, Is.EqualTo("x0"));
    }

    [Test]
    public void HighLaneFromOutsideTheSlotKeepsBothLanes()
    {
        Assert.That(BuildReturn(highCellOffset: 0x10).Operands, Has.Count.EqualTo(2));
    }
}
