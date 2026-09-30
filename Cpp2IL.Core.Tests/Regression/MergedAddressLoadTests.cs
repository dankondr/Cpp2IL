using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.NestedFieldPathLoadTests;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery mechanism (castle-recovery#211): `x = c ? &a.f : &b.g; use(*x)`. The
// compiler merges the addresses of two cells and loads once after the join; the
// load is a merge of the two cell values, each read on its own edge.
public class MergedAddressLoadTests
{
    private sealed record Shape(MethodAnalysisContext Caller, Block Join, Instruction Load, LocalVariable Holder);

    // Holder { string name @0x10; string other @0x18; int count @0x20 }, then
    //   0: if (cond) goto 3   1: slot = "zeros"   2: goto 4   3: nop   4: [join] dst = [p]; return dst
    // with p = phi(left on the 1-2 edge, right on the 3 edge).
    private static Shape Build(string left, string right, bool callBeforeLoad = false)
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var type = InjectClass(app, "Holder");
        InjectField("name", app.SystemTypes.SystemStringType, type, 0x10);
        InjectField("other", app.SystemTypes.SystemStringType, type, 0x18);
        InjectField("count", app.SystemTypes.SystemInt32Type, type, 0x20);
        var module = new ModuleDefinition("Merged.dll");
        Seed(module, app, type);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemStringType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType);

        var holder = Local("holder", type);
        var slot = Local("slot");
        var address = Local("address");
        var dst = Local("dst");
        var cond = Local("cond", app.SystemTypes.SystemBooleanType);
        var right0 = new Instruction(3, OpCode.Nop);
        var load = new Instruction(4, OpCode.Move, dst, new MemoryOperand(address, null, 0, 0, 8));
        var joinStart = callBeforeLoad ? new Instruction(40, OpCode.CallVoid, new Immediate(0x1234)) : load;
        List<Instruction> instructions =
        [
            new(0, OpCode.ConditionalJump, right0, cond),
            new(1, OpCode.Move, slot, new StringLiteral("zeros")),
            new(2, OpCode.Jump, joinStart),
            right0,
        ];
        if (callBeforeLoad)
            instructions.Add(joinStart);
        instructions.AddRange([load, new(5, OpCode.Return, dst)]);
        var (caller, _) = ForeignCaller(app, module, instructions, [holder, slot, address, dst, cond]);

        IOperand Cell(string name) => name == "slot"
            ? slot
            : new AddressOf(new FieldReference(type.Fields.Single(f => f.Name == name), holder, type.Fields.Single(f => f.Name == name).Offset));
        var join = caller.ControlFlowGraph!.Blocks.Single(b => b.Instructions.Contains(joinStart));
        join.Instructions.Insert(0, new Instruction(-1, OpCode.Phi,
            [address, .. join.Predecessors.Select(p => Cell(p.Instructions.Any(i => i.Index == 2) ? left : right))]));
        return new Shape(caller, join, load, holder);
    }

    // What the merged value is on each incoming edge, in predecessor order.
    private static List<string> MergedValues(Shape shape)
    {
        Assert.That(shape.Load.Operands[1], Is.InstanceOf<LocalVariable>());
        var merged = shape.Join.Instructions.Single(i => i.OpCode == OpCode.Phi
            && ReferenceEquals(i.Operands[0], shape.Load.Operands[1]));
        return shape.Join.Predecessors.Select((predecessor, k) =>
        {
            var source = (LocalVariable)merged.Operands[1 + k];
            var move = predecessor.Instructions.SingleOrDefault(i => i.OpCode == OpCode.Move && ReferenceEquals(i.Operands[0], source));
            return move?.Operands[1] is FieldReference field ? field.Field.Name : source.Name;
        }).ToList();
    }

    [Test]
    public void LoadThroughMergedFieldAddressesIsAMergeOfTheFields()
    {
        var shape = Build("name", "other");

        MetadataResolver.LoadThroughMergedAddresses(shape.Caller);

        Assert.That(MergedValues(shape), Is.EquivalentTo(new[] { "name", "other" }));
    }

    [Test]
    public void StringLiteralSlotMergesAsItsValue()
    {
        // `return c ? "zeros" : holder.name`: the slot local already stands for the string.
        var shape = Build("slot", "name");

        MetadataResolver.LoadThroughMergedAddresses(shape.Caller);

        Assert.That(MergedValues(shape), Is.EquivalentTo(new[] { "slot", "name" }));
        Assert.That(((LocalVariable)shape.Load.Operands[1]).Type,
            Is.SameAs(Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemStringType));
    }

    [Test]
    public void CallBetweenJoinAndLoadKeepsTheLoad()
    {
        // The call may write either field after its address was taken.
        var shape = Build("name", "other", callBeforeLoad: true);

        MetadataResolver.LoadThroughMergedAddresses(shape.Caller);

        Assert.That(shape.Load.Operands[1], Is.InstanceOf<MemoryOperand>());
    }

    [Test]
    public void CellsOfDifferentTypesKeepTheLoad()
    {
        var shape = Build("name", "count");

        MetadataResolver.LoadThroughMergedAddresses(shape.Caller);

        Assert.That(shape.Load.Operands[1], Is.InstanceOf<MemoryOperand>());
    }
}
