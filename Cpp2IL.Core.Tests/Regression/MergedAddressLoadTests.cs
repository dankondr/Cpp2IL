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

    // Holder { string name @0x10; string other @0x18; int count @0x20; Point2 start @0x28; Point2 end @0x30 }, then
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
        var point = InjectStruct(app, "Point2");
        InjectField("x", app.SystemTypes.SystemSingleType, point, 0);
        InjectField("y", app.SystemTypes.SystemSingleType, point, 4);
        InjectField("start", point, type, 0x28);
        InjectField("end", point, type, 0x30);
        // static string shared @0; static string fallback @8 (Holder's static block)
        foreach (var (name, offset) in new[] { ("shared", 0), ("fallback", 8) })
            type.Fields.Add(new InjectedFieldAnalysisContext(name, app.SystemTypes.SystemStringType,
                System.Reflection.FieldAttributes.Public | System.Reflection.FieldAttributes.Static, type, offset));
        var module = new ModuleDefinition("Merged.dll");
        Seed(module, app, type, point);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemStringType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemSingleType, app.SystemTypes.SystemObjectType);

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

        // "name" is `&holder.name`; "+name" is `holder + offset`, the form the type and
        // field fixpoint sees before object field addresses are recovered.
        IOperand Cell(string name)
        {
            if (name == "slot")
                return slot;
            if (name.StartsWith("items["))
            {
                // `&items[k]` is items + 0x20 + 8k: the element after the array header.
                var items = Local("items", new SzArrayTypeAnalysisContext(app.SystemTypes.SystemStringType));
                var element = Local($"element_{name}");
                caller.ControlFlowGraph!.Blocks.First().Instructions.Insert(0, new Instruction(-3, OpCode.Add,
                    element, items, new Immediate(0x20 + 8 * int.Parse(name[6..^1]))));
                return element;
            }
            // "copy" is the slot kept in another register: a copy reaches the merge.
            if (name == "copy")
            {
                var copy = Local("copy");
                caller.ControlFlowGraph!.Blocks.First(b => b.Instructions.Any(i => i.Index == 1)).Instructions
                    .Insert(1, new Instruction(-2, OpCode.Move, copy, slot));
                return copy;
            }
            // "static:f" is `[klass + static_fields] + offset` off a class constant, "phi:f" the
            // same off a merge of two different class pointers, "same:f" off a merge of the
            // class with itself (a class-init guard reloads it on one arm).
            if (name.Split(':') is [var kind and ("static" or "phi" or "same"), var staticName])
            {
                var entry = caller.ControlFlowGraph!.Blocks.First().Instructions;
                var klass = Local($"klass_{staticName}", new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly));
                if (kind == "static")
                    entry.Insert(0, new Instruction(-4, OpCode.Move, klass, type));
                else
                {
                    var (a, b) = (Local("klass_a"), Local("klass_b"));
                    entry.InsertRange(0, [new Instruction(-6, OpCode.Move, a, type),
                        new Instruction(-5, OpCode.Move, b, kind == "same" ? type : app.SystemTypes.SystemStringType),
                        new Instruction(-4, OpCode.Phi, klass, a, b)]);
                }
                var staticSum = Local($"sum_{staticName}");
                entry.Insert(kind == "static" ? 1 : 3, new Instruction(-3, OpCode.Add, staticSum,
                    new MemoryOperand(klass, null, app.Binary.is32Bit ? 0x5C : 0xB8, 0, 8),
                    new Immediate(type.Fields.Single(f => f.Name == staticName).Offset)));
                return staticSum;
            }
            // "block" is the static block itself (`ldr x8, [klass + static_fields]`): the
            // address of the static at offset 0.
            if (name == "block")
            {
                var block = Local("block", new StaticFieldStorageTypeAnalysisContext(type, type.DeclaringAssembly));
                caller.ControlFlowGraph!.Blocks.First().Instructions.Insert(0, new Instruction(-4, OpCode.Move, block,
                    new MemoryOperand(Local("klass", new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly)),
                        null, app.Binary.is32Bit ? 0x5C : 0xB8, 0, 8)));
                return block;
            }
            var field = type.Fields.Single(f => f.Name == name.TrimStart('+'));
            if (!name.StartsWith('+'))
                return new AddressOf(new FieldReference(field, holder, field.Offset));
            var sum = Local($"sum_{field.Name}");
            caller.ControlFlowGraph!.Blocks.First().Instructions.Insert(0,
                new Instruction(-3, OpCode.Add, sum, holder, new Immediate(field.Offset)));
            return sum;
        }
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
            return move?.Operands[1] switch
            {
                FieldReference field => field.Field.Name,
                ArrayAccess { Array.Name: var array, Index: Immediate index } => $"{array}[{index.Value}]",
                _ => source.Name,
            };
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
    public void MergedObjectPlusOffsetIsAMergeOfTheFields()
    {
        var shape = Build("+name", "+other");

        MetadataResolver.LoadThroughMergedAddresses(shape.Caller);

        Assert.That(MergedValues(shape), Is.EquivalentTo(new[] { "name", "other" }));
    }

    [Test]
    public void ArrayElementCellMergesAsTheElement()
    {
        // `return c ? holder.name : items[1]`: a constant element address is a cell of its own.
        var shape = Build("name", "items[1]");

        MetadataResolver.LoadThroughMergedAddresses(shape.Caller);

        Assert.That(MergedValues(shape), Is.EquivalentTo(new[] { "name", "items[1]" }));
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
    public void MergedStaticFieldAddressesAreAMergeOfTheStatics()
    {
        // `return c ? Holder.shared : Holder.fallback`: each address is the static block
        // loaded off the class plus the field's offset, with no storage local.
        var shape = Build("static:shared", "static:fallback");

        MetadataResolver.LoadThroughMergedAddresses(shape.Caller);
        DeadCodeEliminator.Run(shape.Caller);

        Assert.That(MergedValues(shape), Is.EquivalentTo(new[] { "shared", "fallback" }));
        // The class pointer only fed the addresses: nothing reads it any more.
        Assert.That(shape.Caller.ControlFlowGraph!.Instructions.Any(i =>
            i is { OpCode: OpCode.Move, Operands: [LocalVariable { Name: var name }, _] } && name.StartsWith("klass")), Is.False);
    }

    [Test]
    public void StaticAndInstanceCellsMerge()
    {
        var shape = Build("name", "static:shared");

        MetadataResolver.LoadThroughMergedAddresses(shape.Caller);

        Assert.That(MergedValues(shape), Is.EquivalentTo(new[] { "name", "shared" }));
    }

    [Test]
    public void StaticBlockIsTheStaticAtItsStart()
    {
        // `return c ? holder.name : Holder.shared`, shared at offset 0 of the block.
        var shape = Build("name", "block");

        MetadataResolver.LoadThroughMergedAddresses(shape.Caller);

        Assert.That(MergedValues(shape), Is.EquivalentTo(new[] { "name", "shared" }));
    }

    [Test]
    public void LoadThroughAMergeOfTheStaticBlockAndAnotherAddressIsNoStaticRead()
    {
        // The merge took the block's type from one input; read through T's layout it
        // would name Holder.shared on the path that holds &holder.other too.
        var shape = Build("block", "+other");
        var address = (LocalVariable)((MemoryOperand)shape.Load.Operands[1]).Base!;
        address.Type = new StaticFieldStorageTypeAnalysisContext(shape.Holder.Type!, shape.Holder.Type!.DeclaringAssembly);

        Assert.That(MetadataResolver.ResolveScalarFieldAccess(shape.Caller, (MemoryOperand)shape.Load.Operands[1]),
            Is.Null);
        MetadataResolver.ResolveFieldOffsets(shape.Caller);
        Assert.That(shape.Load.Operands[1], Is.InstanceOf<MemoryOperand>());
    }

    [Test]
    public void StaticsOffAMergeOfOneClassMerge()
    {
        var shape = Build("same:shared", "static:fallback");

        MetadataResolver.LoadThroughMergedAddresses(shape.Caller);

        Assert.That(MergedValues(shape), Is.EquivalentTo(new[] { "shared", "fallback" }));
    }

    [Test]
    public void StaticsOffAMergeOfClassPointersKeepTheLoad()
    {
        // The class is one of two; the joined type of the merge does not say which.
        var shape = Build("phi:shared", "static:fallback");

        MetadataResolver.LoadThroughMergedAddresses(shape.Caller);

        Assert.That(shape.Load.Operands[1], Is.InstanceOf<MemoryOperand>());
    }

    [Test]
    public void CopyOfASlotMergesAsItsValue()
    {
        var shape = Build("copy", "static:shared");

        MetadataResolver.LoadThroughMergedAddresses(shape.Caller);

        Assert.That(MergedValues(shape), Is.EquivalentTo(new[] { "copy", "shared" }));
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
    public void StructCellsKeepTheLoad()
    {
        // Eight bytes at `&start` are start.x and start.y, not a Point2 value.
        var shape = Build("start", "end");

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

    // entry: if (cond) goto join (edge from a block with two exits)   next: nop   join: use([p])
    private static (MethodAnalysisContext Caller, Instruction Load, LocalVariable Holder) Branching(
        bool branchReadsThis, System.Func<LocalVariable, MemoryOperand, TypeAnalysisContext, Instruction> use,
        string field = "name", bool staticOnBranch = false)
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var type = InjectClass(app, "Holder");
        InjectField("name", app.SystemTypes.SystemStringType, type, 0x10);
        var point = InjectStruct(app, "Point2");
        InjectField("x", app.SystemTypes.SystemSingleType, point, 0);
        InjectField("y", app.SystemTypes.SystemSingleType, point, 4);
        InjectField("start", point, type, 0x18);
        InjectField("end", point, type, 0x20);
        type.Fields.Add(new InjectedFieldAnalysisContext("shared", app.SystemTypes.SystemStringType,
            System.Reflection.FieldAttributes.Public | System.Reflection.FieldAttributes.Static, type, 0));
        var module = new ModuleDefinition("Merged.dll");
        Seed(module, app, type, point);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemStringType, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemObjectType);

        var self = Local("self", type);
        self.IsThis = branchReadsThis;
        var other = Local("other", type);
        var address = Local("address");
        var cond = Local("cond", app.SystemTypes.SystemBooleanType);
        var load = use(address, new MemoryOperand(address, null, 0, 0, 8), point);
        var (caller, _) = ForeignCaller(app, module, [
            new(0, OpCode.ConditionalJump, load, cond),
            new(1, OpCode.Nop),
            load,
            new(3, OpCode.Return)], [self, other, address, cond]);

        IOperand Cell(LocalVariable owner)
        {
            if (staticOnBranch && ReferenceEquals(owner, self))
            {
                // Holder's static block, loaded in the branching block: `&Holder.shared`.
                var block = Local("block", new StaticFieldStorageTypeAnalysisContext(type, type.DeclaringAssembly));
                caller.ControlFlowGraph!.Blocks.First().Instructions.Insert(0, new Instruction(-4, OpCode.Move, block,
                    new MemoryOperand(Local("klass", new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly)),
                        null, app.Binary.is32Bit ? 0x5C : 0xB8, 0, 8)));
                return block;
            }
            var f = type.Fields.Single(candidate => candidate.Name == field);
            var target = field == "name" ? f : point.Fields.Single(candidate => candidate.Name == "x");
            return new AddressOf(field == "name"
                ? new FieldReference(f, owner, f.Offset)
                : new FieldReference(target, owner, f.Offset, [f]));
        }
        var join = caller.ControlFlowGraph!.Blocks.Single(b => b.Instructions.Contains(load));
        join.Instructions.Insert(0, new Instruction(-1, OpCode.Phi,
            [address, .. join.Predecessors.Select(p => Cell(p.Instructions.Any(i => i.Index == 0) ? self : other))]));
        return (caller, load, self);
    }

    [Test]
    public void EdgeFromABranchingBlockMayReadAFieldOfThis()
    {
        var (caller, load, _) = Branching(branchReadsThis: true,
            (address, memory, _) => new Instruction(2, OpCode.Move, Local("dst"), memory));

        MetadataResolver.LoadThroughMergedAddresses(caller);

        Assert.That(load.Operands[1], Is.InstanceOf<LocalVariable>());
    }

    [Test]
    public void EdgeFromABranchingBlockKeepsTheLoadForAnotherObject()
    {
        // `other` may be null where the join is not reached; reading its field there could throw.
        var (caller, load, _) = Branching(branchReadsThis: false,
            (address, memory, _) => new Instruction(2, OpCode.Move, Local("dst"), memory));

        MetadataResolver.LoadThroughMergedAddresses(caller);

        Assert.That(load.Operands[1], Is.InstanceOf<MemoryOperand>());
    }

    [Test]
    public void EdgeFromABranchingBlockMayReadAStatic()
    {
        // A static read cannot fault: its class was initialized before its address was taken.
        var (caller, load, _) = Branching(branchReadsThis: false,
            (address, memory, _) => new Instruction(2, OpCode.Move, Local("dst"), memory), staticOnBranch: true);

        MetadataResolver.LoadThroughMergedAddresses(caller);

        Assert.That(load.Operands[1], Is.InstanceOf<LocalVariable>());
    }

    [Test]
    public void StructPassedWholeMergesTheWholeStructs()
    {
        // Take(c ? start : end): each cell names the struct's first field upstream.
        InjectedMethodAnalysisContext? take = null;
        var (caller, load, _) = Branching(branchReadsThis: true, (address, memory, point) =>
        {
            var app = Cpp2IlApi.CurrentAppContext!;
            take = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Take",
                app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Static, [point]);
            return new Instruction(2, OpCode.CallVoid, take, memory);
        }, field: "start");

        MetadataResolver.LoadThroughMergedAddresses(caller);

        Assert.That(load.Operands[1], Is.InstanceOf<LocalVariable>());
        Assert.That(((LocalVariable)load.Operands[1]).Type?.Name, Is.EqualTo("Point2"));
    }

    [Test]
    public void LoadIntoAStructLocalKeepsTheLoad()
    {
        var (caller, load, _) = Branching(branchReadsThis: true,
            (address, memory, point) => new Instruction(2, OpCode.Move, Local("dst", point), memory), field: "start");

        MetadataResolver.LoadThroughMergedAddresses(caller);

        Assert.That(load.Operands[1], Is.InstanceOf<MemoryOperand>());
    }

    [Test]
    public void LoadWiderThanTheCellKeepsTheLoad()
    {
        // A 16-byte vector load at `&start.x` is not the float `start.x`.
        var (caller, load, _) = Branching(branchReadsThis: true, (address, memory, _) =>
            new Instruction(2, OpCode.Move, Local("dst"), new MemoryOperand(address, null, 0, 0, 0)) { NativeMemoryAccessSize = 16 },
            field: "start");

        MetadataResolver.LoadThroughMergedAddresses(caller);

        Assert.That(load.Operands[1], Is.InstanceOf<MemoryOperand>());
    }
}
