using System.Collections.Generic;
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

// Recovery cluster: residual stores of the memory lane (castle-recovery#340).
// The store side of the addressed-storage model: a store through a local every
// definition of which is the same `&f`, a store through `&T.s` computed as
// `statics + offset`, and an aggregate element whose lanes stp writes left
// behind after the whole element resolved to `arr[i, j] = value`.
public class ResidualStoreRecoveryTests
{
    // Panel { Frame frame @0x10 }; Frame { Point2 origin @0; Point2 size @8 };
    // Point2 { float x @0; float y @4 }.
    [Test]
    public void StoreThroughMergedFieldAddressResolves()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var point = InjectStruct(app, "Point2");
        InjectField("x", app.SystemTypes.SystemSingleType, point, 0);
        var y = InjectField("y", app.SystemTypes.SystemSingleType, point, 4);
        var frameType = InjectStruct(app, "Frame");
        var origin = InjectField("origin", point, frameType, 0);
        InjectField("size", point, frameType, 8);
        var panel = InjectClass(app, "Panel");
        var frame = InjectField("frame", frameType, panel, 0x10);

        var holder = Local("holder", panel);
        var pointer = Local("pointer");
        var source = Local("source", app.SystemTypes.SystemSingleType);
        var address = new AddressOf(new FieldReference(frame, holder, 0x10,
            [origin], 4));
        var store = new Instruction(3, OpCode.Move,
            new MemoryOperand(pointer, null, 4, 0, 4), source);
        var module = new ModuleDefinition("Stores.dll");
        Seed(module, app, point, frameType, panel);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemObjectType);
        var (caller, method) = ForeignCaller(app, module, [
            // `v = &f` re-taken on each path through the merge: every definition of
            // `pointer` is the same address-of, so it still names the one storage.
            new(0, OpCode.Move, pointer, address),
            new(1, OpCode.Move, pointer, new AddressOf(new FieldReference(frame, holder, 0x10,
                [origin], 4))),
            new(2, OpCode.CallVoid, new Immediate(0x1000)),
            store,
            new(4, OpCode.Return)], [holder, pointer, source]);

        MetadataResolver.ResolveFieldOffsets(caller);

        Assert.Multiple(() =>
        {
            Assert.That(store.Operands[0], Is.TypeOf<FieldReference>(),
                () => store.Operands[0]?.ToString() ?? "<null>");
            Assert.That(((FieldReference)store.Operands[0]).Field, Is.SameAs(y));
        });
    }

    // Holder { static int count @0; static P point @4 }.
    [Test]
    public void StoreThroughStaticFieldAddressResolves()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var holder = InjectClass(app, "Holder");
        var count = new InjectedFieldAnalysisContext("count", app.SystemTypes.SystemInt32Type,
            R.FieldAttributes.Public | R.FieldAttributes.Static, holder, 0);
        holder.Fields.Add(count);
        var module = new ModuleDefinition("Statics.dll");
        Seed(module, app, holder);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemIntPtrType);

        var statics = Local("statics",
            new StaticFieldStorageTypeAnalysisContext(holder, holder.DeclaringAssembly));
        var pointer = Local("pointer");
        var source = Local("source", app.SystemTypes.SystemInt32Type);
        var store = new Instruction(1, OpCode.Move,
            new MemoryOperand(pointer, null, 0, 0, 4), source);
        var (caller, method) = ForeignCaller(app, module, [
            // &Holder.count = statics + 0; [p] = count.
            new(0, OpCode.Add, pointer, statics, new Immediate(0)),
            store,
            new(2, OpCode.Return)], [statics, pointer, source]);

        ArrayRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        Assert.Multiple(() =>
        {
            Assert.That(store.Operands[0], Is.TypeOf<FieldReference>(),
                () => store.Operands[0]?.ToString() ?? "<null>");
            Assert.That(((FieldReference)store.Operands[0]).Field, Is.SameAs(count));
            Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Stsfld
                && i.Operand is IMemberDescriptor member && member.Name == "count"), Is.True,
                () => string.Join("\n", method.CilMethodBody!.Instructions));
        });
    }

    // A phi already claimed by the class type can never reach the classic
    // `[RuntimeClass + static_fields]` dereference - its `[phi + static_fields]`
    // load takes the stand-in instead.
    [Test]
    public void StaticsLoadThroughClassClaimedPhiResolves()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var holder = InjectClass(app, "Holder");
        var module = new ModuleDefinition("Statics.dll");
        Seed(module, app, holder);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType);

        var merged = Local("merged", holder);
        var input = Local("input");
        var loaded = Local("loaded");
        var load = new Instruction(2, OpCode.Move, loaded,
            new MemoryOperand(merged, null, 0xB8, 0, 8));
        var (caller, _) = ForeignCaller(app, module, [
            new(0, OpCode.Phi, merged, input),
            new(1, OpCode.Move, input, holder),
            load,
            new(3, OpCode.Return)], [merged, input, loaded]);

        MetadataResolver.ResolveFieldOffsets(caller);

        Assert.Multiple(() =>
        {
            Assert.That(load.Operands[1], Is.TypeOf<LocalVariable>(),
                () => load.Operands[1]?.ToString() ?? "<null>");
            Assert.That(((LocalVariable)load.Operands[1]).Type,
                Is.TypeOf<StaticFieldStorageTypeAnalysisContext>());
            Assert.That(
                ((StaticFieldStorageTypeAnalysisContext)((LocalVariable)load.Operands[1]).Type!)
                    .OwnerType, Is.SameAs(holder));
        });
    }

    // [klass + static_fields] is T's statics block and [klass] the type object
    // itself, resolved through copies of the class pointer.
    [Test]
    public void ClassPointerDereferencesResolveThroughCopy()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var holder = InjectClass(app, "Holder");
        var module = new ModuleDefinition("Statics.dll");
        Seed(module, app, holder);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType);

        var runtimeClass = new RuntimeClassTypeAnalysisContext(holder, holder.DeclaringAssembly);
        var copied = Local("copied", runtimeClass);
        var klass = Local("klass", runtimeClass);
        var statics = Local("statics");
        var loaded = Local("loaded");
        var type = Local("type");
        var staticsUse = new Instruction(2, OpCode.Add, statics,
            new MemoryOperand(klass, null, 0xB8, 0, 8), new Immediate(0));
        var loadStatics = new Instruction(3, OpCode.Move, loaded,
            new MemoryOperand(klass, null, 0xB8, 0, 8));
        var loadType = new Instruction(4, OpCode.Move, type,
            new MemoryOperand(klass, null, 0, 0, 8));
        var (caller, _) = ForeignCaller(app, module, [
            new(0, OpCode.Move, copied, holder),
            new(1, OpCode.Move, klass, copied),
            staticsUse,
            loadStatics,
            loadType,
            new(5, OpCode.CallVoid, new Immediate(0x1000), statics),
            new(6, OpCode.Return)], [copied, klass, statics, loaded, type]);

        MetadataResolver.ResolveFieldOffsets(caller);

        Assert.Multiple(() =>
        {
            Assert.That(staticsUse.Operands[1], Is.TypeOf<LocalVariable>(),
                () => staticsUse.Operands[1]?.ToString() ?? "<null>");
            Assert.That(((LocalVariable)staticsUse.Operands[1]).Type,
                Is.TypeOf<StaticFieldStorageTypeAnalysisContext>());
            Assert.That(
                ((StaticFieldStorageTypeAnalysisContext)((LocalVariable)staticsUse.Operands[1]).Type!)
                    .OwnerType, Is.SameAs(holder));
            // The load itself stays a dereference: typing its destination on the
            // classic schedule keeps a phi merging such loads honest about the join.
            Assert.That(loadStatics.Operands[1], Is.TypeOf<MemoryOperand>(),
                () => loadStatics.Operands[1]?.ToString() ?? "<null>");
            Assert.That(loadType.Operands[1], Is.SameAs((IOperand)holder),
                () => loadType.Operands[1]?.ToString() ?? "<null>");
        });
    }

    // stp writes a 16-byte aggregate element as two 8-byte lanes: `[p] = value`
    // names the whole element (its operand is the element type), and the upper
    // `[p + 8] = lane` writes bytes that call's implicit-definition register
    // already put in `value` - both resolve to grid[x, y] = value.
    [Test]
    public void AggregateElementStoreSplitAcrossLanes()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var aggregate = InjectStruct(app, "Agg4");
        foreach (var (name, at) in new[] { ("a", 0), ("b", 4), ("c", 8), ("d", 12) })
            InjectField(name, app.SystemTypes.SystemInt32Type, aggregate, at);
        var module = new ModuleDefinition("Grid.dll");
        Seed(module, app, aggregate);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemBooleanType, app.SystemTypes.SystemObjectType);

        var api = InjectClass(app, "Api");
        var make = api.InjectMethodContext("Make", aggregate,
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        var laneRegister = new Register(null, "X1");

        var grid = Local("grid", new ArrayTypeAnalysisContext(aggregate, 2));
        var bounds = Local("bounds");
        var x = Local("x", app.SystemTypes.SystemInt32Type);
        var y = Local("y", app.SystemTypes.SystemInt32Type);
        var cx = Local("cx", app.SystemTypes.SystemBooleanType);
        var cy = Local("cy", app.SystemTypes.SystemBooleanType);
        var product = Local("product");
        var flat = Local("flat");
        var scaled = Local("scaled");
        var pointer = Local("pointer");
        var value = Local("value", aggregate);
        var lane = new LocalVariable("lane", laneRegister);
        var upper = Local("upper", app.SystemTypes.SystemInt64Type);
        var call = new Instruction(7, OpCode.Call, make, value);
        call.ImplicitDefinitions.Add(laneRegister);
        var storeLow = new Instruction(9, OpCode.Move,
            new MemoryOperand(pointer, null, 0x20, 0, 8), value);
        var storeHigh = new Instruction(10, OpCode.Move,
            new MemoryOperand(pointer, null, 0x28, 0, 8), upper);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, bounds, new MemoryOperand(grid, null, 0x10, 0, 8)),
            new(1, OpCode.CheckLess, cx, x, new MemoryOperand(bounds, null, 0, 0, 4)),
            new(2, OpCode.CheckLess, cy, y, new MemoryOperand(bounds, null, 0x10, 0, 4)),
            new(3, OpCode.Multiply, product, new MemoryOperand(bounds, null, 0x10, 0, 4), x),
            new(4, OpCode.Add, flat, y, product),
            new(5, OpCode.ShiftLeft, scaled, flat, new Immediate(4)),
            new(6, OpCode.Add, pointer, grid, scaled),
            call,
            new(8, OpCode.Move, upper, lane),
            storeLow,
            storeHigh,
            new(11, OpCode.Return)],
            [grid, bounds, x, y, cx, cy, product, flat, scaled, pointer, value, lane, upper]);

        ArrayRecovery.Run(caller);

        Assert.Multiple(() =>
        {
            Assert.That(storeLow.OpCode, Is.EqualTo(OpCode.CallVoid),
                () => storeLow.ToString());
            Assert.That(storeLow.Operands[0], Is.InstanceOf<MethodAnalysisContext>()
                .And.Property("Name").EqualTo("Set"), () => storeLow.ToString());
            Assert.That(storeLow.Operands.Skip(1).Take(4).ToArray(),
                Is.EqualTo(new IOperand[] { grid, x, y, value }));
            Assert.That(storeHigh, Has.Property("OpCode").EqualTo(OpCode.Nop),
                () => storeHigh.ToString());
        });
    }
}
