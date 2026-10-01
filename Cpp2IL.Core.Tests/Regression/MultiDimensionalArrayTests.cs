using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.NestedFieldPathLoadTests;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery mechanism (castle-recovery#218): a T[,] keeps its lengths in a bounds block at
// [array + 0x10], one 16-byte {length, lower bound} pair per dimension, and its elements
// row-major at array + 0x20 + (i·len1 + j)·size. il2cpp checks each index against its
// length before the access.
public class MultiDimensionalArrayTests
{
    private sealed record Grid(MethodAnalysisContext Caller, MethodDefinition Method, ModuleDefinition Module,
        LocalVariable Array, LocalVariable X, LocalVariable Y, Instruction Access);

    //   b = [grid + 0x10]; x < [b]; y < [b + 0x10]            (the bounds checks)
    //   p = grid + ((y + [b + 0x10]·x) << shift); access at [p + 0x20 + offset]
    private static Grid Build(TypeAnalysisContext elementType, int shift, System.Func<MemoryOperand, LocalVariable, Instruction> access,
        bool checkY = true, params TypeAnalysisContext[] seeded)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("Grid.dll");
        Seed(module, app, seeded);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemBooleanType,
            app.SystemTypes.SystemObjectType);

        var grid = Local("grid", new ArrayTypeAnalysisContext(elementType, 2));
        var bounds = Local("bounds");
        var x = Local("x", app.SystemTypes.SystemInt32Type);
        var y = Local("y", app.SystemTypes.SystemInt32Type);
        var cx = Local("cx", app.SystemTypes.SystemBooleanType);
        var cy = Local("cy", app.SystemTypes.SystemBooleanType);
        var product = Local("product");
        var flat = Local("flat");
        var scaled = Local("scaled");
        var pointer = Local("pointer");
        var value = Local("value", elementType);
        var accessInstruction = access(new MemoryOperand(pointer, null, 0x20, 0, 4), value);
        List<Instruction> instructions =
        [
            new(0, OpCode.Move, bounds, new MemoryOperand(grid, null, 0x10, 0, 8)),
            new(1, OpCode.CheckLess, cx, x, new MemoryOperand(bounds, null, 0, 0, 4)),
        ];
        if (checkY)
            instructions.Add(new(2, OpCode.CheckLess, cy, y, new MemoryOperand(bounds, null, 0x10, 0, 4)));
        instructions.AddRange([
            new(3, OpCode.Multiply, product, new MemoryOperand(bounds, null, 0x10, 0, 4), x),
            new(4, OpCode.Add, flat, y, product),
            new(5, OpCode.ShiftLeft, scaled, flat, new Immediate(shift)),
            new(6, OpCode.Add, pointer, grid, scaled),
            accessInstruction,
            new(8, OpCode.Return, value),
        ]);
        var (caller, method) = ForeignCaller(app, module, instructions,
            [grid, bounds, x, y, cx, cy, product, flat, scaled, pointer, value]);
        caller.ParameterLocals = [grid, x, y];
        return new Grid(caller, method, module, grid, x, y, accessInstruction);
    }

    private static List<Instruction> Instructions(MethodAnalysisContext caller)
        => caller.ControlFlowGraph!.Blocks.SelectMany(b => b.Instructions).ToList();

    private static Instruction Accessor(MethodAnalysisContext caller, string name)
        => Instructions(caller).Single(i => i.Operands.FirstOrDefault() is MethodAnalysisContext { Name: var n } && n == name);

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [Test]
    public void ElementReadIsGetOfBothIndices()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var grid = Build(app.SystemTypes.SystemInt32Type, 2, (memory, value) => new Instruction(7, OpCode.Move, value, memory));

        ArrayRecovery.RecoverMultiDimensionalAccesses(grid.Caller);

        var get = Accessor(grid.Caller, "Get");
        Assert.Multiple(() =>
        {
            Assert.That(get.Operands.Skip(2), Is.EqualTo(new IOperand[] { grid.Array, grid.X, grid.Y }));
            Assert.That(Instructions(grid.Caller).Count(i => i.Operands.FirstOrDefault() is MethodAnalysisContext { Name: "GetLength" }),
                Is.EqualTo(2), "the two bounds checks read GetLength(0) and GetLength(1)");
            Assert.That(Instructions(grid.Caller).Any(i => i.Operands.Any(o => o is MemoryOperand)), Is.False,
                () => string.Join("\n", Instructions(grid.Caller)));
        });
    }

    [Test]
    public void ElementStoreIsSet()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var grid = Build(app.SystemTypes.SystemInt32Type, 2, (memory, value) => new Instruction(7, OpCode.Move, memory, value));

        ArrayRecovery.RecoverMultiDimensionalAccesses(grid.Caller);

        Assert.That(grid.Access.OpCode, Is.EqualTo(OpCode.CallVoid));
        Assert.That(grid.Access.Operands[0], Is.InstanceOf<MethodAnalysisContext>().With.Property("Name").EqualTo("Set"));
        Assert.That(grid.Access.Operands.Skip(1).Take(3), Is.EqualTo(new IOperand[] { grid.Array, grid.X, grid.Y }));
    }

    [Test]
    public void StructElementFieldIsReadThroughAddress()
    {
        // Cell { int a @0; int b @4 }: [p + 0x24] is grid[x, y].b.
        var app = Cpp2IlApi.CurrentAppContext!;
        var cell = InjectStruct(app, "Cell");
        InjectField("a", app.SystemTypes.SystemInt32Type, cell, 0);
        InjectField("b", app.SystemTypes.SystemInt32Type, cell, 4);
        var read = Local("read", app.SystemTypes.SystemInt32Type);
        var grid = Build(cell, 3, (memory, _) => new Instruction(7, OpCode.Move, read,
            new MemoryOperand(memory.Base, null, 0x24, 0, 4)), seeded: cell);

        ArrayRecovery.RecoverMultiDimensionalAccesses(grid.Caller);

        Assert.Multiple(() =>
        {
            Assert.That(Accessor(grid.Caller, "Address").Operands.Skip(2), Is.EqualTo(new IOperand[] { grid.Array, grid.X, grid.Y }));
            Assert.That((grid.Access.Operands[1] as FieldReference)?.Field.Name, Is.EqualTo("b"));
        });
    }

    [Test]
    public void IndexNeverComparedWithItsLengthKeepsTheLoad()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var grid = Build(app.SystemTypes.SystemInt32Type, 2, (memory, value) => new Instruction(7, OpCode.Move, value, memory),
            checkY: false);

        ArrayRecovery.RecoverMultiDimensionalAccesses(grid.Caller);

        Assert.That(grid.Access.Operands[1], Is.InstanceOf<MemoryOperand>());
    }

    [Test]
    public void EmitsTheArrayAccessorAndGetLength()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var grid = Build(app.SystemTypes.SystemInt32Type, 2, (memory, value) => new Instruction(7, OpCode.Move, value, memory));

        // System.Array::GetLength needs its AsmResolver definition, like any corlib member.
        var arrayType = app.SystemTypes.SystemArrayType!;
        SeedCorLibTypes(app, grid.Module, arrayType);
        var getLength = arrayType.Methods.Single(m => m.Name == "GetLength" && m.Parameters.Count == 1);
        var definition = new MethodDefinition("GetLength", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public,
            AsmResolver.DotNet.Signatures.MethodSignature.CreateInstance(grid.Module.CorLibTypeFactory.Int32,
                [grid.Module.CorLibTypeFactory.Int32]));
        arrayType.GetExtraData<TypeDefinition>("AsmResolverType")!.Methods.Add(definition);
        getLength.PutExtraData("AsmResolverMethod", definition);

        ArrayRecovery.RecoverMultiDimensionalAccesses(grid.Caller);
        IlGenerator.GenerateIl(grid.Caller, grid.Method);

        var calls = grid.Method.CilMethodBody!.Instructions
            .Where(i => i.OpCode == CilOpCodes.Call || i.OpCode == CilOpCodes.Callvirt)
            .Select(i => i.Operand as IMethodDescriptor).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(calls.Any(m => m?.Name == "Get" && m.DeclaringType?.FullName == "System.Int32[0..., 0...]"), Is.True,
                () => Dump(grid.Method));
            Assert.That(calls.Count(m => m?.Name == "GetLength"), Is.EqualTo(2), () => Dump(grid.Method));
        });
    }

    // for (i…) { p = &grid[i, 0]; for (…) { sum += *p; p++; } }, with the row start scaled by
    // a counter s that steps by the element size alongside i (il2cpp's strength reduction).
    private (MethodAnalysisContext Caller, Instruction Load, LocalVariable Grid, LocalVariable Row) RowWalk(bool rowChangesInside)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("Grid.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemBooleanType,
            app.SystemTypes.SystemObjectType);
        var int32 = app.SystemTypes.SystemInt32Type;
        var grid = Local("grid", new ArrayTypeAnalysisContext(int32, 2));
        LocalVariable data = Local("data"), i = Local("i", int32), s = Local("s"), sum = Local("sum", int32),
            b = Local("bounds"), ci = Local("ci", app.SystemTypes.SystemBooleanType), m = Local("m"), p = Local("p"),
            x = Local("x", int32), cj = Local("cj", app.SystemTypes.SystemBooleanType),
            ck = Local("ck", app.SystemTypes.SystemBooleanType), n = Local("n", int32);
        var outer = new Instruction(4, OpCode.Move, b, new MemoryOperand(grid, null, 0x10, 0, 8));
        var load = new Instruction(8, OpCode.Move, x, new MemoryOperand(p, null, 0, 0, 4));
        List<Instruction> instructions =
        [
            new(0, OpCode.Add, data, grid, new Immediate(0x20)),
            new(1, OpCode.Move, i, new Immediate(0)),
            new(2, OpCode.Move, s, new Immediate(0)),
            new(3, OpCode.Move, sum, new Immediate(0)),
            outer,
            new(5, OpCode.CheckLess, ci, i, new MemoryOperand(b, null, 0, 0, 4)),
            new(6, OpCode.Multiply, m, new MemoryOperand(b, null, 0x10, 0, 4), s),
            new(7, OpCode.Add, p, data, m),
            load,
            new(9, OpCode.Add, p, p, new Immediate(4)),
            new(10, OpCode.Add, sum, sum, x),
        ];
        if (rowChangesInside)
            instructions.Add(new(11, OpCode.Add, i, i, new Immediate(1)));
        instructions.AddRange([
            new(12, OpCode.CheckLess, cj, sum, n),
            new(13, OpCode.ConditionalJump, load, cj),
        ]);
        if (!rowChangesInside)
            instructions.Add(new(14, OpCode.Add, i, i, new Immediate(1)));
        instructions.AddRange([
            new(15, OpCode.Add, s, s, new Immediate(4)),
            new(16, OpCode.CheckLess, ck, i, n),
            new(17, OpCode.ConditionalJump, outer, ck),
            new(18, OpCode.Return, sum),
        ]);
        var (caller, _) = ForeignCaller(app, module, instructions, [grid, data, i, s, sum, b, ci, m, p, x, cj, ck, n]);
        caller.ParameterLocals = [grid, n];
        return (caller, load, grid, i);
    }

    [Test]
    public void RowWalkIsTheElementAtRowAndAColumnCounter()
    {
        var (caller, load, grid, row) = RowWalk(rowChangesInside: false);

        ArrayRecovery.RecoverMultiDimensionalAccesses(caller);

        Assert.That(load.OpCode, Is.EqualTo(OpCode.Call), () => string.Join("\n", Instructions(caller)));
        Assert.That(load.Operands[0], Is.InstanceOf<MethodAnalysisContext>().With.Property("Name").EqualTo("Get"));
        Assert.That(load.Operands[2], Is.SameAs(grid));
        Assert.That(load.Operands[3], Is.SameAs(row));
        var column = (LocalVariable)load.Operands[4];
        var writes = Instructions(caller).Where(i => ReferenceEquals(i.Destination, column)).ToList();
        Assert.That(writes.Count, Is.EqualTo(2), () => string.Join("\n", Instructions(caller)));
    }

    [Test]
    public void RowWalkWhoseRowChangesInsideKeepsTheLoad()
    {
        var (caller, load, _, _) = RowWalk(rowChangesInside: true);

        ArrayRecovery.RecoverMultiDimensionalAccesses(caller);

        Assert.That(load.Operands[1], Is.InstanceOf<MemoryOperand>());
    }

    [Test]
    public void OffsetWalkIsTheElementAtItsCounter()
    {
        // for (k = 2; k < len1; k++) x = grid[0, k], strength-reduced to `grid + off + 0x28`
        // with off stepping by 4 from 0.
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("Grid.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemBooleanType,
            app.SystemTypes.SystemObjectType);
        var int32 = app.SystemTypes.SystemInt32Type;
        var grid = Local("grid", new ArrayTypeAnalysisContext(int32, 2));
        LocalVariable off = Local("off"), k = Local("k", int32), b = Local("bounds"),
            ck = Local("ck", app.SystemTypes.SystemBooleanType), p = Local("p"), x = Local("x", int32);
        var head = new Instruction(3, OpCode.CheckLess, ck, k, new MemoryOperand(b, null, 0x10, 0, 4));
        var load = new Instruction(5, OpCode.Move, x, new MemoryOperand(p, null, 0x28, 0, 4));
        var (caller, _) = ForeignCaller(app, module, [
            new(0, OpCode.Move, off, new Immediate(0)),
            new(1, OpCode.Move, k, new Immediate(2)),
            new(2, OpCode.Move, b, new MemoryOperand(grid, null, 0x10, 0, 8)),
            head,
            new(4, OpCode.Add, p, grid, off),
            load,
            new(6, OpCode.Add, off, off, new Immediate(4)),
            new(7, OpCode.Add, k, k, new Immediate(1)),
            new(8, OpCode.ConditionalJump, head, ck),
            new(9, OpCode.Return, x)], [grid, off, k, b, ck, p, x]);
        caller.ParameterLocals = [grid];

        ArrayRecovery.RecoverMultiDimensionalAccesses(caller);

        Assert.That(load.OpCode, Is.EqualTo(OpCode.Call), () => string.Join("\n", Instructions(caller)));
        Assert.That(load.Operands.Skip(2), Is.EqualTo(new IOperand[] { grid, new Immediate(0), k }));
    }

    [Test]
    public void AllocationOfARankTwoArrayEmitsItsConstructor()
    {
        // new int[w, h]: the array type's own .ctor(int, int).
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("Grid.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        var gridType = new ArrayTypeAnalysisContext(app.SystemTypes.SystemInt32Type, 2);
        var grid = Local("grid", gridType);
        var w = Local("w", app.SystemTypes.SystemInt32Type);
        var h = Local("h", app.SystemTypes.SystemInt32Type);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.NewArr, grid, gridType, w, h),
            new(1, OpCode.Return)], [grid, w, h]);
        caller.ParameterLocals = [w, h];

        IlGenerator.GenerateIl(caller, method);

        var constructor = method.CilMethodBody!.Instructions.Single(i => i.OpCode == CilOpCodes.Newobj).Operand as IMethodDescriptor;
        Assert.That(constructor?.Name?.ToString(), Is.EqualTo(".ctor"), () => Dump(method));
        Assert.That(constructor!.DeclaringType?.FullName, Is.EqualTo("System.Int32[0..., 0...]"));
        Assert.That(constructor.Signature!.ParameterTypes, Has.Count.EqualTo(2));
    }

    [Test]
    public void StubPassingNoLowerBoundsToTheExportedNewFullIsProven()
    {
        // il2cpp_array_new_full @0x1000: b 0x2000. Stub @0x3000: mov x2, xzr; b 0x2000.
        var words = new Dictionary<ulong, uint> { [0x1000] = 0x14000400, [0x3000] = 0xaa1f03e2, [0x3004] = 0x17fffbff };
        uint? Read(ulong at) => words.TryGetValue(at, out var word) ? word : null;

        Assert.That(ArrayRecovery.ProvesArrayNewWithoutBounds(0x1000, 0x3000, Read), Is.True);
        words[0x3004] = 0x17fffc00; // b 0x2004: somewhere else
        Assert.That(ArrayRecovery.ProvesArrayNewWithoutBounds(0x1000, 0x3000, Read), Is.False);
    }
}
