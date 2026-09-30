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
}
