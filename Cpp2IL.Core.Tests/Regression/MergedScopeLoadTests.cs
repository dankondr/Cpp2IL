using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using AsmResolver.DotNet;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.NestedFieldPathLoadTests;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster (castle-recovery#354): scope loads that stayed `Unmanaged
// memory load` because a merge, an address fold, or an untyped register hid
// the managed value they carry - a reloaded bounds block, an element address
// summed into one pointer, a shared-generic newarr whose type lives in a
// class local, and a statics base proven only by a phi of class constants.
public class MergedScopeLoadTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    // The jit may reload `[grid + bounds]` on each edge of a merge, leaving the
    // bounds pointer with several definitions that read the same word through
    // different copies of `this.grid`. The block still names one array, so its
    // lengths are GetLength calls - spelled by the local that holds the grid,
    // the same operand the bounds-check prover matches the access against.
    [Test]
    public void MergedBoundsReloadsStillNameTheirLengths()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("Bounds.dll");
        var int32 = app.SystemTypes.SystemInt32Type;
        SeedCorLibTypes(app, module, int32);

        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, TypeAttributes.Public);
        var grid = new InjectedFieldAnalysisContext("grid", new ArrayTypeAnalysisContext(int32, 2),
            FieldAttributes.Public, owner, 0x10);
        owner.Fields.Add(grid);
        var self = Local("self", owner);
        var first = Local("first");
        var second = Local("second");
        var bounds = Local("bounds");
        var length0 = Local("length0", int32);
        var length1 = Local("length1", int32);
        var lengthRead = new Instruction(4, OpCode.Move, length0, new MemoryOperand(bounds));
        var widthRead = new Instruction(5, OpCode.Move, length1,
            new MemoryOperand(bounds, null, 0x10, 0, 4));
        var (caller, _) = ForeignCaller(app, module, [
            new(0, OpCode.Move, first, new FieldReference(grid, self, 0x10)),
            new(1, OpCode.Move, second, new FieldReference(grid, self, 0x10)),
            new(2, OpCode.Move, bounds, new MemoryOperand(first, null, 0x10, 0, 8)),
            new(3, OpCode.Move, bounds, new MemoryOperand(second, null, 0x10, 0, 8)),
            lengthRead,
            widthRead,
            new(6, OpCode.Return, length0, length1)],
            [self, first, second, bounds, length0, length1]);

        ArrayRecovery.RecoverMultiDimensionalAccesses(caller);

        var getLengths = caller.ControlFlowGraph!.Instructions
            .Where(i => i.OpCode == OpCode.Call
                        && i.Operands[0] is MethodAnalysisContext { Name: "GetLength" })
            .ToList();
        Assert.Multiple(() =>
        {
            Assert.That(getLengths, Has.Count.EqualTo(2));
            Assert.That(getLengths.Select(i => ((Immediate)i.Operands[3]).Value),
                Is.EqualTo(new long[] { 0, 1 }));
            Assert.That(getLengths.All(i => i.Operands[2] is LocalVariable
                && (ReferenceEquals(i.Operands[2], first) || ReferenceEquals(i.Operands[2], second))),
                Is.True);
            Assert.That(lengthRead.Operands[1], Is.Not.InstanceOf<MemoryOperand>());
            Assert.That(widthRead.Operands[1], Is.Not.InstanceOf<MemoryOperand>());
        });
    }

    // `arr[i]` with the whole address folded into one pointer: the jit keeps
    // `p = arr + (idx << shift) + header` and dereferences `[p]` - no
    // `[base + index * scale]` operand exists for the element matchers. The
    // same unsigned guard still proves the index, and the comparison may run
    // on a copy of the sign-extended register.
    [Test]
    public void FoldedElementAddressReadsAsAnIndex()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("Folded.dll");
        var int32 = app.SystemTypes.SystemInt32Type;
        var array = Local("array", new SzArrayTypeAnalysisContext(int32));
        var index = Local("index", int32);
        var compared = Local("compared", int32);
        var extended = Local("extended");
        var scaled = Local("scaled");
        var partial = Local("partial");
        var pointer = Local("pointer");
        var flag = new LocalVariable("flag", new Register(null, "C"));
        var value = Local("value", int32);
        var load = new Instruction(8, OpCode.Move, value, new MemoryOperand(pointer));
        var (caller, _) = ForeignCaller(app, module, [
            new(0, OpCode.SignExtend32, extended, index),
            new(1, OpCode.Move, compared, extended),
            new(2, OpCode.ShiftLeft, scaled, extended, new Immediate(2)),
            new(3, OpCode.Add, partial, array, scaled),
            new(4, OpCode.Add, pointer, partial, new Immediate(0x20)),
            new(5, OpCode.CheckLess, flag, compared, new ArrayLength(array)),
            new(6, OpCode.ConditionalJump, load, flag),
            new(7, OpCode.Return),
            load,
            new(9, OpCode.CallVoid, new StringLiteral("consume"), value),
            new(10, OpCode.Return)],
            [array, index, compared, extended, scaled, partial, pointer, flag, value]);
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph!);

        ArrayRecovery.Run(caller);

        Assert.Multiple(() =>
        {
            Assert.That(load.Operands[1], Is.TypeOf<ArrayAccess>());
            var access = (ArrayAccess)load.Operands[1];
            Assert.That(access.Array, Is.SameAs(array));
            Assert.That(access.Index, Is.SameAs(index));
        });
    }

    // A shared-generic `new T[n]` keeps its element type in a register: the
    // operand of `SzArrayNew` is the local holding `Il2CppClass<T[]>`, not a
    // folded `Type:` constant. The class a local holds still names the array
    // type, through a `Move` of the class constant or a RuntimeClass-typed
    // copy.
    [Test]
    public void SharedGenericNewarrReadsItsTypeFromTheClassLocal()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("Newarr.dll");
        var int32 = app.SystemTypes.SystemInt32Type;
        var arrayType = new SzArrayTypeAnalysisContext(app.SystemTypes.SystemStringType);
        var klass = Local("klass");
        var copy = Local("copy");
        var result = Local("result");
        var length = Local("length", int32);
        var allocate = new Instruction(2, OpCode.Call,
            new StringLiteral("SzArrayNew"), result, copy, length);
        var (caller, _) = ForeignCaller(app, module, [
            new(0, OpCode.Move, klass,
                new RuntimeClassTypeAnalysisContext(arrayType, arrayType.DeclaringAssembly)),
            new(1, OpCode.Move, copy, klass),
            allocate,
            new(3, OpCode.Return, result)],
            [klass, copy, result, length]);

        ArrayRecovery.Run(caller);

        Assert.Multiple(() =>
        {
            Assert.That(allocate.OpCode, Is.EqualTo(OpCode.NewArr));
            Assert.That(result.Type, Is.SameAs(arrayType));
        });
    }

    // A copy of a class constant created after the seeding fixpoint settled (an
    // edge copy, a split phi input) still holds the same Il2CppClass pointer but
    // keeps a null type - `PropagateStaticFieldStorage` can never reach the
    // dereference it feeds. The class constant is proof enough to claim
    // `RuntimeClass` itself, and the dereference then types its destination on
    // the classic schedule.
    [Test]
    public void UnprovenClassConstantStaticsBaseClaimsRuntimeClass()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("Statics.dll");
        var leaf = Local("leaf");
        var copy = Local("copy");
        var value = Local("value");
        var read = new Instruction(2, OpCode.Move, value,
            new MemoryOperand(copy, null, 0xB8, 0, 8));
        var (caller, _) = ForeignCaller(app, module, [
            new(0, OpCode.Move, leaf, app.SystemTypes.SystemStringType),
            new(1, OpCode.Move, copy, leaf),
            read,
            new(3, OpCode.Return)],
            [leaf, copy, value]);

        // `ResolveFieldOffsets` alone sees the copy before any seeding pass:
        // `copy` has no type but its def chain proves the class constant.
        MetadataResolver.ResolveFieldOffsets(caller);

        Assert.That(copy.Type, Is.InstanceOf<RuntimeClassTypeAnalysisContext>());

        // With the base claimed, the classic propagation types the statics
        // dereference's destination.
        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(value.Type, Is.InstanceOf<StaticFieldStorageTypeAnalysisContext>());
            Assert.That(((StaticFieldStorageTypeAnalysisContext)value.Type!).OwnerType,
                Is.SameAs(app.SystemTypes.SystemStringType));
        });
    }
}
