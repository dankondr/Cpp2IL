using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.NestedFieldPathLoadTests;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery mechanism (castle-recovery#285, catalog il2cpp-null-check / il2cpp-bounds-check):
// IL2CPP null-checks every dereference and bounds-checks every array element (per dimension
// in a T[,]) by calling a non-returning raise helper, lifted as a bare Throw of its exception
// type. A branch to it that guards exactly the access il2cpp guards is that access's implicit
// check; anything else stays.
public class Il2CppCheckRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;

    private static MethodAnalysisContext Method(List<Instruction> instructions, params LocalVariable[] locals)
        => ForeignCaller(App, new ModuleDefinition("Checks.dll"), instructions, [.. locals]).caller;

    private static List<Instruction> All(MethodAnalysisContext method)
        => method.ControlFlowGraph!.Blocks.SelectMany(b => b.Instructions).Where(i => i.OpCode != OpCode.Nop).ToList();

    private static string Dump(MethodAnalysisContext method) => string.Join("\n", All(method));

    // A helper raise whose result the lifter still saw read: what LowerThrowHelperCall leaves.
    private static Instruction Raise(int index, string exception)
        => new(index, OpCode.Throw, App.SystemTypes.SystemObjectType.DeclaringAssembly!.GetTypeByFullName(exception)!)
            { ThrowFromNonReturningCall = true };

    // if (x == null) raise NRE; return [deref + 0x10];
    private static MethodAnalysisContext NullGuard(LocalVariable checkedReference, LocalVariable dereferenced, Instruction raise)
    {
        var flag = Local("flag", App.SystemTypes.SystemBooleanType);
        var value = Local("value", App.SystemTypes.SystemInt32Type);
        return Method([
            new(0, OpCode.CheckEqual, flag, checkedReference, new Immediate(0)),
            new(1, OpCode.ConditionalJump, raise, flag),
            new(2, OpCode.Move, value, new MemoryOperand(dereferenced, null, 0x10, 0, 4)),
            new(3, OpCode.Return, value),
            raise,
            new(5, OpCode.Return, value),
        ], checkedReference, dereferenced, flag, value);
    }

    [Test]
    public void NullCheckGuardingTheDereferenceIsRemoved()
    {
        var node = Local("node", App.SystemTypes.SystemObjectType);
        var method = NullGuard(node, node, Raise(4, "System.NullReferenceException"));

        Il2CppCheckRecovery.Run(method);

        Assert.That(All(method).Any(i => i.OpCode is OpCode.ConditionalJump or OpCode.Throw), Is.False, () => Dump(method));
    }

    [Test]
    public void NullCheckOfAnotherReferenceIsKept()
    {
        var method = NullGuard(Local("node", App.SystemTypes.SystemObjectType), Local("other", App.SystemTypes.SystemObjectType),
            Raise(4, "System.NullReferenceException"));

        Il2CppCheckRecovery.Run(method);

        Assert.That(All(method).Count(i => i.OpCode is OpCode.ConditionalJump or OpCode.Throw), Is.EqualTo(2), () => Dump(method));
    }

    // `throw new NullReferenceException()` raises the object it built, not the helper's type.
    [Test]
    public void ThrowOfAConstructedExceptionIsKept()
    {
        var node = Local("node", App.SystemTypes.SystemObjectType);
        var method = NullGuard(node, node, new Instruction(4, OpCode.Throw, Local("constructed", App.SystemTypes.SystemObjectType)));

        Il2CppCheckRecovery.Run(method);

        Assert.That(All(method).Count(i => i.OpCode is OpCode.ConditionalJump or OpCode.Throw), Is.EqualTo(2), () => Dump(method));
    }

    // NativeExceptionRegionProof knows a raise call never returns only from the Throw left in the
    // graph: a removed raise that natively falls into a call inside a protected range would merge
    // its frame into that call site's.
    [TestCase(true, 4)]
    [TestCase(false, 2)]
    public void RaiseFallingIntoAProtectedCallKeepsItsCheck(bool protectedNext, int kept)
    {
        var node = Local("node", App.SystemTypes.SystemObjectType);
        var other = Local("other", App.SystemTypes.SystemObjectType);
        LocalVariable first = Local("first", App.SystemTypes.SystemBooleanType), second = Local("second", App.SystemTypes.SystemBooleanType),
            value = Local("value", App.SystemTypes.SystemInt32Type);
        var raised = Raise(6, "System.NullReferenceException");
        raised.NativeAddress = 0x100;
        var live = Raise(7, "System.NullReferenceException");
        live.NativeAddress = 0x104;
        var method = Method([
            new(0, OpCode.CheckEqual, first, node, new Immediate(0)),
            new(1, OpCode.ConditionalJump, raised, first),
            new(2, OpCode.Move, value, new MemoryOperand(node, null, 0x10, 0, 4)),
            new(3, OpCode.CheckEqual, second, other, new Immediate(0)),
            new(4, OpCode.ConditionalJump, live, second),
            new(5, OpCode.Return, value),
            raised,
            live,
        ], node, other, first, second, value);
        // The second raise sits inside a try (or, without one, only another range is protected).
        method.UnwindInfo = new LibCpp2IL.EhFunctionInfo { Start = 0, Size = 0x300 };
        method.UnwindInfo.CallSites.Add(new LibCpp2IL.EhCallSiteInfo(protectedNext ? 0x104UL : 0x2F0UL, 4, 0x200, 0));
        method.ExceptionRegionInstructions = [raised, live];

        Il2CppCheckRecovery.Run(method);

        Assert.That(All(method).Count(i => i.OpCode is OpCode.ConditionalJump or OpCode.Throw), Is.EqualTo(kept), () => Dump(method));
    }

    // cmp len, i; b.ls raise  ==  `!(!(len < i)) || (len - i) == 0`, then a[read].
    private static MethodAnalysisContext Bounds(bool sameIndex)
    {
        var int32 = App.SystemTypes.SystemInt32Type;
        var boolean = App.SystemTypes.SystemBooleanType;
        var array = Local("array", new SzArrayTypeAnalysisContext(int32));
        LocalVariable index = Local("i", int32), other = Local("j", int32), length = Local("length", int32),
            less = Local("less", boolean), carry = Local("carry", boolean), difference = Local("difference", int32),
            zero = Local("zero", boolean), notCarry = Local("notCarry", boolean), lowerOrSame = Local("ls", boolean),
            value = Local("value", int32);
        var raise = Raise(9, "System.IndexOutOfRangeException");
        return Method([
            new(0, OpCode.Move, length, new ArrayLength(array)),
            new(1, OpCode.CheckLess, less, length, index),
            new(2, OpCode.Not, carry, less),
            new(3, OpCode.Subtract, difference, length, index),
            new(4, OpCode.CheckEqual, zero, difference, new Immediate(0)),
            new(5, OpCode.Not, notCarry, carry),
            new(6, OpCode.Or, lowerOrSame, notCarry, zero),
            new(7, OpCode.ConditionalJump, raise, lowerOrSame),
            new(8, OpCode.Move, value, new ArrayAccess(array, sameIndex ? index : other)),
            new(10, OpCode.Return, value),
            raise,
        ], array, index, other, length, less, carry, difference, zero, notCarry, lowerOrSame, value);
    }

    [TestCase(true, 0)]
    [TestCase(false, 2)]
    public void BoundsCheckIsRemovedOnlyForTheIndexItCompares(bool sameIndex, int kept)
    {
        var method = Bounds(sameIndex);

        Il2CppCheckRecovery.Run(method);

        Assert.That(All(method).Count(i => i.OpCode is OpCode.ConditionalJump or OpCode.Throw), Is.EqualTo(kept), () => Dump(method));
    }

    // grid[i, j] after ArrayRecovery: a null check, then per dimension `GetLength(d) <= index`
    // (unsigned) raising, then Get. Each check is removed from the access outwards.
    [Test]
    public void GridChecksPeelFromTheAccessOutwards()
    {
        var int32 = App.SystemTypes.SystemInt32Type;
        var boolean = App.SystemTypes.SystemBooleanType;
        var gridType = new ArrayTypeAnalysisContext(int32, 2);
        var get = new InjectedMethodAnalysisContext(gridType, "Get", int32, R.MethodAttributes.Public, [int32, int32]);
        var getLength = App.SystemTypes.SystemArrayType!.Methods.Single(m => m.Name == "GetLength" && m.Parameters.Count == 1);
        var grid = Local("grid", gridType);
        LocalVariable i = Local("i", int32), j = Local("j", int32), isNull = Local("isNull", boolean),
            value = Local("value", int32);
        var nullRaise = Raise(30, "System.NullReferenceException");
        var indexRaise = Raise(31, "System.IndexOutOfRangeException");
        List<Instruction> instructions =
        [
            new(0, OpCode.CheckEqual, isNull, grid, new Immediate(0)),
            new(1, OpCode.ConditionalJump, nullRaise, isNull),
        ];
        var locals = new List<LocalVariable> { grid, i, j, isNull, value };
        foreach (var (dimension, index) in new[] { (0, i), (1, j) })
        {
            LocalVariable first = Local($"len{dimension}a", int32), second = Local($"len{dimension}b", int32),
                less = Local($"less{dimension}", boolean), carry = Local($"carry{dimension}", boolean),
                difference = Local($"difference{dimension}", int32), zero = Local($"zero{dimension}", boolean),
                notCarry = Local($"notCarry{dimension}", boolean), lowerOrSame = Local($"ls{dimension}", boolean);
            var at = 2 + dimension * 10;
            instructions.AddRange([
                new(at, OpCode.Call, getLength, first, grid, new Immediate(dimension)),
                new(at + 1, OpCode.CheckLess, less, first, index),
                new(at + 2, OpCode.Not, carry, less),
                new(at + 3, OpCode.Call, getLength, second, grid, new Immediate(dimension)),
                new(at + 4, OpCode.Subtract, difference, second, index),
                new(at + 5, OpCode.CheckEqual, zero, difference, new Immediate(0)),
                new(at + 6, OpCode.Not, notCarry, carry),
                new(at + 7, OpCode.Or, lowerOrSame, notCarry, zero),
                new(at + 8, OpCode.ConditionalJump, indexRaise, lowerOrSame),
            ]);
            locals.AddRange([first, second, less, carry, difference, zero, notCarry, lowerOrSame]);
        }
        var access = new Instruction(25, OpCode.Call, get, value, grid, i, j);
        instructions.AddRange([access, new(26, OpCode.Return, value), indexRaise, nullRaise]);
        var method = Method(instructions, [.. locals]);

        Il2CppCheckRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(All(method).Select(x => x.OpCode), Is.EqualTo(new[] { OpCode.Call, OpCode.Return }), () => Dump(method));
            Assert.That(Il2CppCheckRecovery.ReceiverWasNullChecked(method, access), Is.False,
                "an array accessor stays a call, as C# emits it");
        });
    }

    // NullCheck(s); s.Trim(): the source called it with callvirt, which il2cpp turned into the check.
    [Test]
    public void NullCheckedDirectCallIsMarkedForCallvirt()
    {
        var text = Local("text", App.SystemTypes.SystemStringType);
        var trimmed = Local("trimmed", App.SystemTypes.SystemStringType);
        var flag = Local("flag", App.SystemTypes.SystemBooleanType);
        var trim = App.SystemTypes.SystemStringType.Methods.First(m => m.Name == "Trim" && !m.IsStatic && m.Parameters.Count == 0);
        var raise = Raise(3, "System.NullReferenceException");
        var call = new Instruction(2, OpCode.Call, trim, trimmed, text);
        var method = Method([
            new(0, OpCode.CheckEqual, flag, text, new Immediate(0)),
            new(1, OpCode.ConditionalJump, raise, flag),
            call,
            new(4, OpCode.Return, trimmed),
            raise,
        ], text, trimmed, flag);

        Il2CppCheckRecovery.Run(method);

        Assert.Multiple(() =>
        {
            Assert.That(All(method).Any(i => i.OpCode is OpCode.ConditionalJump or OpCode.Throw), Is.False, () => Dump(method));
            Assert.That(Il2CppCheckRecovery.ReceiverWasNullChecked(method, call), Is.True);
        });
    }
}
