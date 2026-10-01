using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

// `list.Clear(); Save();` in a class holding a List<T>: IL2CPP inlines Clear as
// `_version++; _size = 0;` (plus Array.Clear behind `if (size > 0)` for reference
// elements). Only that body becomes the Clear call; what follows it stays.
public class InlinedListClearRecoveryTests
{
    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;

    private InjectedMethodAnalysisContext _method = null!;
    private MethodAnalysisContext _save = null!;
    private InjectedFieldAnalysisContext _other = null!;
    private LocalVariable _this = null!;

    [SetUp]
    public void LoadGame()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var owner = new InjectedTypeAnalysisContext(App.AssembliesByName["mscorlib"], "Tests", "Holder",
            App.SystemTypes.SystemObjectType, TypeAttributes.Public);
        _other = new InjectedFieldAnalysisContext("other", App.SystemTypes.SystemInt32Type,
            FieldAttributes.Public, owner, 0);
        owner.Fields.Add(_other);
        var save = new InjectedMethodAnalysisContext(owner, "Save", App.SystemTypes.SystemVoidType,
            MethodAttributes.Public, []);
        owner.Methods.Add(save);
        _save = save;
        _method = new InjectedMethodAnalysisContext(owner, "ClearAndSave", App.SystemTypes.SystemVoidType,
            MethodAttributes.Public, []);
        _this = Local("this", owner);
    }

    private static LocalVariable Local(string name, TypeAnalysisContext? type) =>
        new(name, new Register(null, name), type);

    private static LocalVariable NewList(string name, TypeAnalysisContext element) =>
        Local(name, App.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!
            .MakeGenericInstanceType(element));

    private static FieldReference Field(LocalVariable list, string name) =>
        new(((GenericInstanceTypeAnalysisContext)list.Type!).GenericType.Fields.Single(field => field.Name == name),
            list, 0);

    // Value-type elements: `_version++; _size = 0;` in the block's straight line.
    private static Instruction[] ValueTypeClear(LocalVariable list, int index)
    {
        var bumped = Local($"bumped{index}", App.SystemTypes.SystemInt32Type);
        return
        [
            new(index, OpCode.Add, bumped, Field(list, "_version"), new Immediate(1)),
            new(index + 1, OpCode.Move, Field(list, "_size"), new Immediate(0)),
            new(index + 2, OpCode.Move, Field(list, "_version"), bumped),
        ];
    }

    // Reference elements: the same, then `if (size < 1) goto merge; Array.Clear(_items, 0, size);`.
    private static Instruction[] ReferenceTypeClear(LocalVariable list, int index, Instruction merge)
    {
        var empty = Local($"empty{index}", App.SystemTypes.SystemBooleanType);
        var arrayClear = App.SystemTypes.SystemArrayType!.Methods.First(method =>
            method.Name == "Clear" && method.Parameters.Count == 3);
        return
        [
            ..ValueTypeClear(list, index),
            new(index + 3, OpCode.CheckLess, empty, Field(list, "_size"), new Immediate(1)),
            new(index + 4, OpCode.ConditionalJump, merge, empty),
            new(index + 5, OpCode.CallVoid, arrayClear, Field(list, "_items"), new Immediate(0), Field(list, "_size")),
        ];
    }

    private System.Collections.Generic.List<Instruction> Recover(int expected, params Instruction[] instructions)
    {
        _method.ControlFlowGraph = new ISILControlFlowGraph(instructions.ToList());
        Assert.That(InlinedListClearRecovery.Run(_method), Is.EqualTo(expected));
        return _method.ControlFlowGraph.Blocks.SelectMany(block => block.Instructions).ToList();
    }

    private static void AssertClearCall(Instruction instruction, LocalVariable list)
    {
        Assert.That(instruction.OpCode, Is.EqualTo(OpCode.CallVoid));
        Assert.That(((MethodAnalysisContext)instruction.Operands[0]).Name, Is.EqualTo("Clear"));
        Assert.That(instruction.Operands[1], Is.SameAs(list));
    }

    [Test]
    public void CallAfterInlinedClearSurvives()
    {
        var list = NewList("list", App.SystemTypes.SystemInt32Type);
        var save = new Instruction(3, OpCode.CallVoid, _save, _this);

        var instructions = Recover(1, [..ValueTypeClear(list, 0), save, new(4, OpCode.Return)]);

        Assert.That(instructions, Has.Count.EqualTo(3));
        AssertClearCall(instructions[0], list);
        Assert.That(instructions[1], Is.SameAs(save));
        Assert.That(instructions[2].OpCode, Is.EqualTo(OpCode.Return));
    }

    [Test]
    public void UnrelatedStoreAfterInlinedClearSurvives()
    {
        var list = NewList("list", App.SystemTypes.SystemInt32Type);
        var store = new Instruction(3, OpCode.Move, new FieldReference(_other, _this, 0), new Immediate(0));

        var instructions = Recover(1, [..ValueTypeClear(list, 0), store, new(4, OpCode.Return)]);

        Assert.That(instructions, Has.Count.EqualTo(3));
        AssertClearCall(instructions[0], list);
        Assert.That(instructions[1], Is.SameAs(store));
        Assert.That(instructions[2].OpCode, Is.EqualTo(OpCode.Return));
    }

    // `if (list.Count < 1) return; list.Clear(); Save();` - the early return is not
    // where the Clear rejoins, and the call after it stays.
    [Test]
    public void EarlyReturnBeforeClearKeepsTheCall()
    {
        var list = NewList("list", App.SystemTypes.SystemInt32Type);
        var empty = Local("empty", App.SystemTypes.SystemBooleanType);
        var exit = new Instruction(6, OpCode.Return);
        var save = new Instruction(5, OpCode.CallVoid, _save, _this);

        var instructions = Recover(1,
        [
            new(0, OpCode.CheckLess, empty, Field(list, "_size"), new Immediate(1)),
            new(1, OpCode.ConditionalJump, exit, empty),
            ..ValueTypeClear(list, 2),
            save,
            exit,
        ]);

        Assert.That(instructions.Select(i => i.OpCode), Is.EqualTo(new[]
            { OpCode.CheckLess, OpCode.ConditionalJump, OpCode.CallVoid, OpCode.CallVoid, OpCode.Return }));
        AssertClearCall(instructions[2], list);
        Assert.That(instructions[3], Is.SameAs(save));
    }

    // Four Clears in a row (two behind the Array.Clear branch), then a call: every
    // body becomes its call, the clearing paths go, and the trailing call stays.
    [Test]
    public void FourClearsThenACall()
    {
        var a = NewList("a", App.SystemTypes.SystemStringType);
        var b = NewList("b", App.SystemTypes.SystemStringType);
        var c = NewList("c", App.SystemTypes.SystemInt32Type);
        var d = NewList("d", App.SystemTypes.SystemInt32Type);
        var cBody = ValueTypeClear(c, 20);
        var bBody = ReferenceTypeClear(b, 10, cBody[0]);
        var save = new Instruction(30, OpCode.CallVoid, _save, _this);

        var instructions = Recover(4,
        [
            ..ReferenceTypeClear(a, 0, bBody[0]),
            ..bBody,
            ..cBody,
            ..ValueTypeClear(d, 23),
            save,
            new(31, OpCode.Return),
        ]);

        Assert.That(instructions, Has.Count.EqualTo(6));
        AssertClearCall(instructions[0], a);
        AssertClearCall(instructions[1], b);
        AssertClearCall(instructions[2], c);
        AssertClearCall(instructions[3], d);
        Assert.That(instructions[4], Is.SameAs(save));
        Assert.That(instructions[5].OpCode, Is.EqualTo(OpCode.Return));
    }
}
