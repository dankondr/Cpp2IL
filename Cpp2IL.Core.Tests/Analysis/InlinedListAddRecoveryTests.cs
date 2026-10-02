using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

// IL2CPP inlines List<T>.Add as `items = _items; _version++; if (_size < items.Length)
// { _size++; items[size] = item; } else AddWithResize(item);`. Only that body goes: the
// slow path's AddWithResize stands for the Add, and everything else stays.
public class InlinedListAddRecoveryTests
{
    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;

    private InjectedMethodAnalysisContext _method = null!;
    private MethodAnalysisContext _addWithResize = null!;
    private LocalVariable _list = null!;
    private int _index;

    [SetUp]
    public void LoadGame()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var mscorlib = App.AssembliesByName["mscorlib"];
        var listDefinition = mscorlib.GetTypeByFullName("System.Collections.Generic.List`1")!;
        var owner = new InjectedTypeAnalysisContext(mscorlib, "Tests", "Holder",
            App.SystemTypes.SystemObjectType, TypeAttributes.Public);
        _method = new InjectedMethodAnalysisContext(owner, "Fill", App.SystemTypes.SystemVoidType,
            MethodAttributes.Public, []);
        _addWithResize = new InjectedMethodAnalysisContext(listDefinition, "AddWithResize",
            App.SystemTypes.SystemVoidType, MethodAttributes.Private, [App.SystemTypes.SystemInt32Type]);
        _list = Local("list", listDefinition.MakeGenericInstanceType(App.SystemTypes.SystemInt32Type));
        _index = 0;
    }

    private static LocalVariable Local(string name, TypeAnalysisContext? type) =>
        new(name, new Register(null, name), type);

    private FieldReference Field(string name) =>
        new(((GenericInstanceTypeAnalysisContext)_list.Type!).GenericType.Fields.Single(field => field.Name == name),
            _list, 0);

    private Instruction At(OpCode opCode, params List<IOperand> operands) => new(_index++, opCode, operands);

    private LocalVariable Int(string name) => Local(name, App.SystemTypes.SystemInt32Type);

    // `items = _items; _version++` - the prologue; the fast path repeats the next one's
    // version bump and carries the array over in a register copy instead of reloading it.
    private IEnumerable<Instruction> Prologue(LocalVariable items, bool fastCopy, LocalVariable? previousItems = null)
    {
        var bumped = Int($"bumped{_index}");
        if (!fastCopy)
            yield return At(OpCode.Move, items, Field("_items"));
        yield return At(OpCode.Add, bumped, Field("_version"), new Immediate(1));
        yield return At(OpCode.Move, Field("_version"), bumped);
        if (fastCopy)
            yield return new Instruction(-1, OpCode.Move, items, previousItems!);
    }

    private List<Instruction> Check(LocalVariable items, Instruction slow)
    {
        var size = Int($"size{_index}");
        var fits = Local($"fits{_index}", App.SystemTypes.SystemBooleanType);
        var full = Local($"full{_index}", App.SystemTypes.SystemBooleanType);
        return
        [
            At(OpCode.Move, size, Field("_size")),
            At(OpCode.CheckLess, fits, Field("_size"), new ArrayLength(items)),
            At(OpCode.Not, full, fits),
            At(OpCode.ConditionalJump, slow, full),
        ];
    }

    private List<Instruction> FastPath(LocalVariable items, IOperand item)
    {
        var grown = Int($"grown{_index}");
        return
        [
            At(OpCode.Add, grown, Field("_size"), new Immediate(1)),
            At(OpCode.Move, Field("_size"), grown),
            At(OpCode.Move, new ArrayAccess(items, Field("_size")), item),
        ];
    }

    private List<Instruction> Recover(int expected, List<Instruction> instructions)
    {
        _method.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        // The lifter's graph keeps a call and what follows it in one block.
        _method.ControlFlowGraph.MergeCallBlocks();
        Assert.That(InlinedListAddRecovery.Run(_method), Is.EqualTo(expected));
        return _method.ControlFlowGraph.Blocks.SelectMany(block => block.Instructions).ToList();
    }

    private bool TouchesListInternals(Instruction instruction) => instruction.Operands.Any(operand =>
        operand is FieldReference field && ReferenceEquals(field.Local, _list)
        || operand is ArrayLength or ArrayAccess);

    // `new List<int> { 1, 2, 3, 4 }`: each Add's slow path also holds the next Add's
    // prologue, so the block with the previous AddWithResize is part of the next body's run.
    [Test]
    public void FourInlinedAddsOfConstantsKeepEveryAdd()
    {
        var items = Enumerable.Range(0, 4).Select(i => Local($"items{i}", null)).ToArray();
        var exit = new Instruction(1000, OpCode.Return);
        var instructions = Prologue(items[0], fastCopy: false).ToList();
        var checkHeads = new List<Instruction>();
        var fastJumps = new List<Instruction>();
        for (var i = 0; i < 4; i++)
        {
            var slow = new Instruction(500 + i, OpCode.CallVoid, _addWithResize, _list, new Immediate(i + 1));
            var check = Check(items[i], slow);
            checkHeads.Add(check[0]);
            instructions.AddRange(check);
            instructions.AddRange(FastPath(items[i], new Immediate(i + 1)));
            if (i < 3)
                instructions.AddRange(Prologue(items[i + 1], fastCopy: true, items[i]));
            fastJumps.Add(At(OpCode.Jump, exit));
            instructions.Add(fastJumps[i]);
            instructions.Add(slow);
            if (i < 3)
                instructions.AddRange(Prologue(items[i + 1], fastCopy: false));
        }
        instructions.Add(exit);
        // Each fast path rejoins at the next Add's check (the last one at the return).
        for (var i = 0; i < 3; i++)
            fastJumps[i].SetOperand(0, checkHeads[i + 1]);

        var recovered = Recover(4, instructions);

        var adds = recovered.Where(instruction => instruction.Operands.FirstOrDefault() == _addWithResize).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(adds.Select(add => ((Immediate)add.Operands[2]).Value), Is.EqualTo(new long[] { 1, 2, 3, 4 }));
            Assert.That(recovered.Where(TouchesListInternals), Is.Empty);
            Assert.That(recovered, Does.Contain(exit));
        });
    }

    // `if (list.Count != 20) list.Add(x);` with the prologue in a block of its own: the
    // emptied block goes, and the guard's branch lands on what follows it.
    [Test]
    public void BranchIntoAnEmptiedPrologueKeepsItsTarget()
    {
        var items = Local("items", null);
        var item = Int("item");
        var other = Local("other", App.SystemTypes.SystemBooleanType);
        var exit = new Instruction(1000, OpCode.Return);
        var slow = new Instruction(500, OpCode.CallVoid, _addWithResize, _list, item);
        var prologue = Prologue(items, fastCopy: false).ToList();
        var check = Check(items, slow);
        var fallThrough = At(OpCode.Jump, check[0]);
        var instructions = new List<Instruction>
        {
            At(OpCode.CheckNotEqual, other, Field("_size"), new Immediate(20)),
            At(OpCode.ConditionalJump, prologue[0], other),
            At(OpCode.Return),
        };
        instructions.AddRange(prologue);
        instructions.Add(fallThrough);
        instructions.AddRange(check);
        instructions.AddRange(FastPath(items, item));
        instructions.Add(At(OpCode.Jump, exit));
        instructions.Add(slow);
        instructions.Add(exit);
        _method.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        _method.ControlFlowGraph.MergeCallBlocks();
        // The lifter's graph has the prologue fall into the check without a jump.
        _method.ControlFlowGraph.Blocks.Single(block => block.Instructions.Contains(fallThrough)).Instructions.Remove(fallThrough);

        Assert.That(InlinedListAddRecovery.Run(_method), Is.EqualTo(1));

        var blocks = _method.ControlFlowGraph.Blocks;
        var targets = blocks.SelectMany(block => block.Instructions).Select(instruction => instruction.Operands.FirstOrDefault())
            .OfType<Block>().ToList();
        Assert.Multiple(() =>
        {
            Assert.That(targets, Is.Not.Empty);
            Assert.That(targets, Has.All.Matches<Block>(target => target != null && blocks.Contains(target) && target.Instructions.Count > 0));
            Assert.That(blocks.SelectMany(block => block.Instructions), Does.Contain(slow));
        });
    }

    // The item is computed between the prologue and the size check, and the slow path
    // passes it on: it is not part of the Add and must stay.
    [Test]
    public void ItemComputedBeforeTheCheckSurvives()
    {
        var items = Local("items", null);
        var high = Int("high");
        var item = Int("item");
        var x = Int("x");
        var exit = new Instruction(1000, OpCode.Return);
        var slow = new Instruction(500, OpCode.CallVoid, _addWithResize, _list, item);
        var shift = At(OpCode.ShiftLeft, high, x, new Immediate(32));
        var pack = At(OpCode.Or, item, new Immediate(1), high);
        var instructions = Prologue(items, fastCopy: false).ToList();
        instructions.AddRange([shift, pack]);
        instructions.AddRange(Check(items, slow));
        instructions.AddRange(FastPath(items, item));
        instructions.Add(At(OpCode.Jump, exit));
        instructions.Add(slow);
        instructions.Add(exit);

        var recovered = Recover(1, instructions);

        Assert.Multiple(() =>
        {
            Assert.That(recovered, Does.Contain(shift));
            Assert.That(recovered, Does.Contain(pack));
            Assert.That(recovered.IndexOf(pack), Is.LessThan(recovered.IndexOf(slow)));
            Assert.That(recovered.Where(TouchesListInternals), Is.Empty);
        });
    }
}
