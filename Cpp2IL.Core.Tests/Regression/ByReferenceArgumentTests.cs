using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// castle-recovery#306: AAPCS64 passes a by-value struct wider than 16 bytes as the
// address of a caller-owned copy (`add x1, sp, #0x48`). The managed call takes the
// value; a ref/out parameter takes the address of storage of its element type.
public class ByReferenceArgumentTests
{
    private ApplicationAnalysisContext _app = null!;
    private TypeAnalysisContext _loadout = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
        _app.InstructionSet = new NewArmV8InstructionSet();
        var loadout = new InjectedTypeAnalysisContext(_app.AssembliesByName["mscorlib"], "Tests", "Loadout",
            _app.SystemTypes.SystemValueTypeType, R.TypeAttributes.Public | R.TypeAttributes.SequentialLayout);
        foreach (var (name, offset) in new[] { ("a", 0), ("b", 8), ("c", 16) })
            loadout.Fields.Add(new InjectedFieldAnalysisContext(name, _app.SystemTypes.SystemInt64Type,
                R.FieldAttributes.Public, loadout, offset));
        _loadout = loadout;
    }

    private MethodAnalysisContext Callee(TypeAnalysisContext parameterType)
    {
        var owner = new InjectedTypeAnalysisContext(_app.AssembliesByName["mscorlib"], "Tests", "Panel",
            _app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        return new InjectedMethodAnalysisContext(owner, "SetData", _app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, [parameterType]);
    }

    private MethodAnalysisContext Caller(params Instruction[] instructions)
    {
        var caller = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "Run",
            _app.SystemTypes.SystemVoidType, R.MethodAttributes.Public | R.MethodAttributes.Static, [])
        {
            ParameterLocals = [],
            AnalysisWarnings = [],
        };
        caller.ControlFlowGraph = new ISILControlFlowGraph([.. instructions, new Instruction(99, OpCode.Return)]);
        caller.Locals = caller.ControlFlowGraph.Instructions
            .SelectMany(i => i.Operands.SelectMany(LocalVariables.OperandLocals)).Distinct().ToList();
        return caller;
    }

    private static LocalVariable Slot(string name) => new(name, new Register(null, name), null);

    // memcpy(&slot, &result, 24): the copy IL2CPP makes before passing the struct.
    private Instruction FillFrom(LocalVariable slot) =>
        new(0, OpCode.Call, new StringLiteral("memcpy"), new LocalVariable("r", new Register(null, "X0", 5), null),
            new AddressOf(slot), new AddressOf(new LocalVariable("hret", new Register(null, "HRET_1"), _loadout)),
            new Immediate(24));

    [Test]
    public void WideByValueArgumentIsTheCopyItsAddressNames()
    {
        var slot = Slot("stack_-108");
        var call = new Instruction(1, OpCode.CallVoid, Callee(_loadout), new AddressOf(slot));
        var caller = Caller(FillFrom(slot), call);

        ByReferenceArgumentRecovery.Run(caller);

        Assert.That(call.Operands[1], Is.SameAs(slot), "the call passes the struct the address names");
        Assert.That(slot.Type, Is.SameAs(_loadout));
    }

    [Test]
    public void SlotNothingFillsKeepsItsAddress()
    {
        var slot = Slot("stack_-108");
        var call = new Instruction(1, OpCode.CallVoid, Callee(_loadout), new AddressOf(slot));
        var caller = Caller(call);

        ByReferenceArgumentRecovery.Run(caller);

        Assert.That(call.Operands[1], Is.TypeOf<AddressOf>());
        Assert.That(slot.Type, Is.Null, "an unfilled slot would be read unassigned");
    }

    [Test]
    public void SlotOverlappedByAnotherFrameLocalKeepsItsAddress()
    {
        var slot = Slot("stack_-108");
        var inside = new LocalVariable("inside", new Register(null, "stack_-100"), _app.SystemTypes.SystemInt64Type);
        var call = new Instruction(1, OpCode.CallVoid, Callee(_loadout), new AddressOf(slot));
        var caller = Caller(FillFrom(slot), new Instruction(2, OpCode.Move, inside, new Immediate(1)), call);

        ByReferenceArgumentRecovery.Run(caller);

        Assert.That(call.Operands[1], Is.TypeOf<AddressOf>());
        Assert.That(slot.Type, Is.Null);
    }

    [Test]
    public void RefParameterTypesTheSlotAndKeepsTheAddress()
    {
        var slot = Slot("stack_-108");
        var call = new Instruction(1, OpCode.CallVoid, Callee(new ByRefTypeAnalysisContext(_loadout)),
            new AddressOf(slot));
        var caller = Caller(call);

        ByReferenceArgumentRecovery.Run(caller);

        Assert.That(call.Operands[1], Is.TypeOf<AddressOf>(), "ref/out takes the address");
        Assert.That(slot.Type, Is.SameAs(_loadout), "the callee fills storage of the element type");
    }

    [Test]
    public void ManagedPointerArgumentIsDereferenced()
    {
        var pointer = new LocalVariable("p", new Register(null, "X19", 2), new ByRefTypeAnalysisContext(_loadout));
        var call = new Instruction(1, OpCode.CallVoid, Callee(_loadout), pointer);
        var caller = Caller(call);

        ByReferenceArgumentRecovery.Run(caller);

        Assert.That(call.Operands[1], Is.TypeOf<MemoryOperand>());
        Assert.That(((MemoryOperand)call.Operands[1]).Base, Is.SameAs(pointer));
    }

    [Test]
    public void NarrowStructArgumentIsLeftAlone()
    {
        var narrow = _app.SystemTypes.SystemInt64Type;
        var slot = Slot("stack_-108");
        var call = new Instruction(1, OpCode.CallVoid, Callee(narrow), new AddressOf(slot));
        var caller = Caller(FillFrom(slot), call);

        ByReferenceArgumentRecovery.Run(caller);

        Assert.That(call.Operands[1], Is.TypeOf<AddressOf>());
    }

    // The copy itself is fed from a frame slot nothing writes (a register copy
    // out of a hidden-return slot the lift does not connect to the call's result):
    // the argument keeps its address rather than pass unassigned bytes.
    [Test]
    public void CopyOfAnUnwrittenSlotKeepsItsAddress()
    {
        var unwritten = new LocalVariable("stack_-90", new Register(null, "stack_-90"), _loadout);
        var copy = new LocalVariable("stack_-B0", new Register(null, "stack_-B0"), _loadout);
        var call = new Instruction(1, OpCode.CallVoid, Callee(_loadout), new AddressOf(copy));
        var caller = Caller(new Instruction(0, OpCode.Move, copy, unwritten), call);

        ByReferenceArgumentRecovery.Run(caller);

        Assert.That(call.Operands[1], Is.TypeOf<AddressOf>());
    }
}
