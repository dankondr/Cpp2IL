using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: duplicate-definition (CS0102) from inlined event raises.
// A field-like event's raiser `E?.Invoke()` gets inlined into foreign bodies
// as a null-check on the private backing field plus a direct delegate
// Invoke on it, leaving a foreign field reference that keeps the emitted
// field widened and decompiles as a field/event duplicate. When the only
// entry into the raise block is that null guard and the declaring type has
// exactly one signature-compatible method whose own body invokes the field,
// the raise is proven to be the inlined raiser: respell the call to it.
public class InlinedEventRaiseRecoveryTests
{
    private ApplicationAnalysisContext _app = null!;
    private TypeAnalysisContext _action = null!;
    private MethodAnalysisContext _invoke = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2022Game();
        _action = _app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Action")!;
        _invoke = _action.Methods.First(m => m.Name == "Invoke");
    }

    private (InjectedTypeAnalysisContext type, FieldAnalysisContext field) NotifierAssembly()
    {
        var assembly = _app.InjectAssembly("Recovered.Events");
        var notifier = assembly.InjectType("Recovered", "Notifier",
            _app.SystemTypes.SystemObjectType,
            TypeAttributes.Public | TypeAttributes.Class);
        var field = notifier.InjectFieldContext("Changed", _action,
            FieldAttributes.Private);
        var adder = notifier.InjectMethodContext("add_Changed",
            _app.SystemTypes.SystemVoidType, MethodAttributes.Public, [_action]);
        var remover = notifier.InjectMethodContext("remove_Changed",
            _app.SystemTypes.SystemVoidType, MethodAttributes.Public, [_action]);
        notifier.InjectEventContext("Changed", _action, adder, remover, null,
            EventAttributes.None);
        return (notifier, field);
    }

    // `RaiseChanged` (and any alternates) carry the raise idiom themselves:
    // load the field, dispatch on its invoke_impl slot.
    private MethodAnalysisContext AddRaiser(InjectedTypeAnalysisContext notifier,
        FieldAnalysisContext field, string name)
    {
        var raiser = notifier.InjectMethodContext(name,
            _app.SystemTypes.SystemVoidType, MethodAttributes.Public, []);
        var thisLocal = new LocalVariable("this", new Register(null, "x0"), notifier);
        var del = new LocalVariable("del", new Register(null, "x8"), _action);
        raiser.ConvertedIsil =
        [
            new Instruction(0, OpCode.Move, del, new FieldReference(field, thisLocal, 0)),
            new Instruction(1, OpCode.IndirectCall,
                new MemoryOperand(del, addend: _app.Binary.PointerSizeBytes * 3), del)
        ];
        return raiser;
    }

    // Foreign body `notifier.E?.Invoke()` as the compiler inlines it:
    // flag = (E == null); if (flag) skip; E.Invoke(); skip: ret
    private (MethodAnalysisContext caller, Instruction invokeCall, Instruction guard)
        ForeignRaise(InjectedTypeAnalysisContext notifier, FieldAnalysisContext field)
    {
        var assembly = notifier.DeclaringAssembly;
        var driver = assembly.InjectType("Recovered", "Driver",
            _app.SystemTypes.SystemObjectType,
            TypeAttributes.Public | TypeAttributes.Class);
        var caller = driver.InjectMethodContext("Fire",
            _app.SystemTypes.SystemVoidType, MethodAttributes.Public, [notifier]);

        var recv = new LocalVariable("notifier", new Register(null, "x1"), notifier);
        var flag = new LocalVariable("flag", new Register(null, "x2"),
            _app.SystemTypes.SystemBooleanType);
        var check = new Instruction(0, OpCode.CheckEqual, flag,
            new FieldReference(field, recv, 0), new Immediate(0));
        var ret = new Instruction(3, OpCode.Return);
        var guard = new Instruction(1, OpCode.ConditionalJump, ret, flag);
        var invokeCall = new Instruction(2, OpCode.CallVoid, _invoke,
            new FieldReference(field, recv, 0));
        caller.ConvertedIsil = [check, guard, invokeCall, ret];
        caller.ControlFlowGraph = new ISILControlFlowGraph(caller.ConvertedIsil);
        return (caller, invokeCall, guard);
    }

    // Invoked through reflection so the fixture still compiles - and the
    // assertions still fail - on a tree where the recovery pass is absent.
    private static void Run(MethodAnalysisContext caller)
    {
        var method = typeof(InlinedEventRaiseRecovery).GetMethod("Run",
            BindingFlags.Static | BindingFlags.NonPublic | BindingFlags.Public);
        if (method is null)
        {
            Assert.Fail("InlinedEventRaiseRecovery.Run does not exist");
            return;
        }
        method.Invoke(null, [caller]);
    }

    private static bool UsesField(MethodAnalysisContext caller, FieldAnalysisContext field) =>
        caller.ControlFlowGraph!.Blocks
            .SelectMany(b => b.Instructions)
            .SelectMany(i => i.Operands.Concat(i.Sources))
            .OfType<FieldReference>()
            .Any(f => f.Field == field);

    [Test]
    public void GuardedForeignRaiseRespellsToUniqueRaiser()
    {
        var (notifier, field) = NotifierAssembly();
        var raiser = AddRaiser(notifier, field, "RaiseChanged");
        var (caller, invokeCall, _) = ForeignRaise(notifier, field);

        Run(caller);

        Assert.Multiple(() =>
        {
            Assert.That(invokeCall.Operands[0], Is.SameAs(raiser),
                "the inlined delegate invoke is respelled to the proven raiser");
            Assert.That(UsesField(caller, field), Is.False,
                "no foreign reference to the private backing field remains");
            Assert.That(caller.ControlFlowGraph!.Blocks
                    .SelectMany(b => b.Instructions)
                    .Any(i => i.OpCode == OpCode.ConditionalJump), Is.False,
                "the null guard folds into the raiser's own body");
            Assert.That(invokeCall.Operands[1], Is.TypeOf<LocalVariable>(),
                "the raiser is invoked on the object that held the event");
        });
    }

    [Test]
    public void AmbiguousRaisersKeepFieldAccess()
    {
        var (notifier, field) = NotifierAssembly();
        AddRaiser(notifier, field, "RaiseChanged");
        AddRaiser(notifier, field, "RaiseChangedAlternate");
        var (caller, invokeCall, _) = ForeignRaise(notifier, field);

        Run(caller);

        Assert.Multiple(() =>
        {
            Assert.That(invokeCall.Operands[0], Is.SameAs(_invoke),
                "no unique raiser: the site keeps its delegate invoke");
            Assert.That(UsesField(caller, field), Is.True,
                "no unique raiser: the field access is preserved unchanged");
        });
    }

    [Test]
    public void UnguardedForeignRaiseKeepsFieldAccess()
    {
        var (notifier, field) = NotifierAssembly();
        AddRaiser(notifier, field, "RaiseChanged");
        var (caller, invokeCall, _) = ForeignRaise(notifier, field);

        // Strip the guard: a bare E.Invoke() with the invoke reached without
        // the null check is not a proven inlined `?.` raise.
        caller.ControlFlowGraph = new ISILControlFlowGraph(
            caller.ConvertedIsil!.Where(i => i.OpCode is not (OpCode.CheckEqual or OpCode.ConditionalJump)).ToList());

        Run(caller);

        Assert.Multiple(() =>
        {
            Assert.That(invokeCall.Operands[0], Is.SameAs(_invoke),
                "an unguarded delegate invoke is not an inlined `?.` raise");
            Assert.That(UsesField(caller, field), Is.True);
        });
    }
}
