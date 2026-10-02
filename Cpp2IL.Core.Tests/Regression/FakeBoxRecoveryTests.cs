using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// castle-recovery#289 class C: IL2CPP boxes a value that does not escape on the stack -
// Il2CppFakeBox<T> { klass, monitor = -1, T value } - and passes the frame address as
// the object (`MyEnum.X.ToString()`). The receiver is the boxed value, not the class
// pointer in the struct's first word.
public class FakeBoxRecoveryTests
{
    private static (MethodAnalysisContext Method, Instruction Call, LocalVariable KlassCell, LocalVariable ValueCell)
        Build(ApplicationAnalysisContext app, TypeAnalysisContext classOf, long sentry)
    {
        var mscorlib = app.AssembliesByName["mscorlib"];
        var klass = new RuntimeClassTypeAnalysisContext(classOf, mscorlib);
        var klassRegister = new LocalVariable("klass", new Register(null, "X8")) { Type = klass };
        var sentryRegister = new LocalVariable("sentry", new Register(null, "X22"));
        var address = new LocalVariable("address", new Register(null, "X0"));
        var result = new LocalVariable("result", new Register(null, "X0_r"));
        var klassCell = new LocalVariable("klassCell", new Register(null, "stack_-60")) { Type = klass };
        var sentryCell = new LocalVariable("sentryCell", new Register(null, "stack_-58"));
        var valueCell = new LocalVariable("valueCell", new Register(null, "stack_-50"));
        var toString = mscorlib.GetTypeByFullName("System.Enum")!.Methods.First(m => m is { Name: "ToString", Parameters.Count: 0 });
        var call = new Instruction(5, OpCode.Call, toString, result, address);
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "FakeBox", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var method = owner.InjectMethodContext("Run", app.SystemTypes.SystemStringType,
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, sentryRegister, new Immediate(sentry)),
            new(1, OpCode.Move, address, new AddressOf(klassCell)),
            new(2, OpCode.Move, sentryCell, sentryRegister),
            new(3, OpCode.Move, klassCell, klassRegister),
            new(4, OpCode.Move, valueCell, new Immediate(3)),
            call,
            new(6, OpCode.Return, result)]);
        method.Locals = [klassRegister, sentryRegister, address, result, klassCell, sentryCell, valueCell];
        method.ParameterLocals = [];
        return (method, call, klassCell, valueCell);
    }

    [TestCase("System.DayOfWeek", -1L, true)]
    [TestCase("System.String", -1L, false)]
    [TestCase("System.DayOfWeek", 0L, false)]
    public void StackBuiltBoxBecomesBoxOfTheValue(string classOf, long sentry, bool boxed)
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var type = app.AssembliesByName["mscorlib"].GetTypeByFullName(classOf)!;
        var (method, call, klassCell, valueCell) = Build(app, type, sentry);

        FakeBoxRecovery.Run(method);
        FakeBoxRecovery.ResolveTypes(method);

        var box = method.ControlFlowGraph!.Instructions.SingleOrDefault(i => i.OpCode == OpCode.Box);
        var listing = string.Join("\n", method.ControlFlowGraph.Instructions);
        if (boxed)
        {
            Assert.Multiple(() =>
            {
                Assert.That(box, Is.Not.Null, listing);
                Assert.That(box!.Operands[1], Is.SameAs(type), listing);
                Assert.That(box.Operands[2], Is.EqualTo(new AddressOf(valueCell)), listing);
                Assert.That(call.Operands[2], Is.SameAs(box.Operands[0]), listing);
            });
        }
        else
        {
            Assert.Multiple(() =>
            {
                Assert.That(box, Is.Null, listing);
                Assert.That(call.Operands[2] is AddressOf { Target: var target } && ReferenceEquals(target, klassCell)
                    || call.Operands[2] is LocalVariable { Name: "address" }, Is.True, listing);
            });
        }
    }
}
