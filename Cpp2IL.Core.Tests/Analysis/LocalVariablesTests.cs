using System.Reflection;
using System.Linq;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class LocalVariablesTests
{
    [Test]
    public void UnusedThisParameterDoesNotProduceWarning()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "InstanceMethod",
            app.SystemTypes.SystemVoidType, MethodAttributes.Public, []);
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, new Register(8, "X8"), new Immediate(1)),
            new(1, OpCode.Return)
        ]);
        method.ParameterOperands = [new Register(0, "X0")];
        method.AnalysisWarnings = [];

        LocalVariables.CreateAll(method);

        Assert.Multiple(() =>
        {
            Assert.That(method.AnalysisWarnings, Is.Empty);
            Assert.That(method.ParameterLocals.Any(local => local.IsThis), Is.False);
        });
    }

    [Test]
    public void HiddenBufferReturnReturnsTheBufferItBuilt()
    {
        // The struct is built in the caller's buffer (`str x0, [x8]; …; ret`); the return register
        // at `ret` holds nothing of it.
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var guid = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Guid")!;
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Build", guid,
            MethodAttributes.Public | MethodAttributes.Static, []);
        var resolver = app.InstructionSet.CallingConventionResolver!;
        var ret = new Instruction(1, OpCode.Return, resolver.ReturnRegister(method));
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, new MemoryOperand(resolver.HiddenReturnBufferRegister(method)!.Value), new Immediate(1)),
            ret
        ]);
        method.ParameterOperands = [];
        method.AnalysisWarnings = [];

        LocalVariables.CreateAll(method);

        Assert.That(ret.Operands, Is.EqualTo(new IOperand[] { method.Locals.Single(local => local.Name == "returnBuffer") }));
    }
}
