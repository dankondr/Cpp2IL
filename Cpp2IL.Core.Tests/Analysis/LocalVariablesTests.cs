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
}
