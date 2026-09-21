using System.Reflection;
using System.Linq;
using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class NonReturningHelperTests
{
    [SetUp] public void Setup() { Cpp2IlApi.ResetInternalState(); TestGameLoader.LoadSimple2019Game(); }

    [TestCase(true)]
    [TestCase(false)]
    public void NonReturningHelperDoesNotInventUnbalancedReturn(bool proven)
    {
        var app=Cpp2IlApi.CurrentAppContext!;
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Fixture",app.SystemTypes.SystemVoidType,MethodAttributes.Static,[]);
        var helper=new Instruction(1,OpCode.Call,new Immediate(0x1000),new Register(null,"X0"));
        method.ControlFlowGraph=new ISILControlFlowGraph([new(0,OpCode.ShiftStack,new Immediate(-80)),helper,new(2,OpCode.Return)]);
        method.ParameterOperands=[];method.AnalysisWarnings=[];
        var blocks=NonReturningHelperRecovery.Select(method.ControlFlowGraph, address => proven && address==0x1000);
        var edgeCount=method.ControlFlowGraph.Blocks.Sum(b=>b.Successors.Count);
        StackAnalyzer.Analyze(method, blocks);
        Assert.That(method.AnalysisWarnings.Count,Is.EqualTo(proven?0:1));
        Assert.That(method.ControlFlowGraph.Blocks.Sum(b=>b.Successors.Count),Is.EqualTo(edgeCount),"Native SP proof must not mutate the shared SSA graph");
    }

    [TestCase(0,true)]
    [TestCase(1,false)] // Returning helper, not a no-return wrapper.
    [TestCase(2,false)] // Conditional branch could bypass the raise.
    [TestCase(3,false)] // Ordinary branch to returning code.
    [TestCase(4,false)] // Unknown/missing instructions are not evidence.
    public void LinearProofRequiresAnUnavoidableKnownRaise(int kind,bool expected)
    {
        var words=new Dictionary<ulong,uint>{{0x1000,0xf81f0ffe},{0x1004,0x940003ff},{0x2000,0xaa1f03e1},{0x2004,0x140003ff}};
        if(kind==1)words[0x1000]=0xd65f03c0;
        if(kind==2)words[0x1000]=0x54000040;
        if(kind==3){words[0x1000]=0x14000400;words[0x2000]=0xd65f03c0;}
        if(kind==4)words.Remove(0x2004);
        Assert.That(NonReturningHelperRecovery.ProvesNoReturn(0x1000,0x3000,a=>words.TryGetValue(a,out var word)?word:null),Is.EqualTo(expected));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void ExportAnchorRequiresExactWrapper(bool wrongArgument)
    {
        var words=new Dictionary<ulong,uint>{{0x1000,0xf81f0ffe},{0x1004,wrongArgument?0xaa1f03e0u:0xaa1f03e1u},{0x1008,0x940003fe}};
        Assert.That(NonReturningHelperRecovery.MatchRaiseExport(0x1000,12,a=>words[a]),Is.EqualTo(wrongArgument?0UL:0x2000UL));
        Assert.That(NonReturningHelperRecovery.MatchRaiseExport(0x1000,16,a=>words[a]),Is.Zero);
    }
}
