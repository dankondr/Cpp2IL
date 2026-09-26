using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class DelegateInvokeRecoveryTests
{
    [SetUp] public void Setup() { Cpp2IlApi.ResetInternalState(); TestGameLoader.LoadSimple2019Game(); }

    [TestCase(false)]
    [TestCase(true)]
    public void VoidDelegateTailDispatchBecomesInvokeAndReturn(bool resolvedField)
    {
        var app=Cpp2IlApi.CurrentAppContext!;
        var action=app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Action")!;
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Tail",app.SystemTypes.SystemVoidType,MethodAttributes.Static,[]);
        var value=new LocalVariable("value",new Register(null,"X1"),action);
        var target=new LocalVariable("target",new Register(null,"X2"),app.SystemTypes.SystemIntPtrType);
        // The frame's own delegate-internal loads prove the call is the delegate's invoke,
        // carried in the raw integer argument registers the unknown-callee layout leaves.
        var thisArg=new LocalVariable("thisArg",new Register(null,"rcx"));
        var methodInfo=new LocalVariable("methodInfo",new Register(null,"rdx"));
        var operands=new System.Collections.Generic.List<IOperand>{target,new LocalVariable("stale",new Register(null,"X0")),
            thisArg,methodInfo,new Register(null,"r8"),new Register(null,"r9"),
            new Register(null,"xmm0"),new Register(null,"xmm1"),new Register(null,"xmm2"),new Register(null,"xmm3")};
        var dispatch=new Instruction(3,OpCode.IndirectJump,operands);
        IOperand invokeImpl=resolvedField
            ? new FieldReference(app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Delegate")!.Fields.First(f=>f.Name=="invoke_impl"),value,app.Binary.PointerSizeBytes*3)
            : new MemoryOperand(value,addend:app.Binary.PointerSizeBytes*3);
        method.ControlFlowGraph=new ISILControlFlowGraph([
            new Instruction(0,OpCode.Move,target,invokeImpl),
            new Instruction(1,OpCode.Move,thisArg,new MemoryOperand(value,addend:16)),
            new Instruction(2,OpCode.Move,methodInfo,new MemoryOperand(value,addend:8)),
            dispatch]);

        DelegateInvokeRecovery.Run(method);

        Assert.That(dispatch.OpCode,Is.EqualTo(OpCode.CallVoid));
        Assert.That(((MethodAnalysisContext)dispatch.Operands[0]).Name,Is.EqualTo("Invoke"));
        Assert.That(dispatch.Operands[1],Is.SameAs(value));
        Assert.That(dispatch.Operands.Count,Is.EqualTo(3)); // target, receiver, hidden MethodInfo
        Assert.That(method.ControlFlowGraph.Instructions.Last().OpCode,Is.EqualTo(OpCode.Return));
    }

    [Test]
    public void ParameterizedDelegateTailDispatchIsLeftUnchanged()
    {
        var app=Cpp2IlApi.CurrentAppContext!;
        var eventHandler=app.AssembliesByName["mscorlib"].GetTypeByFullName("System.EventHandler")!;
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Tail",app.SystemTypes.SystemVoidType,MethodAttributes.Static,[]);
        var value=new LocalVariable("value",new Register(null,"X1"),eventHandler);
        var dispatch=new Instruction(1,OpCode.IndirectJump,
            new MemoryOperand(value,addend:app.Binary.PointerSizeBytes*3));
        method.ControlFlowGraph=new ISILControlFlowGraph([dispatch]);

        DelegateInvokeRecovery.Run(method);

        Assert.That(dispatch.OpCode,Is.EqualTo(OpCode.IndirectJump));
    }

    [Test]
    public void ResolvedFieldOrdinaryDispatchIsLeftUnchanged()
    {
        var app=Cpp2IlApi.CurrentAppContext!;
        var action=app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Action")!;
        var value=new LocalVariable("value",new Register(null,"X1"),action);
        var invokeImpl=app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Delegate")!.Fields.First(f=>f.Name=="invoke_impl");
        var dispatch=new Instruction(1,OpCode.IndirectCall,new FieldReference(invokeImpl,value,app.Binary.PointerSizeBytes*3));
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Call",app.SystemTypes.SystemVoidType,MethodAttributes.Static,[])
            {ControlFlowGraph=new ISILControlFlowGraph([dispatch])};

        DelegateInvokeRecovery.Run(method);

        Assert.That(dispatch.OpCode,Is.EqualTo(OpCode.IndirectCall));
    }
}
