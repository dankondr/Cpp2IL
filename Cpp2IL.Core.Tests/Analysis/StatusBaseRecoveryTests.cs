using System.Reflection;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class StatusBaseRecoveryTests
{
    [Test]
    public void Arm64IsInstVeneerFollowsRuntimeClassInitVeneer()
    {
        var words = new Dictionary<ulong, uint>
        {
            [0x1000] = 0x14000001,
            [0x1004] = 0x14000002,
        };

        Assert.That(NewArm64KeyFunctionAddresses.AdjacentIsInstVeneer(0x1000, address => words[address]),
            Is.EqualTo(0x1004));
        words[0x1004] = 0xd65f03c0;
        Assert.That(NewArm64KeyFunctionAddresses.AdjacentIsInstVeneer(0x1000, address => words[address]),
            Is.Zero);
    }

    [TestCase(false)]
    [TestCase(true)]
    public void WriteBarrierMatcherRequiresExactStoreWrapper(bool wrongStore)
    {
        var words=new Dictionary<ulong,uint>{{0x1000,0xaa0103e0},{0x1004,0xaa0203e1},{0x1008,0x1400003e},{0x1100,wrongStore?0xf9000002u:0xf9000001u},{0x1104,0x1400003f}};
        Assert.That(NewArm64KeyFunctionAddresses.MatchWriteBarrierExport(0x1000,a=>words[a]),Is.EqualTo(wrongStore?0UL:0x1200UL));
    }
    [SetUp] public void Setup() { Cpp2IlApi.ResetInternalState(); TestGameLoader.LoadSimple2019Game(); }

    [TestCase(0)]
    [TestCase(1)] // unknown root
    [TestCase(2)] // multiple definitions are not SSA evidence
    [TestCase(3)] // indexed memory is outside the recognized shape
    public void AddressAliasResolvesNegativeDisplacementBackToObjectField(int kind)
    {
        var app=Cpp2IlApi.CurrentAppContext!;
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Alias",app.SystemTypes.SystemVoidType,MethodAttributes.Static,[]);
        var owner=app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Exception")!;
        var field=owner.Fields.First(f=>!f.IsStatic);
        var receiver=new LocalVariable("receiver",new Register(null,"receiver"),owner);
        if(kind==1)receiver.Type=null;
        var address=new LocalVariable("address",new Register(null,"address"));
        var value=new LocalVariable("value",new Register(null,"value"));
        var original=new MemoryOperand(address,indexRegister:kind==3?value:null,addend:-0x20);
        var load=new Instruction(1,OpCode.Move,value,original);
        var instructions=new List<Instruction>{new(0,OpCode.Add,address,receiver,new Immediate(field.Offset+0x20)),load};
        if(kind==2)instructions.Add(new(2,OpCode.Move,address,new Immediate(0)));
        instructions.Add(new(3,OpCode.Return));
        method.ControlFlowGraph=new ISILControlFlowGraph(instructions);
        MetadataResolver.ResolveFieldOffsets(method);
        if(kind==0) Assert.That(((FieldReference)load.Operands[1]).Field,Is.SameAs(field));
        else Assert.That(load.Operands[1],Is.EqualTo(original));
    }

    [Test]
    public void AddressAliasUsesConcreteNewobjTypeWhenLocalIsErasedObject()
    {
        var app=Cpp2IlApi.CurrentAppContext!;
        var owner=new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],"Tests","Closure",app.SystemTypes.SystemObjectType,TypeAttributes.Public);
        var field=new InjectedFieldAnalysisContext("id",app.SystemTypes.SystemStringType,FieldAttributes.Public,owner,16);
        owner.Fields.Add(field);
        var method=new InjectedMethodAnalysisContext(owner,"Store",app.SystemTypes.SystemVoidType,MethodAttributes.Static,[]);
        var closure=new LocalVariable("closure",new Register(null,"closure"),app.SystemTypes.SystemObjectType);
        var alias=new LocalVariable("alias",new Register(null,"alias"),app.SystemTypes.SystemObjectType);
        var address=new LocalVariable("address",new Register(null,"address"));
        var value=new LocalVariable("value",new Register(null,"value"),app.SystemTypes.SystemStringType);
        var store=new Instruction(2,OpCode.Move,new MemoryOperand(address),value);
        method.ControlFlowGraph=new ISILControlFlowGraph([
            new(0,OpCode.Newobj,closure,owner),
            new(1,OpCode.Move,alias,closure),
            new(2,OpCode.Add,address,alias,new Immediate(16)),
            store,
            new(4,OpCode.Return)]);

        MetadataResolver.ResolveFieldOffsets(method);

        Assert.That(store.Operands[0],Is.TypeOf<FieldReference>());
        Assert.That(((FieldReference)store.Operands[0]).Field,Is.SameAs(field));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void VirtualTailCallIsResolvedWithoutUsingStaleReturnOperand(bool isVoid)
    {
        var app=Cpp2IlApi.CurrentAppContext!;
        var type=isVoid ? app.AssembliesByName["mscorlib"].GetTypeByFullName("System.IO.TextWriter")! : app.SystemTypes.SystemObjectType;
        var target=type.Methods.Find(m=>isVoid ? m.Name=="Write" && m.Parameters.Count==1 && m.Parameters[0].ParameterType.FullName=="System.String" : m.Name=="ToString")!;
        var method=new InjectedMethodAnalysisContext(type,"VirtualTail",target.ReturnType,MethodAttributes.Static,[]);
        var klass=new LocalVariable("klass",new Register(null,"klass"),new RuntimeClassTypeAnalysisContext(type,type.DeclaringAssembly));
        var receiver=new LocalVariable("receiver",new Register(null,"receiver"),type);
        var pointer=new LocalVariable("pointer",new Register(null,"pointer"));
        var stale=new LocalVariable("stale",new Register(null,"stale"));
        var offset=(app.Binary.PointerSizeBytes==8?0x138:0xc0)+target.Definition!.slot*2*app.Binary.PointerSizeBytes;
        var text=new StringLiteral("status");
        var dispatch=isVoid ? new Instruction(1,OpCode.IndirectJump,pointer,stale,receiver,text) : new Instruction(1,OpCode.IndirectJump,pointer,stale,receiver);
        method.ControlFlowGraph=new ISILControlFlowGraph([new(0,OpCode.Move,pointer,new MemoryOperand(klass,addend:offset)),dispatch]);
        Assert.That(MetadataResolver.ResolveVirtualCalls(method),Is.True);
        Assert.That(dispatch.OpCode,Is.EqualTo(isVoid?OpCode.CallVoid:OpCode.Call));
        Assert.That(dispatch.Operands[1],Is.Not.SameAs(stale));
        if(isVoid) Assert.That(dispatch.Operands[1],Is.SameAs(receiver));
        if(isVoid) Assert.That(dispatch.Operands[2],Is.EqualTo(text));
        Assert.That(method.ControlFlowGraph.Instructions[^1].OpCode,Is.EqualTo(OpCode.Return));
        Assert.That(method.ControlFlowGraph.Instructions[^1].Operands.Count,Is.EqualTo(isVoid?0:1));
    }
}
