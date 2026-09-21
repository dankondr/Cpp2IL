using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class ReferenceCompareExchangeTests
{
    [TestCase(-1, true)]
    [TestCase(0, false)] // unknown prologue
    [TestCase(8, false)] // incorrect argument shuffle
    [TestCase(32, false)] // no memory fence
    [TestCase(52, false)] // incorrect return register
    [TestCase(64, false)] // wrong CAS width
    [TestCase(65, false)] // ordinary load rather than acquire exclusive
    [TestCase(66, false)] // ordinary store rather than release exclusive
    [TestCase(67, false)] // retry target mismatch
    [TestCase(68, false)] // no known reference barrier
    public void RequiresCompleteReferenceCasHelperProof(int mutation, bool expected)
    {
        var words = new Dictionary<ulong, uint>();
        uint[] wrapper = [0xf81e0ffe,0xa9014ff4,0xaa0003f4,0xaa0203f3,0xaa0203e0,0xaa1403e2,
            0x940003fa,0xeb13001f,0xd5033bbf,0x9a800273,0xaa1403e0,0x940007f5,
            0xaa1303e0,0xa9414ff4,0xf84207fe,0xd65f03c0];
        uint[] kernel = [0xd503245f,0x90000010,0x39428210,0x34000070,0xc8e0fc41,0xd65f03c0,
            0xaa0003f0,0xc85ffc40,0xeb10001f,0x54000061,0xc811fc41,0x35ffff91,0xd65f03c0];
        for (var i=0;i<wrapper.Length;i++) words[0x1000UL+(ulong)i*4]=wrapper[i];
        for (var i=0;i<kernel.Length;i++) words[0x2000UL+(ulong)i*4]=kernel[i];
        if (mutation is >=0 and <64) words[0x1000UL+(ulong)mutation]=0xd503201f;
        if (mutation==64) words[0x2010]=0x88e0fc41; // CASAL W, not X
        if (mutation==65) words[0x201c]=0xf9400040;
        if (mutation==66) words[0x2028]=0xf9000041;
        if (mutation==67) words[0x202c]=0x35ffffb1;
        Assert.That(ReferenceCompareExchangeRecovery.MatchesHelper(0x1000,a=>words[a],a=>mutation!=68 && a==0x3000),Is.EqualTo(expected));
    }
}

public class ReferenceCasFieldTests
{
    [SetUp] public void Setup() { Cpp2IlApi.ResetInternalState(); TestGameLoader.LoadSimple2019Game(); }

    [TestCase("nullable", true)]
    [TestCase("nullable-prefix", true)]
    [TestCase("nonnull", true)]
    [TestCase("extra-entry", false)]
    [TestCase("inverted-null", false)]
    [TestCase("wrong-type", false)]
    [TestCase("side-effect", false)]
    [TestCase("wrong-throw", false)]
    public void ReferenceCastRequiresExactNativeTypeGuard(string mutation, bool expected)
    {
        var app=Cpp2IlApi.CurrentAppContext!;var type=app.SystemTypes.SystemStringType;
        var value=new LocalVariable("value",new Register(null,"value"),app.SystemTypes.SystemObjectType);
        var nullCondition=new LocalVariable("null",new Register(null,"null"));var classCondition=new LocalVariable("class",new Register(null,"class"));
        var use=new Block();var nullGuard=new Block();var classGuard=new Block();var failure=new Block();
        nullGuard.Instructions=[new(0,mutation=="inverted-null"?OpCode.CheckNotEqual:OpCode.CheckEqual,nullCondition,value,new Immediate(0)),new(1,OpCode.ConditionalJump,mutation=="nonnull"?new Block():use,nullCondition)];
        if(mutation=="nullable-prefix")nullGuard.Instructions.Insert(0,new(-1,OpCode.Call,new Immediate(0x3000),value));
        classGuard.Instructions=[new(2,OpCode.CheckNotEqual,classCondition,new MemoryOperand(value),mutation=="wrong-type"?app.SystemTypes.SystemObjectType:type),new(3,OpCode.ConditionalJump,failure,classCondition)];
        if(mutation=="side-effect")classGuard.Instructions.Insert(1,new(4,OpCode.CallVoid,new Immediate(0x3000)));
        failure.Instructions=[new(5,OpCode.Throw,app.AssembliesByName["mscorlib"].GetTypeByFullName(mutation=="wrong-throw"?"System.NullReferenceException":"System.InvalidCastException")!)];
        classGuard.Predecessors=[nullGuard];classGuard.Successors=[use,failure];use.Predecessors=[classGuard];failure.Predecessors=[classGuard];
        if(mutation!="nonnull"){nullGuard.Successors=[use,classGuard];use.Predecessors.Insert(0,nullGuard);}
        else nullGuard.Successors=[classGuard];
        if(mutation=="extra-entry")use.Predecessors.Add(new Block());
        Assert.That(ReferenceCastRecovery.HasExactTypeGuard(use,value,type),Is.EqualTo(expected));
    }

    [TestCase(false)]
    [TestCase(true)]
    public void EmittedFieldAddressIsARealManagedReference(bool isStatic)
    {
        var app=Cpp2IlApi.CurrentAppContext!;
        var owner=app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Exception")!;
        var field=owner.Fields.First(f=>!f.IsStatic&&f.FieldType.FullName=="System.String");
        field.Attributes=FieldAttributes.Public|(isStatic?FieldAttributes.Static:0);
        var receiver=new LocalVariable("receiver",new Register(null,"receiver"),owner);
        var caller=new InjectedMethodAnalysisContext(owner,"Address",new ByRefTypeAnalysisContext(field.FieldType),MethodAttributes.Static,[owner]){
            ControlFlowGraph=new ISILControlFlowGraph([new(0,OpCode.Return,new AddressOf(new FieldReference(field,receiver,field.Offset)))]),
            Locals=[receiver],ParameterLocals=[receiver],AnalysisWarnings=[]};
        var module=new AsmResolver.DotNet.ModuleDefinition("FieldAddress.dll",new AsmResolver.DotNet.AssemblyReference("System.Private.CoreLib",typeof(object).Assembly.GetName().Version!));
        var type=new AsmResolver.DotNet.TypeDefinition("Fixture","Owner",AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(type);owner.PutExtraData("AsmResolverType",type);
        var fd=new AsmResolver.DotNet.FieldDefinition("Value",AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public|(isStatic?AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Static:0),new AsmResolver.DotNet.Signatures.FieldSignature(module.CorLibTypeFactory.String));type.Fields.Add(fd);field.PutExtraData("AsmResolverField",fd);
        var md=new AsmResolver.DotNet.MethodDefinition("Address",AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public|AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            AsmResolver.DotNet.Signatures.MethodSignature.CreateStatic(module.CorLibTypeFactory.String.MakeByReferenceType(),[type.ToTypeSignature()]));type.Methods.Add(md);
        md.ParameterDefinitions.Add(new AsmResolver.DotNet.ParameterDefinition(1,"receiver",0));
        IlGenerator.GenerateIl(caller,md);
        Assert.That(md.CilMethodBody!.Instructions.Any(i=>i.OpCode==(isStatic?AsmResolver.PE.DotNet.Cil.CilOpCodes.Ldsflda:AsmResolver.PE.DotNet.Cil.CilOpCodes.Ldflda)),Is.True);
        var assembly=new AsmResolver.DotNet.AssemblyDefinition("FieldAddress",new System.Version(1,0));assembly.Modules.Add(module);
        using var stream=new System.IO.MemoryStream();module.Write(stream);
        var loaded=Assembly.Load(stream.ToArray()).GetType("Fixture.Owner")!;
        var instance=System.Runtime.CompilerServices.RuntimeHelpers.GetUninitializedObject(loaded);loaded.GetField("Value")!.SetValue(isStatic?null:instance,"sentinel");
        Assert.That(loaded.GetMethod("Address")!.Invoke(null,[instance]),Is.EqualTo("sentinel"));
    }

    [TestCase("reference", true)]
    [TestCase("int", false)]
    [TestCase("pointer", false)]
    [TestCase("generic", false)]
    [TestCase("ordinary-call", false)]
    [TestCase("ordinary-store", false)]
    [TestCase("unknown-owner", false)]
    [TestCase("interior-offset", false)]
    [TestCase("multiple-definitions", false)]
    public void OnlyProvenHelperWithExactNamedReferenceFieldGetsManagedAtomicCall(string kind, bool expected)
    {
        var app=Cpp2IlApi.CurrentAppContext!;
        var owner=app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Exception")!;
        var field=owner.Fields.First(f=>!f.IsStatic && f.FieldType.FullName=="System.String");
        if(kind=="int")field.FieldType=app.SystemTypes.SystemInt32Type;
        if(kind=="pointer")field.FieldType=new PointerTypeAnalysisContext(app.SystemTypes.SystemObjectType);
        if(kind=="generic")field.FieldType=new GenericParameterTypeAnalysisContext("T",0,LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_VAR,0,owner);
        var receiver=new LocalVariable("receiver",new Register(null,"receiver"),kind=="unknown-owner"?null:owner);
        var address=new LocalVariable("address",new Register(null,"address"));
        var result=new LocalVariable("result",new Register(null,"result"));
        var call=new Instruction(1,OpCode.Call,new Immediate(0x1000),result,address,new Immediate(0),new Immediate(0),new Immediate(99));
        if(kind=="ordinary-store")call=new Instruction(1,OpCode.Move,new MemoryOperand(address),new Immediate(0));
        var body=new List<Instruction>{new(0,OpCode.Add,address,receiver,new Immediate(field.Offset+(kind=="interior-offset"?1:0))),call,new(2,OpCode.Return)};
        if(kind=="multiple-definitions")body.Insert(1,new(3,OpCode.Move,address,new Immediate(0)));
        var method=new InjectedMethodAnalysisContext(owner,"Cas",app.SystemTypes.SystemVoidType,MethodAttributes.Static,[]){ControlFlowGraph=new ISILControlFlowGraph(body)};
        ReferenceCompareExchangeRecovery.ResolveCalls(method,t=>kind!="ordinary-call" && t==0x1000);
        Assert.That(call.Operands[0] is ConcreteGenericMethodAnalysisContext,Is.EqualTo(expected));
        if(!expected)return;
        Assert.That(call.Operands.Count,Is.EqualTo(5));
        Assert.That(((FieldReference)((AddressOf)call.Operands[2]).Target).Field,Is.SameAs(field));
        Assert.That(result.Type,Is.SameAs(field.FieldType));
        Assert.That(((ConcreteGenericMethodAnalysisContext)call.Operands[0]).MethodGenericParameters[0],Is.SameAs(field.FieldType));
    }
}
