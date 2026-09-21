using System;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R=System.Reflection;

namespace Cpp2IL.Core.Tests;

public class StringConstructionTests
{
    [SetUp] public void Setup(){Cpp2IlApi.ResetInternalState();TestGameLoader.LoadSimple2019Game();}
    private sealed class NativeMethod(TypeAnalysisContext type,string name,TypeAnalysisContext result,R.MethodAttributes attributes,ulong address)
        :InjectedMethodAnalysisContext(type,name,result,attributes,[type.AppContext.SystemTypes.SystemCharType,type.AppContext.SystemTypes.SystemInt32Type])
    {public override ulong UnderlyingPointer=>address;}

    [TestCase(0,0)]
    [TestCase(3,0)]
    [TestCase(-1,0)]
    [TestCase(3,1)] // Non-null pseudo-receiver.
    [TestCase(3,2)] // Incorrect argument shuffle.
    [TestCase(3,3)] // Wrong branch target.
    [TestCase(3,4)] // Public constructor is absent.
    [TestCase(3,5)] // Extra native instruction.
    [TestCase(3,6)] // Virtual dispatch is not this allocation shim.
    public void ProvenStringFactorySerializesAndExecutesPublicConstructor(int count,int kind)
    {
        var app=Cpp2IlApi.CurrentAppContext!;app.InstructionSet=new NewArmV8InstructionSet();var str=app.SystemTypes.SystemStringType;
        str.Methods.Clear();
        var factory=new NativeMethod(str,"CreateString",str,R.MethodAttributes.Private,0x1000){RawBytes=new BinarySlice([0xe0,0x03,0x01,0x2a,0xe1,0x03,0x02,0x2a,0xfe,0x03,0x00,0x14])};
        var runtime=new NativeMethod(str,"Ctor",str,R.MethodAttributes.Private|R.MethodAttributes.Static,0x2000);
        var ctor=new NativeMethod(str,".ctor",app.SystemTypes.SystemVoidType,R.MethodAttributes.Public|R.MethodAttributes.SpecialName|R.MethodAttributes.RTSpecialName,0x3000);
        str.Methods.AddRange([factory,runtime,ctor]);
        var result=new LocalVariable("result",new Register(null,"result"));
        var caller=new InjectedMethodAnalysisContext(str,"Run",str,R.MethodAttributes.Static,[]){Locals=[result],ParameterLocals=[],AnalysisWarnings=[]};
        var call=new Instruction(0,OpCode.Call,factory,result,new Immediate(kind==1?1:0),new Immediate(46),new Immediate(count));
        if(kind==2)factory.RawBytes=new BinarySlice([0xe0,0x03,0x02,0x2a,0xe1,0x03,0x02,0x2a,0xfe,0x03,0x00,0x14]);
        if(kind==3)factory.RawBytes=new BinarySlice([0xe0,0x03,0x01,0x2a,0xe1,0x03,0x02,0x2a,0xfd,0x03,0x00,0x14]);
        if(kind==4)str.Methods.Remove(ctor);
        if(kind==5)factory.RawBytes=new BinarySlice(factory.RawBytes.ToArray().Concat(new byte[4]).ToArray());
        if(kind==6)call.IsVirtualDispatch=true;
        if(kind!=0){Assert.That(Cpp2IL.Core.Analysis.StringConstructorRecovery.Resolve(call,factory),Is.Null);return;}
        caller.ControlFlowGraph=new ISILControlFlowGraph([call,new(1,OpCode.Return,result)]);
        var module=new ModuleDefinition("StringFactory.dll",new AssemblyReference("System.Private.CoreLib",typeof(object).Assembly.GetName().Version!));
        var type=new TypeDefinition("Tests","Factory",TypeAttributes.Public,module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(type);
        var stringType=new TypeDefinition("System","String",TypeAttributes.Public);
        var ctorDef=new MethodDefinition(".ctor",MethodAttributes.Public|MethodAttributes.SpecialName|MethodAttributes.RuntimeSpecialName,MethodSignature.CreateInstance(module.CorLibTypeFactory.Void,[module.CorLibTypeFactory.Char,module.CorLibTypeFactory.Int32]));stringType.Methods.Add(ctorDef);ctor.PutExtraData("AsmResolverMethod",ctorDef);
        var factoryDef=new MethodDefinition("CreateString",MethodAttributes.Private,MethodSignature.CreateInstance(module.CorLibTypeFactory.String,[module.CorLibTypeFactory.Char,module.CorLibTypeFactory.Int32]));stringType.Methods.Add(factoryDef);factory.PutExtraData("AsmResolverMethod",factoryDef);
        var method=new MethodDefinition("Run",MethodAttributes.Public|MethodAttributes.Static,MethodSignature.CreateStatic(module.CorLibTypeFactory.String));type.Methods.Add(method);
        IlGenerator.GenerateIl(caller,method);
        Assert.That(method.CilMethodBody!.Instructions.Count(i=>i.OpCode==CilOpCodes.Newobj),Is.EqualTo(1));
        foreach(var i in method.CilMethodBody.Instructions.Where(i=>ReferenceEquals(i.Operand,ctorDef)))i.Operand=module.DefaultImporter.ImportMethod(typeof(string).GetConstructor([typeof(char),typeof(int)])!);
        var assembly=new AssemblyDefinition("StringFactory",new Version(1,0));assembly.Modules.Add(module);
        using var stream=new System.IO.MemoryStream();module.Write(stream);
        var run=R.Assembly.Load(stream.ToArray()).GetType("Tests.Factory")!.GetMethod("Run")!;
        if(count<0)Assert.That(Assert.Throws<R.TargetInvocationException>(()=>run.Invoke(null,null))!.InnerException,Is.TypeOf<ArgumentOutOfRangeException>());
        else Assert.That(run.Invoke(null,null),Is.EqualTo(new string('.',count)));
    }
}
