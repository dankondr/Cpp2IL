using System.Reflection;
using System.Collections.Generic;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Tests.Analysis;

public class IntegerArithmeticTypeTests
{
    [SetUp] public void Setup() { Cpp2IlApi.ResetInternalState(); TestGameLoader.LoadSimple2019Game(); }

    [Test]
    public void BooleanNotResultRetainsBooleanType()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture", app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        var input = new LocalVariable("input", new Register(null, "input")) { Type = app.SystemTypes.SystemBooleanType };
        var result = new LocalVariable("result", new Register(null, "result"));
        var taken = new Instruction(3, OpCode.Return);
        method.ControlFlowGraph = new ISILControlFlowGraph([new(0, OpCode.Not, result, input), new(1, OpCode.ConditionalJump, taken, result), new(2, OpCode.Return), taken]);
        method.Locals = [input, result];
        method.ParameterLocals = [];
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(result.Type, Is.SameAs(app.SystemTypes.SystemBooleanType));
    }

    [TestCase(0)] // An object is not a boolean flag.
    [TestCase(1)] // An unknown input stays unknown.
    [TestCase(2)] // Numeric bitwise Not preserves the existing numeric contract.
    [TestCase(3)] // Boolean negation is not numeric Negate.
    [TestCase(4)] // Do not seed a result that can propagate backwards through a copy/phi.
    public void BooleanNotInferenceDoesNotGuessOtherOperands(int kind)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture", app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        var input = new LocalVariable("input", new Register(null, "input")) { Type = kind switch { 0 => app.SystemTypes.SystemObjectType, 2 => app.SystemTypes.SystemInt32Type, 3 or 4 => app.SystemTypes.SystemBooleanType, _ => null } };
        var result = new LocalVariable("result", new Register(null, "result"));
        var instructions = new List<Instruction> { new(0, kind == 3 ? OpCode.Negate : OpCode.Not, result, input) };
        if (kind == 4) instructions.Add(new(1, OpCode.Move, new LocalVariable("copy", new Register(null, "copy")), result));
        instructions.Add(new(2, OpCode.Return));
        method.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        method.Locals = [input, result];
        method.ParameterLocals = [];
        LocalVariables.ResolveTypesAndFields(method);
        if (kind == 2) Assert.That(result.Type, Is.SameAs(app.SystemTypes.SystemInt32Type));
        else Assert.That(result.Type, Is.Null);
    }

    [TestCase(OpCode.Add)]
    [TestCase(OpCode.Subtract)]
    [TestCase(OpCode.Multiply)]
    public void TypedInt32AndImmediateHaveInt32Result(OpCode opcode)
    {
        var app=Cpp2IlApi.CurrentAppContext!;
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Fixture",app.SystemTypes.SystemVoidType,MethodAttributes.Static,[]);
        var input=new LocalVariable("input",new Register(null,"input")){Type=app.SystemTypes.SystemInt32Type};
        var result=new LocalVariable("result",new Register(null,"result"));
        var flag=new LocalVariable("flag",new Register(null,"flag"));
        method.ControlFlowGraph=new ISILControlFlowGraph([new(0,opcode,result,input,new Immediate(1)),new(1,OpCode.CheckEqual,flag,result,new Immediate(0)),new(2,OpCode.Return)]);
        method.Locals=[input,result];method.ParameterLocals=[];
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(result.Type,Is.SameAs(app.SystemTypes.SystemInt32Type));
    }

    [TestCase(0)] // Reference arithmetic is not numeric evidence.
    [TestCase(1)] // Mixed I4/I8 widths are not silently coerced.
    [TestCase(2)] // An oversized immediate must not imply I4 truncation.
    [TestCase(3)] // A comparison result also used as an address is not numeric evidence.
    public void UnknownOrIncompatibleArithmeticStaysUnknown(int kind)
    {
        var app=Cpp2IlApi.CurrentAppContext!;
        var method=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Fixture",app.SystemTypes.SystemVoidType,MethodAttributes.Static,[]);
        var input=new LocalVariable("input",new Register(null,"input")){Type=kind==0?app.SystemTypes.SystemObjectType:app.SystemTypes.SystemInt32Type};
        IOperand right=kind==1?new LocalVariable("right",new Register(null,"right")){Type=app.SystemTypes.SystemInt64Type}:new Immediate(kind==2?0x100000000L:1);
        var result=new LocalVariable("result",new Register(null,"result"));
        var flag=new LocalVariable("flag",new Register(null,"flag"));
        var instructions=new List<Instruction>{new(0,OpCode.Add,result,input,right),new(1,OpCode.CheckEqual,flag,result,new Immediate(0))};
        if(kind==3) instructions.Add(new(2,OpCode.Move,flag,new MemoryOperand(result,addend:0x18)));
        instructions.Add(new(3,OpCode.Return));
        method.ControlFlowGraph=new ISILControlFlowGraph(instructions);
        method.Locals=[input,result];method.ParameterLocals=[];
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(result.Type,Is.Null);
    }
}
