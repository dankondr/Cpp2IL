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

    [TestCase(0)] // Two logical inversions ending at a branch.
    [TestCase(1)] // Copy escape must not seed types backwards.
    [TestCase(2)] // Arithmetic escape is not a guard.
    [TestCase(3)] // A cycle is not proof of a control-flow-only result.
    [TestCase(4)] // Known incompatible downstream type must remain untouched.
    [TestCase(5)] // An unused chain does not prove a control-flow flag.
    public void BooleanNotChainRequiresGuardOnlyUses(int kind)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture", app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        var input = new LocalVariable("input", new Register(null, "input")) { Type = app.SystemTypes.SystemBooleanType };
        var first = new LocalVariable("first", new Register(null, "first"));
        var second = new LocalVariable("second", new Register(null, "second")) { Type = kind == 4 ? app.SystemTypes.SystemObjectType : null };
        var escaped = new LocalVariable("escaped", new Register(null, "escaped"));
        var taken = new Instruction(8, OpCode.Return);
        var instructions = new List<Instruction> { new(0, OpCode.Not, first, input), new(1, OpCode.Not, second, first) };
        if (kind == 1) instructions.Add(new(2, OpCode.Move, escaped, second));
        if (kind == 2) instructions.Add(new(2, OpCode.Add, escaped, second, new Immediate(1)));
        if (kind == 3) instructions.Add(new(2, OpCode.Not, first, second));
        if (kind != 5) instructions.Add(new(3, OpCode.ConditionalJump, taken, second));
        instructions.Add(new(4, OpCode.Return)); instructions.Add(taken);
        method.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        method.Locals = [input, first, second, escaped]; method.ParameterLocals = [];
        LocalVariables.ResolveTypesAndFields(method);
        if (kind == 0) Assert.Multiple(() => { Assert.That(first.Type, Is.SameAs(app.SystemTypes.SystemBooleanType)); Assert.That(second.Type, Is.SameAs(app.SystemTypes.SystemBooleanType)); });
        else Assert.That(first.Type, Is.Null);
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

    [Test]
    public void IntegerProducerStaysTypedThroughBitwiseConsumer()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture", app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        var input = new LocalVariable("input", new Register(null, "input")) { Type = app.SystemTypes.SystemInt32Type };
        var sum = new LocalVariable("sum", new Register(null, "sum"));
        var masked = new LocalVariable("masked", new Register(null, "masked"));
        var flag = new LocalVariable("flag", new Register(null, "flag"));
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Add, sum, input, new Immediate(1)),
            new(1, OpCode.And, masked, sum, new Immediate(1)),
            new(2, OpCode.CheckEqual, flag, masked, new Immediate(0)),
            new(3, OpCode.Return)]);
        method.Locals = [input, sum, masked, flag];
        method.ParameterLocals = [];
        LocalVariables.ResolveTypesAndFields(method);
        Assert.That(sum.Type, Is.SameAs(app.SystemTypes.SystemInt32Type));
        Assert.That(masked.Type, Is.SameAs(app.SystemTypes.SystemInt32Type));
    }

    [Test]
    public void BitwiseResultPrefersWideImmediateOverInt32Producer()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture", app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        var input = new LocalVariable("input", new Register(null, "input")) { Type = app.SystemTypes.SystemInt32Type };
        var result = new LocalVariable("result", new Register(null, "result"));
        var flag = new LocalVariable("flag", new Register(null, "flag"));
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.And, result, input, new Immediate(0x1_0000_0000L)),
            new(1, OpCode.CheckEqual, flag, result, new Immediate(0)),
            new(2, OpCode.Return)]);
        method.Locals = [input, result, flag];
        method.ParameterLocals = [];

        LocalVariables.ResolveTypesAndFields(method);

        Assert.That(result.Type, Is.SameAs(app.SystemTypes.SystemInt64Type));
    }

    [Test]
    public void BitwiseResultDoesNotWidenForInt32Immediate()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture", app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        var input = new LocalVariable("input", new Register(null, "input")) { Type = app.SystemTypes.SystemInt32Type };
        var result = new LocalVariable("result", new Register(null, "result"));
        var flag = new LocalVariable("flag", new Register(null, "flag"));
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.And, result, input, new Immediate(0xFFFF_FFFFL)),
            new(1, OpCode.CheckEqual, flag, result, new Immediate(0)),
            new(2, OpCode.Return)]);
        method.Locals = [input, result, flag];
        method.ParameterLocals = [];

        LocalVariables.ResolveTypesAndFields(method);

        Assert.That(result.Type, Is.SameAs(app.SystemTypes.SystemInt32Type));
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

    [Test]
    public void ArrayLengthProducerIsInt32OnlyForRecoveredArrays()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var method = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Fixture", app.SystemTypes.SystemVoidType, MethodAttributes.Static, []);
        var array = new LocalVariable("array", new Register(null, "array"))
        {
            Type = new SzArrayTypeAnalysisContext(app.SystemTypes.SystemObjectType)
        };
        var length = new LocalVariable("length", new Register(null, "length"));
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, length, new ArrayLength(array)),
            new(1, OpCode.Return)]);
        method.Locals = [array, length];
        method.ParameterLocals = [];

        LocalVariables.ResolveTypesAndFields(method);

        Assert.That(length.Type, Is.SameAs(app.SystemTypes.SystemInt32Type));

        var pointer = new LocalVariable("pointer", new Register(null, "pointer"))
        {
            Type = new PointerTypeAnalysisContext(app.SystemTypes.SystemObjectType)
        };
        var pointerLength = new LocalVariable("pointerLength", new Register(null, "pointerLength"));
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, pointerLength, new ArrayLength(pointer)),
            new(1, OpCode.Return)]);
        method.Locals = [pointer, pointerLength];
        method.ParameterLocals = [];

        LocalVariables.ResolveTypesAndFields(method);

        Assert.That(pointerLength.Type, Is.Null);

        var reference = new LocalVariable("reference", new Register(null, "reference"))
        {
            Type = app.SystemTypes.SystemObjectType
        };
        var referenceLength = new LocalVariable("referenceLength", new Register(null, "referenceLength"));
        method.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, referenceLength, new ArrayLength(reference)),
            new(1, OpCode.Return)]);
        method.Locals = [reference, referenceLength];

        LocalVariables.ResolveTypesAndFields(method);

        Assert.That(referenceLength.Type, Is.Null);
    }
}
