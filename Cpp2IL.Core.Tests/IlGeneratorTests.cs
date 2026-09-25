using System;
using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using ReflectionMethodAttributes = System.Reflection.MethodAttributes;

namespace Cpp2IL.Core.Tests;

public class IlGeneratorTests
{
    [Test]
    public void ObjectFallbackLoopIndexUsesArrayLengthInt32Evidence()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var array = new LocalVariable("array", new Register(null, "array"))
            { Type = new SzArrayTypeAnalysisContext(app.SystemTypes.SystemObjectType) };
        var index = new LocalVariable("index", new Register(null, "index"))
            { Type = app.SystemTypes.SystemObjectType };
        var poolSize = new LocalVariable("poolSize", new Register(null, "poolSize"))
            { Type = app.SystemTypes.SystemInt32Type };
        var next = new LocalVariable("next", new Register(null, "next"));
        var flag = new LocalVariable("flag", new Register(null, "flag"))
            { Type = app.SystemTypes.SystemBooleanType };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.NewArr, array, array.Type!, poolSize),
            new(1, OpCode.CheckLess, flag, index, new ArrayLength(array)),
            new(2, OpCode.CheckNotEqual, flag, poolSize, index),
            new(3, OpCode.Add, next, index, new Immediate(1)),
            new(4, OpCode.Return)]);
        context.Locals = [array, index, poolSize, next, flag];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("NumericLoop.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemBooleanType);
        var type = new TypeDefinition("Tests", "NumericLoop", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        Assert.That(method.CilMethodBody!.LocalVariables.Count(local =>
            local.VariableType.FullName == "System.Int32"), Is.GreaterThanOrEqualTo(2));
    }

    [Test]
    public void ObjectFallbackArrayElementUsesElementType()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var arrayType = new SzArrayTypeAnalysisContext(app.SystemTypes.SystemStringType);
        var array = new LocalVariable("array", new Register(null, "array")) { Type = arrayType };
        var value = new LocalVariable("value", new Register(null, "value"))
            { Type = app.SystemTypes.SystemObjectType };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read",
            app.SystemTypes.SystemStringType, ReflectionMethodAttributes.Static, [arrayType]);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, value, new ArrayAccess(array, new Immediate(0))),
            new(1, OpCode.Return, value)]);
        context.Locals = [array, value];
        context.ParameterLocals = [array];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("ArrayElementType.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemStringType, app.SystemTypes.SystemVoidType);
        var type = new TypeDefinition("Tests", "ArrayElementType", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Read", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.String,
                [module.CorLibTypeFactory.String.MakeSzArrayType()]));
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "array", 0));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        Assert.That(method.CilMethodBody!.LocalVariables.Any(local =>
            local.VariableType.FullName == "System.String"), Is.True);
    }

    [Test]
    public void OpenGenericCallIsInstantiatedFromResultContract()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var activator = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Activator")!;
        var createInstance = activator.Methods.Single(method =>
            method.Name == "CreateInstance" && method.GenericParameters.Count == 1
            && method.Parameters.Count == 0);
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemStringType };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Call, createInstance, result),
            new(1, OpCode.Return)]);
        context.Locals = [result];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("OpenGenericCall.dll");
        SeedCorLibTypes(app, module, activator, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemStringType, app.SystemTypes.SystemVoidType);
        var type = new TypeDefinition("Tests", "OpenGenericCall", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        Assert.That(method.CilMethodBody!.Instructions.Any(instruction =>
            instruction.OpCode == CilOpCodes.Call
            && instruction.Operand?.ToString()?.Contains("CreateInstance<System.String>") == true), Is.True,
            () => string.Join("\n", method.CilMethodBody.Instructions));
    }

    [Test]
    public void GenericCallResultIsInferredFromConcreteArgument()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var interlocked = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Threading.Interlocked")!;
        var compareExchange = interlocked.Methods.Single(candidate => candidate.Name == "CompareExchange"
            && candidate.GenericParameters.Count == 1 && candidate.Parameters.Count == 3);
        var listDefinition = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var concreteList = new GenericInstanceTypeAnalysisContext(listDefinition, [app.SystemTypes.SystemStringType]);
        var input = new LocalVariable("input", new Register(null, "input"))
            { Type = concreteList };
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemObjectType };
        var size = new LocalVariable("size", new Register(null, "size"))
            { Type = app.SystemTypes.SystemInt32Type };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, input, new Immediate(0)),
            new(1, OpCode.Call, compareExchange, result, new AddressOf(input), input, input),
            new(2, OpCode.Move, size, new MemoryOperand(result, addend: 0x18, accessSize: 4)),
            new(3, OpCode.Return)]);
        context.Locals = [input, result, size];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("ArgumentGenericCall.dll");
        SeedCorLibTypes(app, module, interlocked, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemStringType, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemVoidType);
        module.TopLevelTypes.Add(SeedGenericListDefinition(listDefinition));
        var type = new TypeDefinition("Tests", "ArgumentGenericCall", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        Assert.Multiple(() =>
        {
            Assert.That(method.CilMethodBody!.LocalVariables.Count(local =>
                local.VariableType.FullName.Contains("List`1<System.String>")), Is.EqualTo(2));
            Assert.That(method.CilMethodBody.Instructions.Any(instruction =>
                instruction.OpCode == CilOpCodes.Call
                && instruction.Operand?.ToString()?.Contains("CompareExchange<System.Collections.Generic.List`1<System.String>>") == true), Is.True);
            Assert.That(method.CilMethodBody.Instructions.Any(instruction =>
                instruction.OpCode == CilOpCodes.Call
                && instruction.Operand?.ToString()?.Contains("get_Count") == true), Is.True,
                () => string.Join("\n", method.CilMethodBody.Instructions));
        });
    }

    [Test]
    public void ErasedGenericCallReturnSharpensObjectLocalFromReceiver()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var listDefinition = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var getItem = listDefinition.Methods.Single(candidate => candidate.Name == "get_Item"
            && !candidate.IsStatic && candidate.Parameters.Count == 1);
        var listType = new GenericInstanceTypeAnalysisContext(listDefinition, [app.SystemTypes.SystemStringType]);
        var erasedGetItem = new ConcreteGenericMethodAnalysisContext(getItem,
            [app.SystemTypes.SystemObjectType], []);
        var list = new LocalVariable("list", new Register(null, "list")) { Type = listType };
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemObjectType };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Call, erasedGetItem, result, list, new Immediate(0)),
            new(1, OpCode.Return)]);
        context.Locals = [list, result];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("ConcreteCallReturn.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemStringType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType);
        module.TopLevelTypes.Add(SeedGenericListDefinition(listDefinition));
        var type = new TypeDefinition("Tests", "ConcreteCallReturn", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Read", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        Assert.That(method.CilMethodBody!.LocalVariables.Any(local =>
            local.VariableType.FullName == "System.String"), Is.True);
    }

    [Test]
    public void ExceptionValueReturnedFromNonExceptionMethodIsThrown()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var exceptionType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.NullReferenceException")!;
        var exception = new LocalVariable("exception", new Register(null, "exception")) { Type = exceptionType };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemInt32Type, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, exception, new Immediate(0)),
            new(1, OpCode.Return, exception)]);
        context.Locals = [exception];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        var module = new ModuleDefinition("ExceptionReturn.dll");
        exceptionType.PutExtraData("AsmResolverType", new TypeDefinition("System", "NullReferenceException",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type));
        var type = new TypeDefinition("Tests", "ExceptionReturn", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Throw), Is.True);
        Assert.That(method.CilMethodBody.Instructions[^1].OpCode, Is.EqualTo(CilOpCodes.Throw));
    }

    [TestCase(0, false, OpCode.CheckEqual, true)]
    [TestCase(0, true, OpCode.CheckNotEqual, true)]
    [TestCase(0, true, OpCode.CheckEqual, true)]
    [TestCase(0, false, OpCode.CheckNotEqual, true)]
    [TestCase(6, false, OpCode.CheckEqual, true)]
    [TestCase(7, false, OpCode.CheckEqual, true)]
    [TestCase(8, false, OpCode.CheckEqual, true)]
    [TestCase(9, false, OpCode.CheckEqual, false)]
    // An unconstrained T tested against zero is the canonical `box T; ldnull; ceq`
    // null check - a reference comparison, so ldnull is emitted.
    [TestCase(10, false, OpCode.CheckEqual, true)]
    [TestCase(11, false, OpCode.CheckEqual, true)]
    [TestCase(1, false, OpCode.CheckEqual, false)]
    [TestCase(2, false, OpCode.CheckEqual, false)]
    [TestCase(3, false, OpCode.CheckEqual, false)]
    [TestCase(4, false, OpCode.CheckEqual, false)]
    [TestCase(5, false, OpCode.CheckEqual, false)]
    [TestCase(0, false, OpCode.Add, false)]
    public void OnlyReferenceEqualityWithLiteralZeroEmitsNull(int kind, bool reverse, OpCode opcode, bool expectsNull)
    {
        var app=Cpp2IlApi.CurrentAppContext!;
        TypeAnalysisContext? operandType=kind switch {1=>app.SystemTypes.SystemInt32Type,2=>app.SystemTypes.SystemBooleanType,3=>new PointerTypeAnalysisContext(app.SystemTypes.SystemInt32Type),11=>null,_=>app.SystemTypes.SystemObjectType};
        var list=app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        if(kind==6)operandType=app.SystemTypes.SystemStringType;
        if(kind==7)operandType=new SzArrayTypeAnalysisContext(app.SystemTypes.SystemObjectType);
        if(kind==8)operandType=new GenericInstanceTypeAnalysisContext(list,[app.SystemTypes.SystemObjectType]);
        if(kind==9)operandType=new ByRefTypeAnalysisContext(app.SystemTypes.SystemObjectType);
        if(kind==10)operandType=list.GenericParameters[0];
        var input=new LocalVariable("input",new Register(null,"input")){Type=operandType};
        var result=new LocalVariable("result",new Register(null,"result")){Type=app.SystemTypes.SystemBooleanType};
        IOperand right=kind==5?new LocalVariable("numeric",new Register(null,"numeric")){Type=app.SystemTypes.SystemInt32Type}:new Immediate(kind==4?1:0);
        var context=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Run",app.SystemTypes.SystemVoidType,ReflectionMethodAttributes.Static,[]);
        context.ControlFlowGraph=new ISILControlFlowGraph([new(0,opcode,result,reverse?right:input,reverse?input:right),new(1,OpCode.Return)]);
        context.Locals=kind==5?[input,result,(LocalVariable)right]:[input,result];context.ParameterLocals=[];context.AnalysisWarnings=[];
        var module=new ModuleDefinition("NullComparison.dll");var type=new TypeDefinition("Tests","Comparison",TypeAttributes.Public,module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(type);
        foreach(var primitive in new[]{app.SystemTypes.SystemObjectType,app.SystemTypes.SystemInt32Type,app.SystemTypes.SystemBooleanType,app.SystemTypes.SystemStringType,list})
            primitive.PutExtraData("AsmResolverType",new TypeDefinition("System",primitive.Name,TypeAttributes.Public));
        var method=new MethodDefinition("Run",MethodAttributes.Public|MethodAttributes.Static,MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));type.Methods.Add(method);
        IlGenerator.GenerateIl(context,method);
        Assert.That(method.CilMethodBody!.Instructions.Any(i=>i.OpCode==CilOpCodes.Ldnull),Is.EqualTo(expectsNull));
    }

    [TestCase("System.RuntimeTypeHandle", false)]
    [TestCase("System.IntPtr", true)]
    [TestCase("runtime-class", true)]
    public void TypeTokenMatchesExpectedRuntimeRepresentation(string expectedName, bool expectsHandleValueCall)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var sourceType = app.SystemTypes.SystemStringType;
        var expected = expectedName == "runtime-class"
            ? new RuntimeClassTypeAnalysisContext(sourceType, sourceType.DeclaringAssembly)
            : app.AssembliesByName["mscorlib"].GetTypeByFullName(expectedName)!;
        var result = new LocalVariable("result", new Register(null, "result")) { Type = expected };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, result, sourceType),
            new(1, OpCode.Return)]);
        context.Locals = [result];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("RuntimeTypeHandle.dll");
        var emittedType = expected is RuntimeClassTypeAnalysisContext ? app.SystemTypes.SystemIntPtrType : expected;
        emittedType.PutExtraData("AsmResolverType", new TypeDefinition("System", emittedType.Name,
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType")));
        var sourceDefinition = new TypeDefinition("System", "String", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(sourceDefinition);
        sourceType.PutExtraData("AsmResolverType", sourceDefinition);
        var owner = new TypeDefinition("Tests", "Handles", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldtoken), Is.True);
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldloca), Is.EqualTo(expectsHandleValueCall));
        Assert.That(il.Any(i => i.Operand?.ToString()?.Contains("get_Value") == true), Is.EqualTo(expectsHandleValueCall));
        Assert.That(il.Any(i => i.Operand?.ToString()?.Contains("GetTypeFromHandle") == true), Is.False);
    }

    [Test]
    public void UntypedLocalZeroUsesItsEmittedObjectContract()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var local = new LocalVariable("value", new Register(null, "value"));
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, local, new Immediate(0)),
            new(1, OpCode.Return)]);
        context.Locals = [local];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        var module = new ModuleDefinition("UntypedZero.dll");
        var owner = new TypeDefinition("Tests", "UntypedZero", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.True);
    }

    [Test]
    public void UntypedBooleanNotResultUsesBooleanLocal()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var input = new LocalVariable("input", new Register(null, "input"))
            { Type = app.SystemTypes.SystemBooleanType };
        var result = new LocalVariable("result", new Register(null, "result"));
        var masked = new LocalVariable("masked", new Register(null, "masked"));
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Not, result, input),
            new(1, OpCode.And, masked, new Immediate(1), result),
            new(2, OpCode.Return)]);
        context.Locals = [input, result, masked];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        var module = new ModuleDefinition("BooleanNot.dll");
        app.SystemTypes.SystemBooleanType.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Boolean", TypeAttributes.Public));
        var owner = new TypeDefinition("Tests", "BooleanNot", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        Assert.Multiple(() =>
        {
            Assert.That(method.CilMethodBody!.LocalVariables[1].VariableType.FullName, Is.EqualTo("System.Boolean"));
            Assert.That(method.CilMethodBody.LocalVariables[2].VariableType.FullName, Is.EqualTo("System.Boolean"));
        });
    }

    [Test]
    public void NativePointerImmediateEmitsConversion()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"));
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        var address = new Instruction(0, OpCode.Move, pointer, new Immediate(0x12345000))
        {
            NativeIntegerWidthBits = 64
        };
        context.ControlFlowGraph = new ISILControlFlowGraph([
            address,
            new(1, OpCode.Return)]);
        context.Locals = [pointer];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        var module = new ModuleDefinition("NativePointer.dll");
        app.SystemTypes.SystemIntPtrType.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "IntPtr", TypeAttributes.Public));
        var owner = new TypeDefinition("Tests", "NativePointer", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        Assert.Multiple(() =>
        {
            Assert.That(method.CilMethodBody!.LocalVariables[0].VariableType.FullName, Is.EqualTo("System.IntPtr"));
            Assert.That(method.CilMethodBody.Instructions.Any(i => i.OpCode == CilOpCodes.Conv_I), Is.True);
        });
    }

    [Test]
    public void UnreachableAnalysisWarningDoesNotMakeSerializedBodyUnrunnable()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run", app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([new(0, OpCode.Return)]);
        context.Locals = []; context.ParameterLocals = []; context.AnalysisWarnings = ["fixture warning"];
        var module = new ModuleDefinition("WarningTrailer.dll", new AssemblyReference("System.Private.CoreLib", typeof(object).Assembly.GetName().Version!));
        var type = new TypeDefinition("Tests", "WarningTrailer", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type); module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static, MethodSignature.CreateStatic(module.CorLibTypeFactory.Void)); type.Methods.Add(method);
        IlGenerator.GenerateIl(context, method);
        Assert.That(method.CilMethodBody!.Instructions[0].OpCode, Is.EqualTo(CilOpCodes.Ret));
        Assert.That(method.CilMethodBody.Instructions[^1].OpCode, Is.EqualTo(CilOpCodes.Throw));
        Assert.That(context.AnalysisWarnings, Does.Contain("fixture warning"));
        var assembly = new AssemblyDefinition("WarningTrailer", new Version(1, 0)); assembly.Modules.Add(module);
        using var stream = new System.IO.MemoryStream(); module.Write(stream);
        var callable = System.Reflection.Assembly.Load(stream.ToArray()).GetType("Tests.WarningTrailer")!.GetMethod("Run")!;
        Assert.DoesNotThrow(() => callable.Invoke(null, null));
    }

    [TestCase(0xffffffffL, -1, false, false)]
    [TestCase(0x80000000L, int.MinValue, false, false)]
    [TestCase(0x100000000L, 0, false, false)]
    [TestCase(0xffffffffL, 0, true, false)]
    [TestCase(0xffffffffL, -1, false, true)]
    [TestCase(-1L, -1, false, true)]
    public void Int32CallArgumentUsesTheLowWordNotInt64(long nativeValue,int expected,bool wide,bool unsigned)
    {
        var app=Cpp2IlApi.CurrentAppContext!;
        var target=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Take",app.SystemTypes.SystemInt32Type,ReflectionMethodAttributes.Public|ReflectionMethodAttributes.Static,[wide?app.SystemTypes.SystemInt64Type:unsigned?app.SystemTypes.SystemUInt32Type:app.SystemTypes.SystemInt32Type]);
        var caller=new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType,"Caller",app.SystemTypes.SystemVoidType,ReflectionMethodAttributes.Public|ReflectionMethodAttributes.Static,[]);
        caller.ControlFlowGraph=new ISILControlFlowGraph([new(0,OpCode.CallVoid,target,new Immediate(nativeValue)),new(1,OpCode.Return)]);
        caller.Locals=[];caller.ParameterLocals=[];caller.AnalysisWarnings=[];
        var module=new ModuleDefinition("WidthFixture.dll");
        var type=new TypeDefinition("Tests","Width",TypeAttributes.Public,module.CorLibTypeFactory.Object.Type);module.TopLevelTypes.Add(type);
        var targetDefinition=new MethodDefinition("Take",MethodAttributes.Public|MethodAttributes.Static,MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32,[wide?module.CorLibTypeFactory.Int64:unsigned?module.CorLibTypeFactory.UInt32:module.CorLibTypeFactory.Int32]));type.Methods.Add(targetDefinition);
        target.PutExtraData("AsmResolverMethod",targetDefinition);
        var definition=new MethodDefinition("Caller",MethodAttributes.Public|MethodAttributes.Static,MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));type.Methods.Add(definition);
        IlGenerator.GenerateIl(caller,definition);
        var needsWide=wide||nativeValue>uint.MaxValue;
        Assert.That(definition.CilMethodBody!.Instructions[0].OpCode,Is.EqualTo(needsWide?CilOpCodes.Ldc_I8:CilOpCodes.Ldc_I4));
        if(needsWide)Assert.That(definition.CilMethodBody.Instructions[0].Operand,Is.EqualTo(nativeValue));
        else Assert.That(definition.CilMethodBody.Instructions[0].Operand,Is.EqualTo(expected));
    }

    [Test]
    public void FloatingComparisonConvertsIntegerImmediateToOperandWidth()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var value = new LocalVariable("value", new Register(null, "value")) { Type = app.SystemTypes.SystemDoubleType };
        var result = new LocalVariable("result", new Register(null, "result")) { Type = app.SystemTypes.SystemBooleanType };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, value, new Immediate(0)),
            new(1, OpCode.CheckEqual, result, value, new Immediate(0)),
            new(2, OpCode.Return)]);
        context.Locals = [value, result];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("FloatingComparison.dll");
        var type = new TypeDefinition("Tests", "FloatingComparison", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        app.SystemTypes.SystemDoubleType.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Double", TypeAttributes.Public));
        app.SystemTypes.SystemBooleanType.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Boolean", TypeAttributes.Public));
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        var instructions = method.CilMethodBody!.Instructions;
        // The immediate adapts to the operand width at load time (ldc.r8), so no raw
        // int ever reaches the ceq - the conversion the name promises, just folded.
        Assert.That(instructions.Select(i => i.OpCode), Does.Contain(CilOpCodes.Ldc_R8));
        // The immediate is loaded directly at double width, so no separate
        // conversion is needed; it must not reach ceq as an integer.
        Assert.That(instructions.Select(i => i.OpCode), Does.Not.Contain(CilOpCodes.Ldc_I4));
        Assert.That(instructions.Select(i => i.OpCode), Does.Contain(CilOpCodes.Ceq));
    }

    [Test]
    public void InvalidStackRemainsExplicitlyDiagnosedAndBodyIsPreserved()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Invalid",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([new(0, OpCode.Return)]);
        caller.Locals = [];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("InvalidStack.dll");
        var type = new TypeDefinition("Tests", "InvalidStack", TypeAttributes.Public | TypeAttributes.Class);
        module.TopLevelTypes.Add(type);
        // A non-void signature with an empty return stack gets no recovered value.
        var method = new MethodDefinition("Invalid", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32));
        type.Methods.Add(method);
        IlGenerator.GenerateIl(caller, method);
        Assert.That(method.CilMethodBody!.Instructions[0].OpCode, Is.EqualTo(CilOpCodes.Ret));
        // The verifier compares pushes against the declared bound, so a failed stack
        // analysis still declares the provable ceiling - the body's total pushes -
        // rather than a guessed bound or a 0 nothing can satisfy.
        Assert.That(method.CilMethodBody.MaxStack, Is.GreaterThanOrEqualTo(1));
        Assert.That(caller.AnalysisWarnings.Any(w => w.Contains("Invalid reconstructed IL stack")), Is.True);
        Assert.That(method.CilMethodBody.Instructions.Any(i => i.Operand is string s && s.Contains("Invalid reconstructed IL stack")), Is.True);
        Assert.That(method.CilMethodBody.Instructions[^1].OpCode, Is.EqualTo(CilOpCodes.Throw));
    }

    [Test]
    public void TypedPointerMemoryLoadUsesThePointerElementType()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Int32", TypeAttributes.Public));
        var pointerType = new PointerTypeAnalysisContext(app.SystemTypes.SystemInt32Type);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"), pointerType);
        var result = new LocalVariable("result", new Register(null, "result")) { Type = app.SystemTypes.SystemInt32Type };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read",
            app.SystemTypes.SystemInt32Type, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, [pointerType]);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, result, new MemoryOperand(pointer)),
            new(1, OpCode.Return, result)]);
        context.Locals = [pointer, result];
        context.ParameterLocals = [pointer];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("TypedPointerLoad.dll");
        var type = new TypeDefinition("Tests", "TypedPointerLoad", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Read", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32, [module.CorLibTypeFactory.Int32.MakePointerType()]));
        type.Methods.Add(method);
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "pointer", 0));

        IlGenerator.GenerateIl(context, method);

        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Ldobj), Is.True);
        Assert.That(method.CilMethodBody.Instructions.Any(i => i.Operand is string text && text.Contains("Unmanaged memory load")), Is.False);
    }

    [Test]
    public void LateRecoveredReferenceFieldComparedToZeroUsesNull()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("child", app.SystemTypes.SystemStringType,
            System.Reflection.FieldAttributes.Public, owner, 16);
        owner.Fields.Add(field);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver")) { Type = owner };
        var erased = new LocalVariable("erased", new Register(null, "erased"))
            { Type = app.SystemTypes.SystemObjectType };
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemBooleanType };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "IsNull",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, [owner]);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, erased, new ReferenceCast(receiver, owner)),
            new(1, OpCode.CheckEqual, result, new MemoryOperand(erased, addend: 16), new Immediate(0)),
            new(2, OpCode.Return)]);
        context.Locals = [receiver, erased, result];
        context.ParameterLocals = [receiver];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("LateFieldNull.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemStringType,
            app.SystemTypes.SystemBooleanType, app.SystemTypes.SystemVoidType);
        var ownerDefinition = new TypeDefinition("Tests", "Owner", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(ownerDefinition);
        owner.PutExtraData("AsmResolverType", ownerDefinition);
        var fieldDefinition = new FieldDefinition("child", FieldAttributes.Public,
            new FieldSignature(module.CorLibTypeFactory.String));
        ownerDefinition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        var method = new MethodDefinition("IsNull", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [owner.ToTypeSignature()]));
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "receiver", 0));
        ownerDefinition.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        var il = method.CilMethodBody!.Instructions;
        var equality = il.IndexOf(il.First(i => i.OpCode == CilOpCodes.Ceq));
        Assert.Multiple(() =>
        {
            Assert.That(il.Take(equality).Any(i => i.OpCode == CilOpCodes.Ldfld), Is.True);
            Assert.That(il[equality - 1].OpCode, Is.EqualTo(CilOpCodes.Ldnull));
        });
    }

    [Test]
    public void HiddenStructReturnIsWrittenToAddressedBuffer()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var instance = new GenericInstanceTypeAnalysisContext(list, [app.SystemTypes.SystemStringType]);
        var getEnumerator = new ConcreteGenericMethodAnalysisContext(
            list.Methods.Single(method => method.Name == "GetEnumerator"), [app.SystemTypes.SystemObjectType], []);
        var receiver = new LocalVariable("receiver", new Register(null, "X0")) { Type = instance };
        var buffer = new LocalVariable("buffer", new Register(null, "stack_-20"));
        var pointer = new LocalVariable("pointer", new Register(null, "X8"));
        var consumed = new LocalVariable("consumed", new Register(null, "X1"));
        var currentSlot = new LocalVariable("currentSlot", new Register(null, "stack_-10"));
        var current = new LocalVariable("current", new Register(null, "X2"));
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        var call = new Instruction(1, OpCode.Call, getEnumerator, new MemoryOperand(pointer), receiver);
        var copy = new Instruction(2, OpCode.Move, consumed, buffer);
        var currentCopy = new Instruction(3, OpCode.Move, current, currentSlot);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, pointer, new AddressOf(buffer)), call, copy, currentCopy, new(4, OpCode.Return)]);
        context.Locals = [receiver, buffer, pointer, consumed, currentSlot, current];
        context.ParameterLocals = [];

        Cpp2IL.Core.Analysis.LocalVariables.ResolveHiddenReturnBuffers(context);

        Assert.Multiple(() =>
        {
            Assert.That(call.Destination, Is.Not.SameAs(buffer));
            Assert.That(call.Destination, Is.TypeOf<LocalVariable>());
            Assert.That(((LocalVariable)call.Destination!).Type!.FullName,
                Does.Contain("Enumerator<System.String>"));
            Assert.That(copy.Operands[1], Is.SameAs(call.Destination));
            Assert.That(currentCopy.Operands[1], Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)currentCopy.Operands[1]).Field.Name, Is.EqualTo("_current"));
            Assert.That(((FieldReference)currentCopy.Operands[1]).Field.FieldType,
                Is.SameAs(app.SystemTypes.SystemStringType));
        });
    }

    [Test]
    public void ReusedHiddenReturnBufferDoesNotCrossEnumeratorLifetimes()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var getEnumerator = list.Methods.Single(method => method.Name == "GetEnumerator");
        var stringList = new GenericInstanceTypeAnalysisContext(list, [app.SystemTypes.SystemStringType]);
        var objectList = new GenericInstanceTypeAnalysisContext(list, [app.SystemTypes.SystemObjectType]);
        var stringReceiver = new LocalVariable("strings", new Register(null, "X0")) { Type = stringList };
        var objectReceiver = new LocalVariable("objects", new Register(null, "X1")) { Type = objectList };
        var buffer = new LocalVariable("buffer", new Register(null, "stack_-20"));
        var secondBuffer = new LocalVariable("secondBuffer", new Register(null, "stack_-20"));
        var pointer = new LocalVariable("pointer", new Register(null, "X8"));
        var secondPointer = new LocalVariable("secondPointer", new Register(null, "X8"));
        var first = new LocalVariable("first", new Register(null, "X2"));
        var firstLoop = new LocalVariable("firstLoop", new Register(null, "stack_-40"));
        var second = new LocalVariable("second", new Register(null, "X3"));
        var secondLoop = new LocalVariable("secondLoop", new Register(null, "stack_-50"));
        var firstCall = new Instruction(1, OpCode.Call, getEnumerator, new MemoryOperand(pointer), stringReceiver);
        var firstCopy = new Instruction(2, OpCode.Move, first, buffer);
        var firstLoopCopy = new Instruction(3, OpCode.Move, firstLoop, first);
        var secondCall = new Instruction(3, OpCode.Call, getEnumerator, new MemoryOperand(secondPointer), objectReceiver);
        var secondCopy = new Instruction(4, OpCode.Move, second, secondBuffer);
        var secondLoopCopy = new Instruction(5, OpCode.Move, secondLoop, second);
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, pointer, new AddressOf(buffer)), firstCall, firstCopy, firstLoopCopy,
            new(3, OpCode.Move, secondPointer, new AddressOf(secondBuffer)), secondCall, secondCopy, secondLoopCopy,
            new(6, OpCode.Return)]);
        context.Locals = [stringReceiver, objectReceiver, buffer, secondBuffer, pointer, secondPointer,
            first, firstLoop, second, secondLoop];
        context.ParameterLocals = [];

        Cpp2IL.Core.Analysis.LocalVariables.ResolveHiddenReturnBuffers(context);

        Assert.Multiple(() =>
        {
            Assert.That(firstCall.Destination, Is.Not.SameAs(secondCall.Destination));
            Assert.That(firstCall.Destination, Is.SameAs(firstLoop));
            Assert.That(secondCall.Destination, Is.SameAs(secondLoop));
            Assert.That(firstCopy.Operands[1], Is.SameAs(firstCall.Destination));
            Assert.That(secondCopy.Operands[1], Is.SameAs(secondCall.Destination));
            Assert.That(secondCopy.Operands[1], Is.Not.SameAs(firstCall.Destination));
        });
    }

    [Test]
    public void HiddenEnumeratorReturnSplitsWideCurrentIntoItsFields()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var valueType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!;
        var entry = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Entry",
            valueType, System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Sealed
                | System.Reflection.TypeAttributes.SequentialLayout);
        var id = new InjectedFieldAnalysisContext("id", app.SystemTypes.SystemStringType,
            System.Reflection.FieldAttributes.Public, entry, 0);
        var prefab = new InjectedFieldAnalysisContext("prefab", app.SystemTypes.SystemObjectType,
            System.Reflection.FieldAttributes.Public, entry, 8);
        entry.Fields.Add(id);
        entry.Fields.Add(prefab);

        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var instance = new GenericInstanceTypeAnalysisContext(list, [entry]);
        var getEnumerator = new ConcreteGenericMethodAnalysisContext(
            list.Methods.Single(method => method.Name == "GetEnumerator"), [app.SystemTypes.SystemObjectType], []);
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var items = new InjectedFieldAnalysisContext("items", instance,
            System.Reflection.FieldAttributes.Public, owner, 16);
        owner.Fields.Add(items);
        var self = new LocalVariable("this", new Register(null, "X0"), owner) { IsThis = true };
        var receiver = new LocalVariable("receiver", new Register(null, "X1"));
        var buffer = new LocalVariable("buffer", new Register(null, "stack_-20"));
        var pointer = new LocalVariable("pointer", new Register(null, "X8"));
        var firstSlot = new LocalVariable("firstSlot", new Register(null, "stack_-10"));
        var secondSlot = new LocalVariable("secondSlot", new Register(null, "stack_-8"));
        var first = new LocalVariable("first", new Register(null, "X1"));
        var second = new LocalVariable("second", new Register(null, "X2"));
        var context = new InjectedMethodAnalysisContext(owner, "Read",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public, []);
        var call = new Instruction(2, OpCode.Call, getEnumerator, new MemoryOperand(pointer), receiver);
        var firstCopy = new Instruction(3, OpCode.Move, first, firstSlot) { NativeMemoryAccessSize = 8 };
        var secondCopy = new Instruction(4, OpCode.Move, second, secondSlot) { NativeMemoryAccessSize = 8 };
        var slotWrite = new Instruction(5, OpCode.Move, secondSlot, new Immediate(0))
            { NativeMemoryAccessSize = 8 };
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, receiver, new FieldReference(items, self, 16)),
            new(1, OpCode.Move, pointer, new AddressOf(buffer)), call, firstCopy, secondCopy,
            slotWrite, new(6, OpCode.Return)]);
        context.Locals = [self, receiver, buffer, pointer, firstSlot, secondSlot, first, second];
        context.ParameterLocals = [self];
        context.AnalysisWarnings = [];

        Cpp2IL.Core.Analysis.LocalVariables.ResolveTypesAndFields(context);

        var firstField = (FieldReference)firstCopy.Operands[1];
        var secondField = (FieldReference)secondCopy.Operands[1];
        Assert.Multiple(() =>
        {
            Assert.That(firstField.Field, Is.SameAs(id));
            Assert.That(secondField.Field, Is.SameAs(prefab));
            Assert.That(firstField.Containers.Single().Name, Is.EqualTo("_current"));
            Assert.That(secondField.Containers.Single().Name, Is.EqualTo("_current"));
            Assert.That(slotWrite.Operands[0], Is.SameAs(secondSlot));
        });
    }

    [Test]
    public void HiddenStructReturnSharpensAfterReceiverFieldIsTyped()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var instance = new GenericInstanceTypeAnalysisContext(list, [app.SystemTypes.SystemStringType]);
        var getEnumerator = new ConcreteGenericMethodAnalysisContext(
            list.Methods.Single(method => method.Name == "GetEnumerator"), [app.SystemTypes.SystemObjectType], []);
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var items = new InjectedFieldAnalysisContext("items", instance,
            System.Reflection.FieldAttributes.Public, owner, 16);
        owner.Fields.Add(items);
        var self = new LocalVariable("this", new Register(null, "X0"), owner) { IsThis = true };
        var receiver = new LocalVariable("receiver", new Register(null, "X1"));
        var buffer = new LocalVariable("buffer", new Register(null, "stack_-20"));
        var pointer = new LocalVariable("pointer", new Register(null, "X8"));
        var currentSlot = new LocalVariable("currentSlot", new Register(null, "stack_-10"));
        var current = new LocalVariable("current", new Register(null, "X2"));
        var context = new InjectedMethodAnalysisContext(owner, "Read", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public, []);
        var call = new Instruction(2, OpCode.Call, getEnumerator, new MemoryOperand(pointer), receiver);
        var currentCopy = new Instruction(3, OpCode.Move, current, currentSlot);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, receiver, new FieldReference(items, self, 16)),
            new(1, OpCode.Move, pointer, new AddressOf(buffer)), call, currentCopy, new(4, OpCode.Return)]);
        context.Locals = [self, receiver, buffer, pointer, currentSlot, current];
        context.ParameterLocals = [self];
        context.AnalysisWarnings = [];

        Cpp2IL.Core.Analysis.LocalVariables.ResolveTypesAndFields(context);

        Assert.Multiple(() =>
        {
            Assert.That(((LocalVariable)call.Destination!).Type!.FullName,
                Does.Contain("Enumerator<System.String>"));
            Assert.That(currentCopy.Operands[1], Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)currentCopy.Operands[1]).Field.FieldType,
                Is.SameAs(app.SystemTypes.SystemStringType));
            Assert.That(current.Type, Is.SameAs(app.SystemTypes.SystemStringType));
        });
    }

    [Test]
    public void InlinedListEnumeratorCurrentUsesPublicGetter()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var enumeratorDefinition = list.NestedTypes.Single(type => type.Name == "Enumerator");
        var enumerator = new GenericInstanceTypeAnalysisContext(enumeratorDefinition,
            [app.SystemTypes.SystemStringType]);
        var currentField = new ConcreteGenericFieldAnalysisContext(
            enumeratorDefinition.Fields.Single(field => field.Name == "_current"), enumerator);
        var receiver = new LocalVariable("enumerator", new Register(null, "enumerator"), enumerator);
        var current = new LocalVariable("current", new Register(null, "current"),
            app.SystemTypes.SystemStringType);
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, current, new FieldReference(currentField, receiver, currentField.Offset)),
            new(1, OpCode.Return)]);
        context.Locals = [receiver, current];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("EnumeratorCurrent.dll");
        var emittedEnumerator = new TypeDefinition("System.Collections.Generic", "Enumerator`1",
            TypeAttributes.Public | TypeAttributes.SequentialLayout | TypeAttributes.Sealed,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        emittedEnumerator.GenericParameters.Add(new GenericParameter("T"));
        module.TopLevelTypes.Add(emittedEnumerator);
        enumeratorDefinition.PutExtraData("AsmResolverType", emittedEnumerator);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemStringType, app.SystemTypes.SystemVoidType);
        var owner = new TypeDefinition("Tests", "Owner", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Read", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        Assert.That(method.CilMethodBody!.Instructions.Any(instruction => instruction.OpCode == CilOpCodes.Call
            && instruction.Operand is MemberReference { Name: { } name }
            && name.ToString() == "get_Current"), Is.True,
            () => string.Join("\n", method.CilMethodBody.Instructions.Select(instruction => instruction.ToString())));
    }

    [Test]
    public void InlinedEnumeratorCurrentUsesNestedValueGetter()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var valueType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!;
        var entry = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Entry",
            valueType, System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Sealed
                | System.Reflection.TypeAttributes.SequentialLayout);
        var key = new InjectedFieldAnalysisContext("key", app.SystemTypes.SystemStringType,
            System.Reflection.FieldAttributes.Private, entry, 0);
        entry.Fields.Add(key);
        var keyGetter = entry.InjectMethodContext("get_Key", app.SystemTypes.SystemStringType,
            ReflectionMethodAttributes.Public, []);
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var enumeratorDefinition = list.NestedTypes.Single(type => type.Name == "Enumerator");
        var enumerator = new GenericInstanceTypeAnalysisContext(enumeratorDefinition, [entry]);
        var currentField = new ConcreteGenericFieldAnalysisContext(
            enumeratorDefinition.Fields.Single(field => field.Name == "_current"), enumerator);
        var receiver = new LocalVariable("enumerator", new Register(null, "enumerator"), enumerator);
        var result = new LocalVariable("result", new Register(null, "result"), app.SystemTypes.SystemStringType);
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, result,
                new FieldReference(key, receiver, currentField.Offset, [currentField], 8)),
            new(1, OpCode.Return)]);
        context.Locals = [receiver, result];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("NestedEnumeratorCurrent.dll");
        var emittedEnumerator = new TypeDefinition("System.Collections.Generic", "Enumerator`1",
            TypeAttributes.Public | TypeAttributes.SequentialLayout | TypeAttributes.Sealed,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        emittedEnumerator.GenericParameters.Add(new GenericParameter("T"));
        module.TopLevelTypes.Add(emittedEnumerator);
        enumeratorDefinition.PutExtraData("AsmResolverType", emittedEnumerator);
        var emittedEntry = new TypeDefinition("Tests", "Entry",
            TypeAttributes.Public | TypeAttributes.SequentialLayout | TypeAttributes.Sealed,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(emittedEntry);
        entry.PutExtraData("AsmResolverType", emittedEntry);
        var emittedKeyGetter = new MethodDefinition("get_Key", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.String));
        emittedEntry.Methods.Add(emittedKeyGetter);
        keyGetter.PutExtraData("AsmResolverMethod", emittedKeyGetter);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemStringType, app.SystemTypes.SystemVoidType);
        var owner = new TypeDefinition("Tests", "Owner", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Read", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        var calls = method.CilMethodBody!.Instructions
            .Where(instruction => instruction.OpCode == CilOpCodes.Call)
            .Select(instruction => instruction.Operand?.ToString()).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(calls.Any(call => call?.Contains("get_Current") == true), Is.True);
            Assert.That(calls.Any(call => call?.Contains("get_Key") == true), Is.True,
                () => string.Join("\n", method.CilMethodBody.Instructions));
        });
    }

    [Test]
    public void WholeEnumeratorCurrentIsLoadedWhenNestedFieldLocalKeepsStructType()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = app.AssembliesByName["UnityEngine.CoreModule"]
            .GetTypeByFullName("UnityEngine.Vector2Int")!;
        vector.OverrideAttributes = System.Reflection.TypeAttributes.Public
            | System.Reflection.TypeAttributes.Sealed | System.Reflection.TypeAttributes.SequentialLayout;
        var x = vector.Fields.Single(field => field.Name == "m_X");
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var enumeratorDefinition = list.NestedTypes.Single(type => type.Name == "Enumerator");
        enumeratorDefinition.OverrideAttributes = System.Reflection.TypeAttributes.NestedPublic
            | System.Reflection.TypeAttributes.Sealed | System.Reflection.TypeAttributes.SequentialLayout;
        var enumerator = new GenericInstanceTypeAnalysisContext(enumeratorDefinition, [vector]);
        var current = new ConcreteGenericFieldAnalysisContext(
            enumeratorDefinition.Fields.Single(field => field.Name == "_current"), enumerator);
        var receiver = new LocalVariable("enumerator", new Register(null, "enumerator"), enumerator);
        var result = new LocalVariable("result", new Register(null, "result"), vector);
        var caller = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Caller", app.SystemTypes.SystemObjectType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        var context = new InjectedMethodAnalysisContext(caller, "Read",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        var nested = new FieldReference(x, receiver, current.Offset + x.Offset, [current], 4);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, result, nested),
            new(1, OpCode.Return)]);
        context.Locals = [receiver, result];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("WholeEnumeratorCurrent.dll");
        var emittedEnumerator = new TypeDefinition("System.Collections.Generic", "Enumerator`1",
            TypeAttributes.Public | TypeAttributes.SequentialLayout | TypeAttributes.Sealed,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        emittedEnumerator.GenericParameters.Add(new GenericParameter("T"));
        module.TopLevelTypes.Add(emittedEnumerator);
        enumeratorDefinition.PutExtraData("AsmResolverType", emittedEnumerator);
        var emittedVector = new TypeDefinition("UnityEngine", "Vector2Int",
            TypeAttributes.Public | TypeAttributes.SequentialLayout | TypeAttributes.Sealed,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(emittedVector);
        vector.PutExtraData("AsmResolverType", emittedVector);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemVoidType);
        var owner = new TypeDefinition("Tests", "Owner", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Read", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        Assert.Multiple(() =>
        {
            Assert.That(IlGenerator.WholeValueContainerReference(nested, vector)?.Field.FieldType.FullName,
                Is.EqualTo(vector.FullName), $"x offset={x.Offset}, current offset={current.Offset}");
            Assert.That(method.CilMethodBody!.Instructions.Any(instruction => instruction.OpCode == CilOpCodes.Call
                && instruction.Operand?.ToString()?.Contains("get_Current") == true), Is.True,
                () => string.Join("\n", method.CilMethodBody.LocalVariables.Select(local => local.VariableType.FullName))
                    + "\n" + string.Join("\n", method.CilMethodBody.Instructions));
            Assert.That(method.CilMethodBody.Instructions.Any(instruction => instruction.Operand?.ToString()?.Contains("m_X") == true),
                Is.False, () => string.Join("\n", method.CilMethodBody.Instructions));
        });
    }

    [Test]
    public void RuntimeFieldHandleFollowsMetadataLocalAlias()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Data",
            app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var field = new InjectedFieldAnalysisContext("Bytes", app.SystemTypes.SystemInt32Type,
            System.Reflection.FieldAttributes.Assembly | System.Reflection.FieldAttributes.Static, owner);
        var metadata = new RuntimeFieldInfoAnalysisContext(field, owner.DeclaringAssembly!);
        var handle = new LocalVariable("handle", new Register(null, "X1"), metadata);
        var context = new InjectedMethodAnalysisContext(owner, "Read", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, handle, metadata), new(1, OpCode.Return)]);

        var contract = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.RuntimeFieldHandle")!;
        Assert.That(IlGenerator.RuntimeFieldHandleSource(handle, contract, context), Is.SameAs(metadata));
    }

    [Test]
    public void RuntimeFieldHandleCanTokenSameAssemblyDataFieldWithPrivateSignature()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var hidden = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "HiddenData",
            app.SystemTypes.SystemValueTypeType, System.Reflection.TypeAttributes.NotPublic);
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Data",
            app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.NotPublic);
        var field = new InjectedFieldAnalysisContext("Bytes", hidden,
            System.Reflection.FieldAttributes.Assembly | System.Reflection.FieldAttributes.Static, owner);
        var module = new ModuleDefinition("Data.dll");
        field.PutExtraData("AsmResolverField", new FieldDefinition("Bytes", FieldAttributes.Assembly
            | FieldAttributes.Static, new FieldSignature(module.CorLibTypeFactory.Int32)));
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);

        Assert.That(IlGenerator.RuntimeFieldTokenUsableFrom(field, context), Is.True);
    }

    [Test]
    public void LayerMaskBackingFieldUsesPublicImplicitConversion()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var layerMask = app.AssembliesByName["UnityEngine.CoreModule"].GetTypeByFullName("UnityEngine.LayerMask")!;
        var mask = layerMask.Fields.Single(field => field.Name == "m_Mask");
        var local = new LocalVariable("mask", new Register(null, "mask"), layerMask);
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([new(0, OpCode.Return)]);
        context.Locals = [local];
        context.ParameterLocals = [];

        var conversion = IlGenerator.BackingFieldConversion(new FieldReference(mask, local, mask.Offset), context);

        Assert.That(conversion?.Name, Is.EqualTo("op_Implicit"));
        Assert.That(conversion?.ReturnType.FullName, Is.EqualTo("UnityEngine.LayerMask"));

        var host = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Host", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var outer = new InjectedFieldAnalysisContext("mask", layerMask,
            System.Reflection.FieldAttributes.Public, host, 16);
        var self = new LocalVariable("this", new Register(null, "this"), host) { IsThis = true };
        var nested = new FieldReference(mask, self, mask.Offset, [outer]);
        Assert.That(IlGenerator.BackingFieldConversion(nested, context)?.Name, Is.EqualTo("op_Implicit"));
    }

    [Test]
    public void NestedZeroOffsetFieldCanRepresentItsWholeValueContainer()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var dateTime = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.DateTime")!;
        var host = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Host",
            app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var purchaseTime = new InjectedFieldAnalysisContext("_purchaseTime", dateTime,
            System.Reflection.FieldAttributes.Public, host, 16);
        var storage = dateTime.Fields.Single(field => field.Name == "_dateData");
        var self = new LocalVariable("this", new Register(null, "this"), host) { IsThis = true };
        var nested = new FieldReference(storage, self, purchaseTime.Offset, [purchaseTime]);

        var recovered = IlGenerator.WholeValueContainerReference(nested, dateTime);

        Assert.That(recovered?.Field, Is.SameAs(purchaseTime));
        Assert.That(IlGenerator.WholeValueContainerReference(nested, storage.FieldType), Is.Null);

        var context = new InjectedMethodAnalysisContext(host, "Read", dateTime,
            ReflectionMethodAttributes.Public, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Return, nested)]);
        context.Locals = [self];
        context.ParameterLocals = [self];
        context.AnalysisWarnings = [];
        var module = new ModuleDefinition("WholeValueContainer.dll");
        SeedCorLibTypes(app, module, dateTime, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        var hostDefinition = new TypeDefinition("Tests", "Host", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(hostDefinition);
        host.PutExtraData("AsmResolverType", hostDefinition);
        var fieldDefinition = new FieldDefinition("_purchaseTime", FieldAttributes.Public,
            new FieldSignature(dateTime.ToTypeSignature()));
        hostDefinition.Fields.Add(fieldDefinition);
        purchaseTime.PutExtraData("AsmResolverField", fieldDefinition);
        var definition = new MethodDefinition("Read", MethodAttributes.Public,
            MethodSignature.CreateInstance(dateTime.ToTypeSignature()));
        hostDefinition.Methods.Add(definition);

        IlGenerator.GenerateIl(context, definition);

        Assert.That(definition.CilMethodBody!.Instructions
            .Any(instruction => instruction.OpCode == CilOpCodes.Ldfld
                && ReferenceEquals(instruction.Operand, fieldDefinition)), Is.True);
    }

    [Test]
    public void ChainedThisPointerAddsResolveTheFinalField()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var first = new InjectedFieldAnalysisContext("first", app.SystemTypes.SystemInt32Type,
            System.Reflection.FieldAttributes.Public, owner, 16);
        var second = new InjectedFieldAnalysisContext("second", app.SystemTypes.SystemInt32Type,
            System.Reflection.FieldAttributes.Public, owner, 32);
        owner.Fields.Add(first);
        owner.Fields.Add(second);
        var self = new LocalVariable("this", new Register(null, "X0"), owner) { IsThis = true };
        var intermediate = new LocalVariable("intermediate", new Register(null, "X1"))
            { Type = app.SystemTypes.SystemObjectType };
        var result = new LocalVariable("result", new Register(null, "X2"))
            { Type = app.SystemTypes.SystemInt32Type };
        var context = new InjectedMethodAnalysisContext(owner, "Read", app.SystemTypes.SystemInt32Type,
            ReflectionMethodAttributes.Public, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Add, intermediate, self, new Immediate(16)),
            new(1, OpCode.Add, result, intermediate, new Immediate(16)),
            new(2, OpCode.Return, result)]);
        context.Locals = [self, intermediate, result];
        context.ParameterLocals = [self];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("ChainedFieldAddress.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemVoidType);
        var ownerDefinition = new TypeDefinition("Tests", "Owner", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(ownerDefinition);
        owner.PutExtraData("AsmResolverType", ownerDefinition);
        foreach (var pair in new[] { (first, "first"), (second, "second") })
        {
            var fieldDefinition = new FieldDefinition(pair.Item2, FieldAttributes.Public,
                new FieldSignature(module.CorLibTypeFactory.Int32));
            ownerDefinition.Fields.Add(fieldDefinition);
            pair.Item1.PutExtraData("AsmResolverField", fieldDefinition);
        }
        var method = new MethodDefinition("Read", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Int32));
        ownerDefinition.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        Assert.That(method.CilMethodBody!.Instructions.Any(instruction => instruction.OpCode == CilOpCodes.Ldfld
            && instruction.Operand is IFieldDescriptor field && field.Name?.ToString() == "second"), Is.True,
            () => string.Join("\n", method.CilMethodBody.Instructions));
    }

    [Test]
    public void FieldFromGenericBaseUsesTheConcreteBaseInstance()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var assembly = app.AssembliesByName["mscorlib"];
        var genericBase = new InjectedTypeAnalysisContext(assembly, "Tests", "Base`1",
            app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        genericBase.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0,
            LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_VAR, 0, genericBase));
        var field = genericBase.InjectFieldContext("value", genericBase.GenericParameters[0],
            System.Reflection.FieldAttributes.Public);
        var instance = new GenericInstanceTypeAnalysisContext(genericBase, [app.SystemTypes.SystemStringType]);
        var derived = new InjectedTypeAnalysisContext(assembly, "Tests", "Derived", instance,
            System.Reflection.TypeAttributes.Public);

        Assert.That(IlGenerator.GenericFieldOwnerInstance(derived, field), Is.SameAs(instance));
    }

    [Test]
    public void UnknownMemoryLoadRemainsExplicitlyUnresolved()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Int32", TypeAttributes.Public));
        var result = new LocalVariable("result", new Register(null, "result")) { Type = app.SystemTypes.SystemInt32Type };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Read",
            app.SystemTypes.SystemInt32Type, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, result, new MemoryOperand(addend: 0x1234)),
            new(1, OpCode.Return, result)]);
        context.Locals = [result];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("UnknownMemoryLoad.dll");
        var type = new TypeDefinition("Tests", "UnknownMemoryLoad", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Read", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        var instructions = method.CilMethodBody!.Instructions;
        Assert.That(instructions.Any(i => i.Operand is string text && text.Contains("Unmanaged memory load")), Is.True);
        Assert.That(instructions.Any(i => i.OpCode == CilOpCodes.Throw), Is.True);
        Assert.That(instructions.Any(i => i.OpCode == CilOpCodes.Conv_I || i.OpCode == CilOpCodes.Ldc_I4_0), Is.False);
    }

    [TestCase(0L, 0L)]
    [TestCase(0x7fffffffL, 34359738352L)]
    [TestCase(0x80000000L, -34359738368L)]
    [TestCase(0xffffffffL, -16L)]
    [TestCase(0x100000001L, 16L)]
    public void SignedWordExtensionExecutesWithCorrectLowWordAndScale(long input, long expected)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Extend",
            app.SystemTypes.SystemInt64Type, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        var wide = new LocalVariable("wide", new Register(null, "wide"));
        var scaled = new LocalVariable("scaled", new Register(null, "scaled"));
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.SignExtend32, wide, new Immediate(input)),
            new(1, OpCode.ShiftLeft, scaled, wide, new Immediate(4)),
            new(2, OpCode.Return, scaled)]);
        caller.Locals = [wide, scaled];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("ExtensionTest.dll", new AssemblyReference("System.Private.CoreLib", typeof(object).Assembly.GetName().Version!));
        var type = new TypeDefinition("Tests", "Extension", TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Extend", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int64));
        type.Methods.Add(method);
        IlGenerator.GenerateIl(caller, method);
        // This standalone harness supplies the primitive signatures without generating the
        // fixture game's entire mscorlib. Exercise the actual emitted conversion and shift IL.
        foreach (var local in method.CilMethodBody!.LocalVariables)
            local.VariableType = module.CorLibTypeFactory.Int64;
        Assert.That(method.CilMethodBody.MaxStack, Is.GreaterThan(0));

        var assembly = new AssemblyDefinition("ExtensionTest", new Version(1, 0));
        assembly.Modules.Add(module);
        using var stream = new System.IO.MemoryStream();
        module.Write(stream);
        var loaded = System.Reflection.Assembly.Load(stream.ToArray());
        Assert.That(loaded.GetType("Tests.Extension")!.GetMethod("Extend")!.Invoke(null, null), Is.EqualTo(expected));
    }

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [TestCase(false, true, false)]
    [TestCase(true, true, false)]
    [TestCase(false, false, true)]
    [TestCase(false, false, false)] // a virtual callee on a non-`this` receiver must dispatch virtually
    public void InterfaceCallPreservesRuntimeDispatch(bool isStatic, bool isInterface, bool virtualDispatch)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = app.SystemTypes.SystemObjectType;
        var iface = new InjectedTypeAnalysisContext(owner.DeclaringAssembly, "Tests", "IDispatch", null,
            System.Reflection.TypeAttributes.Public | (isInterface ? System.Reflection.TypeAttributes.Interface : System.Reflection.TypeAttributes.Class) | System.Reflection.TypeAttributes.Abstract);
        var target = iface.InjectMethodContext("Invoke", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | (isStatic ? ReflectionMethodAttributes.Static : ReflectionMethodAttributes.Abstract | ReflectionMethodAttributes.Virtual));
        var caller = new InjectedMethodAnalysisContext(owner, "Caller", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([isStatic ? new(0, OpCode.CallVoid, target) : new(0, OpCode.CallVoid, target, new Immediate(0)), new(1, OpCode.Return)]);
        caller.ControlFlowGraph.Instructions[0].IsVirtualDispatch = virtualDispatch;
        caller.Locals = [];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("DispatchTest.dll");
        var type = new TypeDefinition("Tests", "IDispatch", TypeAttributes.Public | TypeAttributes.Interface | TypeAttributes.Abstract);
        module.TopLevelTypes.Add(type);
        var targetDefinition = new MethodDefinition("Invoke", MethodAttributes.Public | (isStatic ? MethodAttributes.Static : MethodAttributes.Abstract | MethodAttributes.Virtual),
            isStatic ? MethodSignature.CreateStatic(module.CorLibTypeFactory.Void) : MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        type.Methods.Add(targetDefinition);
        target.PutExtraData("AsmResolverMethod", targetDefinition);
        var method = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);
        IlGenerator.GenerateIl(caller, method);
        // ECMA III.3.19: `call` to a non-final virtual on a non-sealed type only verifies
        // on the caller's own `this` pointer (or a boxed value type). Every non-static row
        // targets a non-final virtual with a placeholder receiver, so `callvirt` is the
        // only verifiable spelling; the static target keeps `call`.
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == (!isStatic ? CilOpCodes.Callvirt : CilOpCodes.Call) && i.Operand == targetDefinition), Is.True);
    }

    [Test]
    public void DirectCallToVirtualOnAddressOfObjectEmitsCallvirtAndNarrowingCast()
    {
        // Enum::ToString is a non-final virtual on a non-sealed reference type and the
        // recovered receiver is the address of an object local: `call` cannot verify on
        // a non-`this` receiver and the dereferenced object is not statically an Enum.
        // The honest emission is ldind.ref + castclass + callvirt.
        var app = Cpp2IlApi.CurrentAppContext!;
        var enumType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Enum")!;
        var toString = enumType.GetMethod("ToString", 0);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"))
            { Type = app.SystemTypes.SystemObjectType };
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemStringType };
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Call, toString, result, new AddressOf(receiver)),
            new(1, OpCode.Return)]);
        caller.Locals = [receiver, result];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("VirtualThis.dll");
        var enumDefinition = new TypeDefinition("System", "Enum",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(enumDefinition);
        enumType.PutExtraData("AsmResolverType", enumDefinition);
        app.SystemTypes.SystemStringType.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "String", TypeAttributes.Public | TypeAttributes.Class,
                module.CorLibTypeFactory.Object.Type));
        var toStringDefinition = new MethodDefinition("ToString", MethodAttributes.Public | MethodAttributes.Virtual,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.String));
        enumDefinition.Methods.Add(toStringDefinition);
        toString.PutExtraData("AsmResolverMethod", toStringDefinition);
        var owner = new TypeDefinition("Tests", "Host", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Callvirt && i.Operand == toStringDefinition), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call && i.Operand == toStringDefinition), Is.False);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldind_Ref), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Castclass), Is.True);
        });
    }

    [Test]
    public void DirectCallToVirtualOnEnumAddressEmitsBoxedReceiver()
    {
        // The same virtual callee with the address of a genuinely enum-typed local
        // recovers the real receiver: ldobj + box leaves a boxed enum on the stack,
        // which is assignable to System.Enum and verifiable under callvirt.
        var app = Cpp2IlApi.CurrentAppContext!;
        var enumType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Enum")!;
        var toString = enumType.GetMethod("ToString", 0);
        var myEnum = new InjectedTypeAnalysisContext(enumType.DeclaringAssembly,
            "Tests", "MyEnum", enumType, System.Reflection.TypeAttributes.Public);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver")) { Type = myEnum };
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemStringType };
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Call, toString, result, new AddressOf(receiver)),
            new(1, OpCode.Return)]);
        caller.Locals = [receiver, result];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("VirtualEnum.dll");
        var enumDefinition = new TypeDefinition("System", "Enum",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(enumDefinition);
        enumType.PutExtraData("AsmResolverType", enumDefinition);
        app.SystemTypes.SystemStringType.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "String", TypeAttributes.Public | TypeAttributes.Class,
                module.CorLibTypeFactory.Object.Type));
        var toStringDefinition = new MethodDefinition("ToString", MethodAttributes.Public | MethodAttributes.Virtual,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.String));
        enumDefinition.Methods.Add(toStringDefinition);
        toString.PutExtraData("AsmResolverMethod", toStringDefinition);
        myEnum.PutExtraData("AsmResolverType", new TypeDefinition("Tests", "MyEnum",
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            enumDefinition));
        var owner = new TypeDefinition("Tests", "Host", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Callvirt && i.Operand == toStringDefinition), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldobj), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Box), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.False);
        });
    }

    [Test]
    public void DirectCallToVirtualOnOwnThisStaysCall()
    {
        // `call` to a non-final virtual is still the right (and only verifiable)
        // spelling for base calls: the receiver is the caller's own `this`.
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Tests", "Base", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var speak = owner.InjectMethodContext("Speak", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Virtual);
        var thisLocal = new LocalVariable("this", new Register(null, "this")) { Type = owner, IsThis = true };
        var caller = new InjectedMethodAnalysisContext(owner, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, speak, thisLocal),
            new(1, OpCode.Return)]);
        caller.Locals = [thisLocal];
        caller.ParameterLocals = [thisLocal];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("BaseCall.dll");
        var ownerDefinition = new TypeDefinition("Tests", "Base",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(ownerDefinition);
        owner.PutExtraData("AsmResolverType", ownerDefinition);
        var speakDefinition = new MethodDefinition("Speak", MethodAttributes.Public | MethodAttributes.Virtual,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        ownerDefinition.Methods.Add(speakDefinition);
        speak.PutExtraData("AsmResolverMethod", speakDefinition);
        var method = new MethodDefinition("Run", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        ownerDefinition.Methods.Add(method);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call && i.Operand == speakDefinition), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Callvirt && i.Operand == speakDefinition), Is.False);
        });
    }

    [Test]
    public void StaticCall_DoesNotLoadMethodInfoOperand()
    {
        var appContext = Cpp2IlApi.CurrentAppContext!;
        var systemObject = appContext.SystemTypes.SystemObjectType;
        var systemVoid = appContext.SystemTypes.SystemVoidType;
        var systemInt = appContext.SystemTypes.SystemInt32Type;

        var callerContext = new InjectedMethodAnalysisContext(
            systemObject,
            "Caller",
            systemVoid,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            []);

        var targetContext = new InjectedMethodAnalysisContext(
            systemObject,
            "TargetStatic",
            systemVoid,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            [systemInt, systemInt]);

        var x = new LocalVariable("x", new Register(null, "x"));
        var y = new LocalVariable("y", new Register(null, "y"));

        var instructions = new List<Instruction>
        {
            
            new(0, OpCode.Move, x, Imm(5)),
            new(1, OpCode.Move, y, Imm(10)),
            // Operand layout: target, arg0, arg1, trailing-non-parameter.
            new(2, OpCode.CallVoid, targetContext, x, y, Imm(999)),
            new(3, OpCode.Return),
        };

        callerContext.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        callerContext.Locals = [x, y];
        callerContext.ParameterLocals = [];
        callerContext.AnalysisWarnings = [];

        var module = new ModuleDefinition("Test.dll", new AssemblyReference("mscorlib", new Version(4, 0, 0, 0)));
        var typeDef = new TypeDefinition("Cpp2IL.Core.Tests", "IlGeneratorTestType", TypeAttributes.Class | TypeAttributes.Public);
        module.TopLevelTypes.Add(typeDef);

        var callerMethodDef = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        typeDef.Methods.Add(callerMethodDef);

        var targetMethodDef = new MethodDefinition("TargetStatic", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
                [module.CorLibTypeFactory.Int32, module.CorLibTypeFactory.Int32]));
        typeDef.Methods.Add(targetMethodDef);
        targetContext.PutExtraData("AsmResolverMethod", targetMethodDef);

        IlGenerator.GenerateIl(callerContext, callerMethodDef);

        var il = callerMethodDef.CilMethodBody!.Instructions;

        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call), Is.True, "expected generated method to contain a call");
        Assert.That(il.Any(i => i.Operand is int intOperand && intOperand == 999), Is.False,
            "trailing non-parameter operand must not be emitted as a call argument");
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldloc), Is.EqualTo(2),
            "expected exactly two Ldloc instructions for the two parameters of the target method");
    }

    [Test]
    public void RecoveredPrivateFieldAccessRelaxesOnlyReferencedMember()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "PrivateOwner",
            app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.NotPublic | System.Reflection.TypeAttributes.Class);
        var field = owner.InjectFieldContext("secret", app.SystemTypes.SystemInt32Type,
            System.Reflection.FieldAttributes.Private | System.Reflection.FieldAttributes.Static);
        var result = new LocalVariable("result", new Register(null, "result")) { Type = app.SystemTypes.SystemInt32Type };
        var methodContext = owner.InjectMethodContext("Read", app.SystemTypes.SystemInt32Type,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static);
        methodContext.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, result, new FieldReference(field, result, 0)),
            new(1, OpCode.Return, result)]);
        methodContext.Locals = [result];
        methodContext.ParameterLocals = [];
        methodContext.AnalysisWarnings = [];

        var module = new ModuleDefinition("PrivateFieldAccess.dll");
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Int32", TypeAttributes.Public));
        var ownerDefinition = new TypeDefinition("Tests", "PrivateOwner", TypeAttributes.NotPublic | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(ownerDefinition);
        var fieldDefinition = new FieldDefinition("secret", FieldAttributes.Private | FieldAttributes.Static,
            new FieldSignature(module.CorLibTypeFactory.Int32));
        ownerDefinition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        var method = new MethodDefinition("Read", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32));
        ownerDefinition.Methods.Add(method);

        IlGenerator.GenerateIl(methodContext, method);

        Assert.That(fieldDefinition.Attributes & FieldAttributes.FieldAccessMask, Is.EqualTo(FieldAttributes.Public));
        Assert.That(ownerDefinition.Attributes & TypeAttributes.VisibilityMask, Is.EqualTo(TypeAttributes.Public));
    }

    [Test]
    public void InlinedPrivateFieldLoadAcrossTypesIsEmitted()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        var callerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Caller",
            app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        var field = owner.InjectFieldContext("<Items>k__BackingField", app.SystemTypes.SystemInt32Type,
            System.Reflection.FieldAttributes.Private);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver")) { Type = owner };
        var result = new LocalVariable("result", new Register(null, "result")) { Type = app.SystemTypes.SystemInt32Type };
        var context = callerType.InjectMethodContext("Read", app.SystemTypes.SystemInt32Type,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, result, new FieldReference(field, receiver, 0)),
            new(1, OpCode.Return, result)]);
        context.Locals = [receiver, result];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("InlinedPrivateField.dll");
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Int32", TypeAttributes.Public));
        var ownerDefinition = new TypeDefinition("Tests", "Owner", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        var callerDefinition = new TypeDefinition("Tests", "Caller", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(ownerDefinition);
        module.TopLevelTypes.Add(callerDefinition);
        owner.PutExtraData("AsmResolverType", ownerDefinition);
        callerType.PutExtraData("AsmResolverType", callerDefinition);
        var fieldDefinition = new FieldDefinition("<Items>k__BackingField", FieldAttributes.Private,
            new FieldSignature(module.CorLibTypeFactory.Int32));
        ownerDefinition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        var method = new MethodDefinition("Read", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32));
        callerDefinition.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        Assert.Multiple(() =>
        {
            Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Ldfld), Is.True);
            Assert.That(fieldDefinition.Attributes & FieldAttributes.FieldAccessMask, Is.EqualTo(FieldAttributes.Public));
        });
    }

    [Test]
    public void PrivateDependencyFieldLoadStaysDefault()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "DependencyOwner", app.SystemTypes.SystemObjectType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        var field = owner.InjectFieldContext("secret", app.SystemTypes.SystemInt32Type,
            System.Reflection.FieldAttributes.Private);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver")) { Type = owner };
        var result = new LocalVariable("result", new Register(null, "result")) { Type = app.SystemTypes.SystemInt32Type };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "ReadDependency",
            app.SystemTypes.SystemInt32Type, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, result, new FieldReference(field, receiver, 0)),
            new(1, OpCode.Return, result)]);
        context.Locals = [receiver, result];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("PrivateDependencyField.dll");
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Int32", TypeAttributes.Public));
        var ownerDefinition = new TypeDefinition("Tests", "DependencyOwner", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        var callerDefinition = new TypeDefinition("Tests", "Caller", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(ownerDefinition);
        module.TopLevelTypes.Add(callerDefinition);
        owner.PutExtraData("AsmResolverType", ownerDefinition);
        var fieldDefinition = new FieldDefinition("secret", FieldAttributes.Private,
            new FieldSignature(module.CorLibTypeFactory.Int32));
        ownerDefinition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        var method = new MethodDefinition("ReadDependency", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32));
        callerDefinition.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        Assert.Multiple(() =>
        {
            Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Ldfld), Is.False);
            Assert.That(fieldDefinition.Attributes & FieldAttributes.FieldAccessMask, Is.EqualTo(FieldAttributes.Private));
        });
    }

    [Test]
    public void ValueTypeFieldLoadUsesOriginalLocalAddress()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var valueType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Value",
            valueType, System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Sealed
                | System.Reflection.TypeAttributes.SequentialLayout);
        var field = owner.InjectFieldContext("number", app.SystemTypes.SystemInt32Type,
            System.Reflection.FieldAttributes.Public);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), owner);
        var result = new LocalVariable("result", new Register(null, "result"), app.SystemTypes.SystemInt32Type);
        var context = new InjectedMethodAnalysisContext(owner, "Read", app.SystemTypes.SystemInt32Type,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, result, new FieldReference(field, receiver, 0)),
            new(1, OpCode.Return, result)]);
        context.Locals = [receiver, result];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("ValueFieldLoad.dll");
        var ownerDefinition = new TypeDefinition("Tests", "Value",
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(ownerDefinition);
        owner.PutExtraData("AsmResolverType", ownerDefinition);
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Int32", TypeAttributes.Public | TypeAttributes.SequentialLayout));
        var fieldDefinition = new FieldDefinition("number", FieldAttributes.Public,
            new FieldSignature(module.CorLibTypeFactory.Int32));
        ownerDefinition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        var method = new MethodDefinition("Read", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32));
        ownerDefinition.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        var body = method.CilMethodBody!;
        var loadAddress = body.Instructions.Single(i => i.OpCode == CilOpCodes.Ldloca);
        Assert.Multiple(() =>
        {
            Assert.That(loadAddress.Operand, Is.SameAs(body.LocalVariables[0]));
            Assert.That(body.LocalVariables, Has.Count.EqualTo(2));
        });
    }

    [Test]
    public void LongDestinationReceivesWidenedSmallLiteral()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var dest = new LocalVariable("dest", new Register(null, "dest")) { Type = app.SystemTypes.SystemInt64Type };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, dest, new Immediate(0)),
            new(1, OpCode.Return)]);
        context.Locals = [dest];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        var module = new ModuleDefinition("WidenLiteral.dll");
        app.SystemTypes.SystemInt64Type.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Int64", TypeAttributes.Public));
        var owner = new TypeDefinition("Tests", "Widen", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il[0].OpCode, Is.EqualTo(CilOpCodes.Ldc_I4));
            Assert.That(il[1].OpCode, Is.EqualTo(CilOpCodes.Conv_I8));
            Assert.That(il[2].OpCode, Is.EqualTo(CilOpCodes.Stloc));
        });
    }

    [Test]
    public void NarrowDestinationKeepsWideLiteralThenTruncates()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var dest = new LocalVariable("dest", new Register(null, "dest")) { Type = app.SystemTypes.SystemInt32Type };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, dest, new Immediate(0x100000000L)),
            new(1, OpCode.Return)]);
        context.Locals = [dest];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        var module = new ModuleDefinition("TruncateLiteral.dll");
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Int32", TypeAttributes.Public));
        var owner = new TypeDefinition("Tests", "Truncate", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il[0].OpCode, Is.EqualTo(CilOpCodes.Ldc_I8));
            Assert.That(il[0].Operand, Is.EqualTo(0x100000000L));
            Assert.That(il[1].OpCode, Is.EqualTo(CilOpCodes.Conv_I4));
            Assert.That(il[2].OpCode, Is.EqualTo(CilOpCodes.Stloc));
        });
    }

    [Test]
    public void BitwiseAndWithInt32OperandNarrowWideLiteral()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var value = new LocalVariable("value", new Register(null, "value")) { Type = app.SystemTypes.SystemInt32Type };
        var dest = new LocalVariable("dest", new Register(null, "dest")) { Type = app.SystemTypes.SystemInt32Type };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.And, dest, value, new Immediate(0x100000000L)),
            new(1, OpCode.Return)]);
        context.Locals = [value, dest];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        var module = new ModuleDefinition("BitwiseWidth.dll");
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Int32", TypeAttributes.Public));
        var owner = new TypeDefinition("Tests", "Mask", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il[0].OpCode, Is.EqualTo(CilOpCodes.Ldloc));
            Assert.That(il[1].OpCode, Is.EqualTo(CilOpCodes.Ldc_I8));
            Assert.That(il[2].OpCode, Is.EqualTo(CilOpCodes.Conv_I4));
            Assert.That(il[3].OpCode, Is.EqualTo(CilOpCodes.And));
            Assert.That(il[4].OpCode, Is.EqualTo(CilOpCodes.Stloc));
        });
    }

    [Test]
    public void CallArgumentWidensInt32LocalToInt64Parameter()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var arg = new LocalVariable("arg", new Register(null, "arg")) { Type = app.SystemTypes.SystemInt32Type };
        var target = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Take",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            [app.SystemTypes.SystemInt64Type]);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, target, arg),
            new(1, OpCode.Return)]);
        caller.Locals = [arg];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("ArgWiden.dll");
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Int32", TypeAttributes.Public));
        var type = new TypeDefinition("Tests", "ArgWiden", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var targetDefinition = new MethodDefinition("Take", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.Int64]));
        type.Methods.Add(targetDefinition);
        target.PutExtraData("AsmResolverMethod", targetDefinition);
        var definition = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(definition);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il[0].OpCode, Is.EqualTo(CilOpCodes.Ldloc));
            Assert.That(il[1].OpCode, Is.EqualTo(CilOpCodes.Conv_I8));
            Assert.That(il[2].OpCode, Is.EqualTo(CilOpCodes.Call));
        });
    }

    [Test]
    public void ObjectDestinationBoxesIntegerValue()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var source = new LocalVariable("source", new Register(null, "source")) { Type = app.SystemTypes.SystemInt32Type };
        var dest = new LocalVariable("dest", new Register(null, "dest")); // untyped
        // `dest` also flows to an object-typed call arg, which is boxing-compatible
        // and no longer disqualifies numeric inference: dest emits Int32 and the
        // box happens at the object-typed call site instead.
        var target = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Take",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            [app.SystemTypes.SystemObjectType]);
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, dest, source),
            new(1, OpCode.CallVoid, target, dest),
            new(2, OpCode.Return)]);
        context.Locals = [source, dest];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        var module = new ModuleDefinition("BoxMove.dll");
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Int32", TypeAttributes.Public));
        var owner = new TypeDefinition("Tests", "Box", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var takeDef = new MethodDefinition("Take", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.Object]));
        owner.Methods.Add(takeDef);
        target.PutExtraData("AsmResolverMethod", takeDef);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il[0].OpCode, Is.EqualTo(CilOpCodes.Ldloc));
            Assert.That(il[1].OpCode, Is.EqualTo(CilOpCodes.Stloc));
            Assert.That(il[2].OpCode, Is.EqualTo(CilOpCodes.Ldloc));
            Assert.That(il[3].OpCode, Is.EqualTo(CilOpCodes.Box));
            Assert.That(il[4].OpCode, Is.EqualTo(CilOpCodes.Call));
        });
    }

    [Test]
    public void CallUsesEmittedValueTypeReturnWhenAnalysisSaysObject()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemObjectType };
        var target = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Target",
            app.SystemTypes.SystemObjectType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            []);
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Call, target, result),
            new(1, OpCode.Return)]);
        context.Locals = [result];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("CallReturnBox.dll");
        var owner = new TypeDefinition("Tests", "Owner", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var targetDefinition = new MethodDefinition("Target", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Boolean));
        owner.Methods.Add(targetDefinition);
        target.PutExtraData("AsmResolverMethod", targetDefinition);
        var caller = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(caller);

        IlGenerator.GenerateIl(context, caller);

        Assert.That(caller.CilMethodBody!.Instructions.Any(instruction =>
            instruction.OpCode == CilOpCodes.Box
            && instruction.Operand?.ToString()?.Contains("Boolean") == true), Is.True,
            () => string.Join("\n", caller.CilMethodBody.Instructions));
    }

    [Test]
    public void ObjectArgumentBoxesBooleanWithoutTypeMapping()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var source = new LocalVariable("source", new Register(null, "source"))
            { Type = app.SystemTypes.SystemBooleanType };
        var target = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Take",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            [app.SystemTypes.SystemObjectType]);
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, target, source),
            new(1, OpCode.Return)]);
        context.Locals = [source];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("BoxBoolean.dll");
        var owner = new TypeDefinition("Tests", "BoxBoolean", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var take = new MethodDefinition("Take", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.Object]));
        owner.Methods.Add(take);
        target.PutExtraData("AsmResolverMethod", take);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        Assert.That(method.CilMethodBody!.Instructions.Any(instruction =>
            instruction.OpCode == CilOpCodes.Box
            && instruction.Operand?.ToString()?.Contains("Boolean") == true), Is.True,
            () => string.Join("\n", method.CilMethodBody.Instructions));
    }

    [Test]
    public void BoxIntoNativeIntSlotDropsReferenceAndStoresNativeDefault()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var source = new LocalVariable("source", new Register(null, "source"))
            { Type = app.SystemTypes.SystemInt32Type };
        var destination = new LocalVariable("destination", new Register(null, "destination"))
            { Type = app.SystemTypes.SystemIntPtrType };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Box, destination, app.SystemTypes.SystemInt32Type, source),
            new(1, OpCode.Return)]);
        context.Locals = [source, destination];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        var module = new ModuleDefinition("BoxNativeInt.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemIntPtrType, app.SystemTypes.SystemVoidType);
        var owner = new TypeDefinition("Tests", "Owner", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(instruction => instruction.OpCode == CilOpCodes.Box), Is.True);
            Assert.That(il.Any(instruction => instruction.OpCode == CilOpCodes.Pop), Is.True);
            Assert.That(il.Any(instruction => instruction.OpCode == CilOpCodes.Conv_I), Is.True);
            Assert.That(il.Any(instruction => instruction.OpCode == CilOpCodes.Stloc), Is.True);
        });
    }

    [Test]
    public void ReusedRegisterForOwnStructFieldStoreUsesThisReceiver()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var state = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "State",
            app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType"),
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Sealed
                | System.Reflection.TypeAttributes.SequentialLayout);
        var field = new InjectedFieldAnalysisContext("state", app.SystemTypes.SystemInt32Type,
            System.Reflection.FieldAttributes.Public, state, 0);
        state.Fields.Add(field);
        var self = new LocalVariable("this", new Register(null, "X0"), state) { IsThis = true };
        var reused = new LocalVariable("reused", new Register(null, "X1"))
            { Type = new SzArrayTypeAnalysisContext(app.SystemTypes.SystemInt32Type) };
        var value = new LocalVariable("value", new Register(null, "X2"))
            { Type = app.SystemTypes.SystemInt32Type };
        var context = new InjectedMethodAnalysisContext(state, "MoveNext", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, new FieldReference(field, reused, 0), value),
            new(1, OpCode.Return)]);
        context.Locals = [self, reused, value];
        context.ParameterLocals = [self];
        context.AnalysisWarnings = [];
        var module = new ModuleDefinition("StructThisStore.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemVoidType);
        var emittedState = new TypeDefinition("Tests", "State",
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(emittedState);
        state.PutExtraData("AsmResolverType", emittedState);
        var emittedField = new FieldDefinition("state", FieldAttributes.Public,
            new FieldSignature(module.CorLibTypeFactory.Int32));
        emittedState.Fields.Add(emittedField);
        field.PutExtraData("AsmResolverField", emittedField);
        var method = new MethodDefinition("MoveNext", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        emittedState.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        var stfld = method.CilMethodBody!.Instructions.ToList()
            .FindIndex(instruction => instruction.OpCode == CilOpCodes.Stfld);
        Assert.That(stfld, Is.GreaterThanOrEqualTo(2));
        Assert.That(method.CilMethodBody.Instructions[stfld - 2].OpCode, Is.EqualTo(CilOpCodes.Ldarg_0),
            () => string.Join("\n", method.CilMethodBody.Instructions));
    }

    [Test]
    public void ReturnNarrowsLongLocalToInt32ReturnType()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var value = new LocalVariable("value", new Register(null, "value")) { Type = app.SystemTypes.SystemInt64Type };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemInt32Type, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Return, value)]);
        context.Locals = [value];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        var module = new ModuleDefinition("RetNarrow.dll");
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Int32", TypeAttributes.Public));
        app.SystemTypes.SystemInt64Type.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Int64", TypeAttributes.Public));
        var owner = new TypeDefinition("Tests", "RetNarrow", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il[0].OpCode, Is.EqualTo(CilOpCodes.Ldloc));
            Assert.That(il[1].OpCode, Is.EqualTo(CilOpCodes.Conv_I4));
            Assert.That(il[2].OpCode, Is.EqualTo(CilOpCodes.Ret));
        });
    }

    [Test]
    public void MissingStructArgumentEmitsParameterlessConstructor()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "UnityEngine", "Vector3", app.SystemTypes.SystemValueTypeType, System.Reflection.TypeAttributes.Public);
        var target = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Place",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            [vector]);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, target),
            new(1, OpCode.Return)]);
        caller.Locals = [];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("StructArg.dll");
        var vectorDef = new TypeDefinition("UnityEngine", "Vector3",
            TypeAttributes.Public | TypeAttributes.SequentialLayout, module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(vectorDef);
        vector.PutExtraData("AsmResolverType", vectorDef);
        var owner = new TypeDefinition("Tests", "Place", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var targetDef = new MethodDefinition("Place", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [vectorDef.ToTypeSignature()]));
        owner.Methods.Add(targetDef);
        target.PutExtraData("AsmResolverMethod", targetDef);
        var definition = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(definition);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il[0].OpCode, Is.EqualTo(CilOpCodes.Ldloca));
            Assert.That(il[1].OpCode, Is.EqualTo(CilOpCodes.Initobj));
            Assert.That(il[2].OpCode, Is.EqualTo(CilOpCodes.Ldloc));
            Assert.That(il[3].OpCode, Is.EqualTo(CilOpCodes.Call));
        });
    }

    [Test]
    public void HiddenMethodInfoOperandDefaultsStructParameter()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "UnityEngine", "Vector3", app.SystemTypes.SystemValueTypeType, System.Reflection.TypeAttributes.Public);
        var target = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Place",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            [vector]);
        var hidden = new RuntimeMethodInfoAnalysisContext(target, app.SystemTypes.SystemObjectType.DeclaringAssembly);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, target, hidden),
            new(1, OpCode.Return)]);
        caller.Locals = [];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("HiddenArg.dll");
        var vectorDef = new TypeDefinition("UnityEngine", "Vector3",
            TypeAttributes.Public | TypeAttributes.SequentialLayout, module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(vectorDef);
        vector.PutExtraData("AsmResolverType", vectorDef);
        var owner = new TypeDefinition("Tests", "Place", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var targetDef = new MethodDefinition("Place", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [vectorDef.ToTypeSignature()]));
        owner.Methods.Add(targetDef);
        target.PutExtraData("AsmResolverMethod", targetDef);
        var definition = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(definition);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il[0].OpCode, Is.EqualTo(CilOpCodes.Ldloca));
            Assert.That(il[1].OpCode, Is.EqualTo(CilOpCodes.Initobj));
            Assert.That(il[2].OpCode, Is.EqualTo(CilOpCodes.Ldloc));
            Assert.That(il[3].OpCode, Is.EqualTo(CilOpCodes.Call));
        });
    }

    [Test]
    public void RuntimeClassOperandEmitsTypeOfForTypeParameter()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "UnityEngine", "Vector3", app.SystemTypes.SystemValueTypeType, System.Reflection.TypeAttributes.Public);
        var target = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Take",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            [app.SystemTypes.SystemTypeType]);
        var klass = new RuntimeClassTypeAnalysisContext(vector, app.SystemTypes.SystemObjectType.DeclaringAssembly);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, target, klass),
            new(1, OpCode.Return)]);
        caller.Locals = [];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("TypeArg.dll");
        var vectorDef = new TypeDefinition("UnityEngine", "Vector3",
            TypeAttributes.Public | TypeAttributes.SequentialLayout, module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(vectorDef);
        vector.PutExtraData("AsmResolverType", vectorDef);
        var owner = new TypeDefinition("Tests", "Take", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var targetDef = new MethodDefinition("Take", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
                [module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "Type").ToTypeSignature(true)]));
        owner.Methods.Add(targetDef);
        target.PutExtraData("AsmResolverMethod", targetDef);
        var definition = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(definition);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il[0].OpCode, Is.EqualTo(CilOpCodes.Ldtoken));
            Assert.That(il[1].OpCode, Is.EqualTo(CilOpCodes.Call));
            Assert.That(il[2].OpCode, Is.EqualTo(CilOpCodes.Call));
        });
    }

    [Test]
    public void MissingRefParameterEmitsAddressOfTempLocal()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var byRefInt = new ByRefTypeAnalysisContext(app.SystemTypes.SystemInt32Type);
        var target = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Take",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            [byRefInt]);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, target),
            new(1, OpCode.Return)]);
        caller.Locals = [];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("RefArg.dll");
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Int32", TypeAttributes.Public));
        var owner = new TypeDefinition("Tests", "Take", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var targetDef = new MethodDefinition("Take", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
                [new ByReferenceTypeSignature(module.CorLibTypeFactory.Int32)]));
        owner.Methods.Add(targetDef);
        target.PutExtraData("AsmResolverMethod", targetDef);
        var definition = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(definition);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il[0].OpCode, Is.EqualTo(CilOpCodes.Ldloca));
            Assert.That(il[1].OpCode, Is.EqualTo(CilOpCodes.Call));
        });
    }

    [Test]
    public void ImmediateInStructArgumentSlotEmitsDefaultOfStruct()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "UnityEngine", "Vector3", app.SystemTypes.SystemValueTypeType, System.Reflection.TypeAttributes.Public);
        var target = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Place",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            [vector]);
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, target, new Immediate(0)),
            new(1, OpCode.Return)]);
        caller.Locals = [];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("StructLit.dll");
        var vectorDef = new TypeDefinition("UnityEngine", "Vector3",
            TypeAttributes.Public | TypeAttributes.SequentialLayout, module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(vectorDef);
        vector.PutExtraData("AsmResolverType", vectorDef);
        var owner = new TypeDefinition("Tests", "Place", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var targetDef = new MethodDefinition("Place", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [vectorDef.ToTypeSignature()]));
        owner.Methods.Add(targetDef);
        target.PutExtraData("AsmResolverMethod", targetDef);
        var definition = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(definition);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il[0].OpCode, Is.EqualTo(CilOpCodes.Ldloca));
            Assert.That(il[1].OpCode, Is.EqualTo(CilOpCodes.Initobj));
            Assert.That(il[2].OpCode, Is.EqualTo(CilOpCodes.Ldloc));
            Assert.That(il[3].OpCode, Is.EqualTo(CilOpCodes.Call));
        });
    }

    private static void SeedCorLibTypes(ApplicationAnalysisContext app, ModuleDefinition module,
        params TypeAnalysisContext[] types)
    {
        foreach (var type in types)
        {
            var baseRef = type is { IsValueType: true }
                ? module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType")
                : null;
            type.PutExtraData("AsmResolverType",
                new TypeDefinition(type.Namespace, type.Name,
                    TypeAttributes.Public | (type.IsValueType ? TypeAttributes.Sealed | TypeAttributes.SequentialLayout : TypeAttributes.Class),
                    baseRef));
        }
    }

    private (MethodAnalysisContext caller, MethodDefinition method) ForeignCaller(ApplicationAnalysisContext app,
        ModuleDefinition module, List<Instruction> instructions, List<LocalVariable> locals)
    {
        var callerType = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "ForeignCaller", app.SystemTypes.SystemObjectType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        var caller = callerType.InjectMethodContext("Run", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        caller.Locals = locals;
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var type = new TypeDefinition("Tests", "ForeignCaller", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);
        return (caller, method);
    }

    [Test]
    public void InlinedCorlibAddWithResizeCallRetargetsToPublicAdd()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var listDefinition = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var addWithResize = listDefinition.Methods.FirstOrDefault(m => m.Name == "AddWithResize");
        Assert.That(addWithResize, Is.Not.Null, "2022 fixture corlib should expose List<T>.AddWithResize");
        Assert.That(addWithResize!.Attributes & ReflectionMethodAttributes.MemberAccessMask,
            Is.Not.EqualTo(ReflectionMethodAttributes.Public));
        var intType = app.SystemTypes.SystemInt32Type;
        var callee = new ConcreteGenericMethodAnalysisContext(addWithResize, [intType], []);
        var list = new LocalVariable("list", new Register(null, "list"))
            { Type = new GenericInstanceTypeAnalysisContext(listDefinition, [intType]) };
        var item = new LocalVariable("item", new Register(null, "item")) { Type = intType };
        var module = new ModuleDefinition("AddWithResize.dll");
        var listTypeDefinition = new TypeDefinition("System.Collections.Generic", "List`1",
            TypeAttributes.Public | TypeAttributes.Class);
        listTypeDefinition.GenericParameters.Add(new GenericParameter("T"));
        listDefinition.PutExtraData("AsmResolverType", listTypeDefinition);
        SeedCorLibTypes(app, module, intType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.CallVoid, callee, list, item),
            new(1, OpCode.Return)], [list, item]);

        IlGenerator.GenerateIl(caller, method);

        var calls = method.CilMethodBody!.Instructions
            .Where(i => i.OpCode == CilOpCodes.Call || i.OpCode == CilOpCodes.Callvirt).ToList();
        Assert.That(calls.Any(c => c.Operand is MemberReference { Name: { } name } && name.ToString() == "Add"), Is.True,
            () => string.Join("\n", method.CilMethodBody.Instructions.Select(i => i.ToString())));
        Assert.That(calls.Any(c => c.Operand?.ToString()?.Contains("AddWithResize") == true), Is.False);
    }

    [Test]
    public void InlinedCorlibAddWithResizeLdftnRetargetsToPublicAdd()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var listDefinition = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var addWithResize = listDefinition.Methods.FirstOrDefault(m => m.Name == "AddWithResize");
        Assert.That(addWithResize, Is.Not.Null);
        var intType = app.SystemTypes.SystemInt32Type;
        var callee = new ConcreteGenericMethodAnalysisContext(addWithResize!, [intType], []);
        var ptr = new LocalVariable("ptr", new Register(null, "ptr")) { Type = app.SystemTypes.SystemIntPtrType };
        var methodInfo = new RuntimeMethodInfoAnalysisContext(callee, app.AssembliesByName["UnityEngine.CoreModule"]);
        var module = new ModuleDefinition("AddWithResizeFtn.dll");
        var listTypeDefinition = new TypeDefinition("System.Collections.Generic", "List`1",
            TypeAttributes.Public | TypeAttributes.Class);
        listTypeDefinition.GenericParameters.Add(new GenericParameter("T"));
        listDefinition.PutExtraData("AsmResolverType", listTypeDefinition);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemIntPtrType,
            app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, ptr, methodInfo),
            new(1, OpCode.Return)], [ptr]);

        IlGenerator.GenerateIl(caller, method);

        var ldftn = method.CilMethodBody!.Instructions.Where(i => i.OpCode == CilOpCodes.Ldftn).ToList();
        Assert.That(ldftn, Has.Count.EqualTo(1));
        Assert.That(ldftn[0].Operand is MemberReference { Name: { } name } && name.ToString() == "Add", Is.True,
            $"expected ldftn of List<T>.Add, got {ldftn[0].Operand}");
    }

    [Test]
    public void PrivateCorlibThrowHelperCallEmitsDiagnosticStub()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var math = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Math")!;
        var throwMinMax = math.Methods.FirstOrDefault(m => m.Name == "ThrowMinMaxException");
        Assert.That(throwMinMax, Is.Not.Null);
        Assert.That(throwMinMax!.Attributes & ReflectionMethodAttributes.MemberAccessMask,
            Is.Not.EqualTo(ReflectionMethodAttributes.Public));
        var intType = app.SystemTypes.SystemInt32Type;
        var callee = new ConcreteGenericMethodAnalysisContext(throwMinMax, [], [intType]);
        var a = new LocalVariable("a", new Register(null, "a")) { Type = intType };
        var b = new LocalVariable("b", new Register(null, "b")) { Type = intType };
        var module = new ModuleDefinition("ThrowHelper.dll");
        SeedCorLibTypes(app, module, intType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.CallVoid, callee, a, b),
            new(1, OpCode.Return)], [a, b]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Throw), Is.True);
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Newobj), Is.True);
        Assert.That(il.Any(i => (i.OpCode == CilOpCodes.Call || i.OpCode == CilOpCodes.Callvirt
                || i.OpCode == CilOpCodes.Ldftn || i.OpCode == CilOpCodes.Newobj)
            && i.Operand?.ToString()?.Contains("ThrowMinMaxException") == true), Is.False);
    }

    [Test]
    public void PrivateCorlibThrowHelperLdftnEmitsNativeZero()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var math = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Math")!;
        var throwMinMax = math.Methods.FirstOrDefault(m => m.Name == "ThrowMinMaxException");
        Assert.That(throwMinMax, Is.Not.Null);
        var callee = new ConcreteGenericMethodAnalysisContext(throwMinMax!, [], [app.SystemTypes.SystemInt32Type]);
        var ptr = new LocalVariable("ptr", new Register(null, "ptr")) { Type = app.SystemTypes.SystemIntPtrType };
        var methodInfo = new RuntimeMethodInfoAnalysisContext(callee, app.AssembliesByName["UnityEngine.CoreModule"]);
        var module = new ModuleDefinition("ThrowHelperFtn.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemIntPtrType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, ptr, methodInfo),
            new(1, OpCode.Return)], [ptr]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldftn), Is.False);
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_I4_0), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Conv_I), Is.True);
        });
    }

    private static InjectedTypeAnalysisContext InjectedVector(ApplicationAnalysisContext app) =>
        new(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "UnityEngine", "Vector3", app.SystemTypes.SystemValueTypeType, System.Reflection.TypeAttributes.Public);

    private static TypeDefinition EmitVectorDefinition(ModuleDefinition module, TypeAnalysisContext vector)
    {
        var vectorDef = new TypeDefinition("UnityEngine", "Vector3",
            TypeAttributes.Public | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(vectorDef);
        vector.PutExtraData("AsmResolverType", vectorDef);
        return vectorDef;
    }

    [Test]
    public void IntLocalInStructArgumentSlotEmitsDefault()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = InjectedVector(app);
        var target = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Place",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            [vector]);
        var intLocal = new LocalVariable("i", new Register(null, "i")) { Type = app.SystemTypes.SystemInt32Type };
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, intLocal, new Immediate(3)),
            new(1, OpCode.CallVoid, target, intLocal),
            new(2, OpCode.Return)]);
        caller.Locals = [intLocal];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("StructArg.dll");
        var vectorDef = EmitVectorDefinition(module, vector);
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Int32", TypeAttributes.Public));
        var owner = new TypeDefinition("Tests", "Place", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var targetDef = new MethodDefinition("Place", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [vectorDef.ToTypeSignature()]));
        owner.Methods.Add(targetDef);
        target.PutExtraData("AsmResolverMethod", targetDef);
        var definition = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(definition);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        // The int local can never occupy the Vector3 slot; default(Vector3) is emitted instead.
        var callIndex = il.Select((i, idx) => (i, idx)).First(t => t.i.OpCode == CilOpCodes.Call).idx;
        Assert.Multiple(() =>
        {
            Assert.That(il[callIndex - 3].OpCode, Is.EqualTo(CilOpCodes.Ldloca));
            Assert.That(il[callIndex - 2].OpCode, Is.EqualTo(CilOpCodes.Initobj));
            Assert.That(il[callIndex - 1].OpCode, Is.EqualTo(CilOpCodes.Ldloc));
        });
    }

    [Test]
    public void IntLocalStoredIntoStructLocalEmitsDefault()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = InjectedVector(app);
        var vectorLocal = new LocalVariable("v", new Register(null, "v")) { Type = vector };
        var intLocal = new LocalVariable("i", new Register(null, "i")) { Type = app.SystemTypes.SystemInt32Type };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, vectorLocal, intLocal),
            new(1, OpCode.Return)]);
        context.Locals = [vectorLocal, intLocal];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        var module = new ModuleDefinition("StructStore.dll");
        EmitVectorDefinition(module, vector);
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Int32", TypeAttributes.Public));
        var owner = new TypeDefinition("Tests", "Run", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var definition = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(definition);

        IlGenerator.GenerateIl(context, definition);

        var il = definition.CilMethodBody!.Instructions;
        // stloc of an int into a Vector3 local is invalid; the store keeps default(Vector3).
        var stlocIndex = il.Select((i, idx) => (i, idx)).Last(t => t.i.OpCode == CilOpCodes.Stloc).idx;
        Assert.Multiple(() =>
        {
            Assert.That(il[stlocIndex - 3].OpCode, Is.EqualTo(CilOpCodes.Ldloca));
            Assert.That(il[stlocIndex - 2].OpCode, Is.EqualTo(CilOpCodes.Initobj));
            Assert.That(il[stlocIndex - 1].OpCode, Is.EqualTo(CilOpCodes.Ldloc));
            Assert.That(il[^1].OpCode, Is.EqualTo(CilOpCodes.Ret));
        });
    }

    [Test]
    public void ImmediateStoredThroughSimpleMemoryDestinationUsesBaseLocalContract()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = InjectedVector(app);
        var vectorLocal = new LocalVariable("v", new Register(null, "v")) { Type = vector };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, new MemoryOperand(vectorLocal), new Immediate(0)),
            new(1, OpCode.Return)]);
        context.Locals = [vectorLocal];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        var module = new ModuleDefinition("StructMemoryStore.dll");
        EmitVectorDefinition(module, vector);
        var owner = new TypeDefinition("Tests", "Run", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var definition = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(definition);

        IlGenerator.GenerateIl(context, definition);

        var il = definition.CilMethodBody!.Instructions;
        // [v] is a plain stloc into the Vector3 local, so the immediate must be default(Vector3).
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initobj), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_I4 || i.OpCode == CilOpCodes.Ldc_I4_0), Is.False);
            Assert.That(il[^2].OpCode, Is.EqualTo(CilOpCodes.Stloc));
            Assert.That(il[^1].OpCode, Is.EqualTo(CilOpCodes.Ret));
        });
    }

    [Test]
    public void StructComparedToZeroEmitsBoxedNullCheck()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = InjectedVector(app);
        var vectorLocal = new LocalVariable("v", new Register(null, "v")) { Type = vector };
        var result = new LocalVariable("r", new Register(null, "r")) { Type = app.SystemTypes.SystemBooleanType };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CheckEqual, result, vectorLocal, new Immediate(0)),
            new(1, OpCode.Return)]);
        context.Locals = [vectorLocal, result];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        var module = new ModuleDefinition("StructEq.dll");
        EmitVectorDefinition(module, vector);
        app.SystemTypes.SystemBooleanType.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Boolean", TypeAttributes.Public));
        var owner = new TypeDefinition("Tests", "Run", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var definition = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(definition);

        IlGenerator.GenerateIl(context, definition);

        var il = definition.CilMethodBody!.Instructions;
        // ceq cannot pair a Vector3 with an int; the honest form is the null test: box; ldnull; ceq.
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Box), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ceq), Is.True);
        });
    }

    [Test]
    public void PublicGenericCalleeOnVisibleInstantiationStaysDirect()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var listDefinition = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var intType = app.SystemTypes.SystemInt32Type;
        var add = listDefinition.Methods.First(m => m.Name == "Add" && m.Parameters.Count == 1);
        var callee = new ConcreteGenericMethodAnalysisContext(add, [intType], []);
        var list = new LocalVariable("list", new Register(null, "list"))
            { Type = new GenericInstanceTypeAnalysisContext(listDefinition, [intType]) };
        var item = new LocalVariable("item", new Register(null, "item")) { Type = intType };
        var module = new ModuleDefinition("VisibleAdd.dll");
        var listTypeDefinition = new TypeDefinition("System.Collections.Generic", "List`1",
            TypeAttributes.Public | TypeAttributes.Class);
        listTypeDefinition.GenericParameters.Add(new GenericParameter("T"));
        listDefinition.PutExtraData("AsmResolverType", listTypeDefinition);
        SeedCorLibTypes(app, module, intType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.CallVoid, callee, list, item),
            new(1, OpCode.Return)], [list, item]);

        IlGenerator.GenerateIl(caller, method);

        var calls = method.CilMethodBody!.Instructions
            .Where(i => i.OpCode == CilOpCodes.Call || i.OpCode == CilOpCodes.Callvirt).ToList();
        Assert.That(calls.Any(c => c.Operand is MemberReference { Name: { } name } && name.ToString() == "Add"), Is.True,
            () => string.Join("\n", method.CilMethodBody.Instructions.Select(i => i.ToString())));
        Assert.That(method.CilMethodBody.Instructions.Any(i => i.Operand is string s && s.Contains("Inaccessible callee")), Is.False);
    }

    [Test]
    public void PrivateGenericCalleeOnOwnTypeStaysDirect()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var listDefinition = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var addWithResize = listDefinition.Methods.FirstOrDefault(m => m.Name == "AddWithResize");
        Assert.That(addWithResize, Is.Not.Null);
        var intType = app.SystemTypes.SystemInt32Type;
        var callee = new ConcreteGenericMethodAnalysisContext(addWithResize!, [intType], []);
        // A method declared on List<T> itself may name its own private member.
        var caller = new InjectedMethodAnalysisContext(listDefinition, "Run", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        var list = new LocalVariable("list", new Register(null, "list"))
            { Type = new GenericInstanceTypeAnalysisContext(listDefinition, [intType]) };
        var item = new LocalVariable("item", new Register(null, "item")) { Type = intType };
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, callee, list, item),
            new(1, OpCode.Return)]);
        caller.Locals = [list, item];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("OwnPrivate.dll");
        var listTypeDefinition = new TypeDefinition("System.Collections.Generic", "List`1",
            TypeAttributes.Public | TypeAttributes.Class);
        listTypeDefinition.GenericParameters.Add(new GenericParameter("T"));
        listDefinition.PutExtraData("AsmResolverType", listTypeDefinition);
        SeedCorLibTypes(app, module, intType, app.SystemTypes.SystemVoidType);
        var type = new TypeDefinition("Tests", "OwnCaller", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(caller, method);

        var calls = method.CilMethodBody!.Instructions
            .Where(i => i.OpCode == CilOpCodes.Call || i.OpCode == CilOpCodes.Callvirt).ToList();
        Assert.That(calls.Any(c => c.Operand?.ToString()?.Contains("AddWithResize") == true), Is.True,
            () => string.Join("\n", method.CilMethodBody.Instructions.Select(i => i.ToString())));
    }

    [Test]
    public void MistypedStructReceiverLoadsMatchingEnumeratorAddress()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var enumerator = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Tests", "Enumerator", app.SystemTypes.SystemValueTypeType, System.Reflection.TypeAttributes.Public);
        var dispose = enumerator.InjectMethodContext("Dispose", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public);
        var enumeratorLocal = new LocalVariable("enumerator", new Register(null, "enumerator")) { Type = enumerator };
        var lostReceiver = new LocalVariable("lostReceiver", new Register(null, "lostReceiver"))
            { Type = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.NullReferenceException")! };
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, dispose, lostReceiver),
            new(1, OpCode.Return)]);
        caller.Locals = [enumeratorLocal, lostReceiver];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("StructReceiver.dll");
        var enumeratorDefinition = new TypeDefinition("Tests", "Enumerator",
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(enumeratorDefinition);
        enumerator.PutExtraData("AsmResolverType", enumeratorDefinition);
        var disposeDefinition = new MethodDefinition("Dispose", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        enumeratorDefinition.Methods.Add(disposeDefinition);
        dispose.PutExtraData("AsmResolverMethod", disposeDefinition);
        lostReceiver.Type!.PutExtraData("AsmResolverType", new TypeDefinition("System", "NullReferenceException",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type));
        var owner = new TypeDefinition("Tests", "Host", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var ldloca = il.Where(i => i.OpCode == CilOpCodes.Ldloca).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(ldloca, Has.Count.EqualTo(1));
            Assert.That(ldloca[0].Operand, Is.SameAs(method.CilMethodBody.LocalVariables[0]));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldloc), Is.False);
        });
    }

    [Test]
    public void MistypedStructReceiverWithoutMatchingLocalGetsFreshDefaultSlot()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var enumerator = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Tests", "Enumerator", app.SystemTypes.SystemValueTypeType, System.Reflection.TypeAttributes.Public);
        var moveNext = enumerator.InjectMethodContext("MoveNext", app.SystemTypes.SystemBooleanType,
            ReflectionMethodAttributes.Public);
        var lostReceiver = new LocalVariable("lostReceiver", new Register(null, "lostReceiver"))
            { Type = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.NullReferenceException")! };
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemBooleanType };
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Call, moveNext, result, lostReceiver),
            new(1, OpCode.Return)]);
        caller.Locals = [lostReceiver, result];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("StructReceiverDefault.dll");
        var enumeratorDefinition = new TypeDefinition("Tests", "Enumerator",
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(enumeratorDefinition);
        enumerator.PutExtraData("AsmResolverType", enumeratorDefinition);
        var moveNextDefinition = new MethodDefinition("MoveNext", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Boolean));
        enumeratorDefinition.Methods.Add(moveNextDefinition);
        moveNext.PutExtraData("AsmResolverMethod", moveNextDefinition);
        lostReceiver.Type!.PutExtraData("AsmResolverType", new TypeDefinition("System", "NullReferenceException",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type));
        var owner = new TypeDefinition("Tests", "Host", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var ldloca = il.Where(i => i.OpCode == CilOpCodes.Ldloca).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(method.CilMethodBody.LocalVariables, Has.Count.EqualTo(3));
            Assert.That(ldloca, Has.Count.EqualTo(1));
            Assert.That(ldloca[0].Operand, Is.SameAs(method.CilMethodBody.LocalVariables[2]));
            Assert.That(method.CilMethodBody.LocalVariables[2].VariableType.FullName, Is.EqualTo("Tests.Enumerator"));
        });
    }

    [Test]
    public void OrderingCompareOnStructEmitsDefaultBool()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = InjectedVector(app);
        var vectorLocal = new LocalVariable("v", new Register(null, "v")) { Type = vector };
        var result = new LocalVariable("r", new Register(null, "r")) { Type = app.SystemTypes.SystemBooleanType };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CheckLess, result, vectorLocal, new Immediate(1)),
            new(1, OpCode.Return)]);
        context.Locals = [vectorLocal, result];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        var module = new ModuleDefinition("StructLt.dll");
        EmitVectorDefinition(module, vector);
        app.SystemTypes.SystemBooleanType.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Boolean", TypeAttributes.Public));
        var owner = new TypeDefinition("Tests", "Run", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var definition = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(definition);

        IlGenerator.GenerateIl(context, definition);

        var il = definition.CilMethodBody!.Instructions;
        // Ordering on a struct has no answer; emit the honest diagnostic throw,
        // never a clt on Vector3.
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Clt), Is.False);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Throw), Is.True);
        });
    }

    [Test]
    public void MoveFromUnbridgeableTypeToStructSlotEmitsDefaultValue()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "UnityEngine", "Vector3", app.SystemTypes.SystemValueTypeType, System.Reflection.TypeAttributes.Public);
        var destination = new LocalVariable("destination", new Register(null, "destination")) { Type = vector };
        var source = new LocalVariable("source", new Register(null, "source"))
            { Type = app.SystemTypes.SystemInt32Type };
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, destination, source),
            new(1, OpCode.Return)]);
        caller.Locals = [destination, source];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("UnbridgeableMove.dll");
        var vectorDefinition = new TypeDefinition("UnityEngine", "Vector3",
            TypeAttributes.Public | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(vectorDefinition);
        vector.PutExtraData("AsmResolverType", vectorDefinition);
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType",
            new TypeDefinition("System", "Int32", TypeAttributes.Public));
        var owner = new TypeDefinition("Tests", "Host", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(method.CilMethodBody.LocalVariables, Has.Count.EqualTo(3));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldloca), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initobj), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stloc), Is.True);
        });
    }

    [Test]
    public void CallResultIntoStructLocalEmitsDefault()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = InjectedVector(app);
        var target = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Count",
            app.SystemTypes.SystemInt32Type, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            []);
        var vectorLocal = new LocalVariable("v", new Register(null, "v")) { Type = vector };
        var caller = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Caller",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Call, target, vectorLocal),
            new(1, OpCode.Return)]);
        caller.Locals = [vectorLocal];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("StructResult.dll");
        EmitVectorDefinition(module, vector);
        var owner = new TypeDefinition("Tests", "Place", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var targetDef = new MethodDefinition("Count", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32));
        owner.Methods.Add(targetDef);
        target.PutExtraData("AsmResolverMethod", targetDef);
        var definition = new MethodDefinition("Caller", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        owner.Methods.Add(definition);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        // The int return value cannot land in a Vector3 local: it is popped and the
        // store keeps default(Vector3).
        var stlocIndex = il.Select((i, idx) => (i, idx)).Last(t => t.i.OpCode == CilOpCodes.Stloc).idx;
        Assert.Multiple(() =>
        {
            Assert.That(il[stlocIndex - 4].OpCode, Is.EqualTo(CilOpCodes.Pop));
            Assert.That(il[stlocIndex - 3].OpCode, Is.EqualTo(CilOpCodes.Ldloca));
            Assert.That(il[stlocIndex - 2].OpCode, Is.EqualTo(CilOpCodes.Initobj));
            Assert.That(il[stlocIndex - 1].OpCode, Is.EqualTo(CilOpCodes.Ldloc));
            Assert.That(il[^1].OpCode, Is.EqualTo(CilOpCodes.Ret));
        });
    }

    // IL2CPP's shared-generic lowering instantiates generic code over internal
    // corlib marker types (System.Int32Enum and friends) that managed callers can
    // never name. The fixture's own corlib carries them, so these tests assert the
    // generator never fabricates a token that references the marker: the emitted
    // member/type references are checked for the marker's name, and locals that
    // carried it must be declared as a visible placeholder.

    private static TypeAnalysisContext SeedInternalEnumMarker(ApplicationAnalysisContext app, ModuleDefinition module)
    {
        var marker = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Int32Enum");
        Assert.That(marker, Is.Not.Null, "2022 fixture corlib should expose the shared-generic enum markers");
        Assert.That(marker!.IsValueType && marker.IsEnumType, Is.True);
        Assert.That(marker.Visibility, Is.EqualTo(System.Reflection.TypeAttributes.NotPublic));
        marker.PutExtraData("AsmResolverType", new TypeDefinition(marker.Namespace, marker.Name,
            TypeAttributes.NotPublic | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType")));
        return marker;
    }

    private static TypeDefinition SeedGenericListDefinition(TypeAnalysisContext listDefinition)
    {
        var typeDefinition = new TypeDefinition("System.Collections.Generic", "List`1",
            TypeAttributes.Public | TypeAttributes.Class);
        typeDefinition.GenericParameters.Add(new GenericParameter("T"));
        listDefinition.PutExtraData("AsmResolverType", typeDefinition);
        return typeDefinition;
    }

    [TestCase(false)]
    [TestCase(true)]
    public void ErasedGenericAllocationUsesConcreteFieldStoreContract(bool nested)
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var listDefinition = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var parameterless = listDefinition.Methods.First(m => m.Name == ".ctor" && m.Parameters.Count == 0);
        TypeAnalysisContext erasedArgument = app.SystemTypes.SystemObjectType;
        TypeAnalysisContext concreteArgument = app.SystemTypes.SystemStringType;
        if (nested)
        {
            erasedArgument = new GenericInstanceTypeAnalysisContext(listDefinition, [erasedArgument]);
            concreteArgument = new GenericInstanceTypeAnalysisContext(listDefinition, [concreteArgument]);
        }
        var erasedType = new GenericInstanceTypeAnalysisContext(listDefinition, [erasedArgument]);
        var concreteType = new GenericInstanceTypeAnalysisContext(listDefinition, [concreteArgument]);
        var erasedCtor = new ConcreteGenericMethodAnalysisContext(parameterless, [erasedArgument], []);
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Owner", app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var field = owner.InjectFieldContext("Items", concreteType,
            System.Reflection.FieldAttributes.Public | System.Reflection.FieldAttributes.Static);
        var temporary = new LocalVariable("temporary", new Register(null, "temporary")) { Type = erasedType };
        var caller = owner.InjectMethodContext("Create", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Newobj, temporary, erasedType),
            new(1, OpCode.CallVoid, erasedCtor, temporary),
            new(2, OpCode.Move, new FieldReference(field, temporary, 0), temporary),
            new(3, OpCode.Return)]);
        caller.Locals = [temporary];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];

        var module = new ModuleDefinition("ConcreteGenericStore.dll");
        var listTypeDefinition = SeedGenericListDefinition(listDefinition);
        module.TopLevelTypes.Add(listTypeDefinition);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemStringType);
        var ctorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        listTypeDefinition.Methods.Add(ctorDefinition);
        parameterless.PutExtraData("AsmResolverMethod", ctorDefinition);
        var ownerDefinition = new TypeDefinition("Tests", "Owner", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(ownerDefinition);
        owner.PutExtraData("AsmResolverType", ownerDefinition);
        var fieldDefinition = new FieldDefinition("Items", FieldAttributes.Public | FieldAttributes.Static,
            new FieldSignature(concreteType.ToTypeSignature()));
        ownerDefinition.Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        var method = new MethodDefinition("Create", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        ownerDefinition.Methods.Add(method);

        IlGenerator.GenerateIl(caller, method);

        Assert.Multiple(() =>
        {
            Assert.That(method.CilMethodBody!.LocalVariables[0].VariableType.FullName,
                Does.Contain("System.String"));
            Assert.That(method.CilMethodBody.Instructions.Any(i => i.OpCode == CilOpCodes.Castclass), Is.False);
            Assert.That(method.CilMethodBody.Instructions.Single(i => i.OpCode == CilOpCodes.Newobj)
                .Operand!.ToString(), Does.Contain("System.String"));
        });
    }

    [Test]
    public void ObjectAllocationUsesConcreteCastContract()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var widget = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Widget", app.SystemTypes.SystemObjectType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        var widgetCtor = widget.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public);
        var objectCtor = app.SystemTypes.SystemObjectType.Methods
            .First(method => method.Name == ".ctor" && method.Parameters.Count == 0);
        var temporary = new LocalVariable("temporary", new Register(null, "temporary"))
            { Type = app.SystemTypes.SystemObjectType };
        var result = new LocalVariable("result", new Register(null, "result")) { Type = widget };
        var caller = widget.InjectMethodContext("Create", widget,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Newobj, temporary, app.SystemTypes.SystemObjectType),
            new(1, OpCode.CallVoid, objectCtor, temporary),
            new(2, OpCode.Move, result, new ReferenceCast(temporary, widget)),
            new(3, OpCode.Return, result)]);
        caller.Locals = [temporary, result];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];

        var module = new ModuleDefinition("ConcreteObjectStore.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var objectCtorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        app.SystemTypes.SystemObjectType.GetExtraData<TypeDefinition>("AsmResolverType")!
            .Methods.Add(objectCtorDefinition);
        objectCtor.PutExtraData("AsmResolverMethod", objectCtorDefinition);
        var widgetDefinition = new TypeDefinition("Tests", "Widget",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(widgetDefinition);
        widget.PutExtraData("AsmResolverType", widgetDefinition);
        var ctorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        widgetDefinition.Methods.Add(ctorDefinition);
        widgetCtor.PutExtraData("AsmResolverMethod", ctorDefinition);
        var method = new MethodDefinition("Create", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(widget.ToTypeSignature()));
        widgetDefinition.Methods.Add(method);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(method.CilMethodBody.LocalVariables[0].VariableType.FullName, Does.Contain("Tests.Widget"));
            Assert.That(il.Any(instruction => instruction.OpCode == CilOpCodes.Castclass), Is.False);
            Assert.That(il.Single(instruction => instruction.OpCode == CilOpCodes.Newobj).Operand!.ToString(),
                Does.Contain("Tests.Widget"));
        });
    }

    [Test]
    public void InlinedConcreteConstructorGetsBareAllocationShell()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var widget = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Widget", app.SystemTypes.SystemObjectType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        var objectCtor = app.SystemTypes.SystemObjectType.Methods
            .First(method => method.Name == ".ctor" && method.Parameters.Count == 0);
        var widgetCtor = widget.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemInt32Type);
        var temporary = new LocalVariable("temporary", new Register(null, "temporary")) { Type = widget };
        var caller = widget.InjectMethodContext("Create", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Newobj, temporary, widget),
            new(1, OpCode.CallVoid, objectCtor, temporary),
            new(2, OpCode.Return)]);
        caller.Locals = [temporary];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];

        var module = new ModuleDefinition("BareAllocation.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemVoidType);
        var objectCtorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        app.SystemTypes.SystemObjectType.GetExtraData<TypeDefinition>("AsmResolverType")!
            .Methods.Add(objectCtorDefinition);
        objectCtor.PutExtraData("AsmResolverMethod", objectCtorDefinition);
        var widgetDefinition = new TypeDefinition("Tests", "Widget",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(widgetDefinition);
        widget.PutExtraData("AsmResolverType", widgetDefinition);
        var originalCtor = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void,
                [module.CorLibTypeFactory.Int32, module.CorLibTypeFactory.Int32]));
        widgetDefinition.Methods.Add(originalCtor);
        widgetCtor.PutExtraData("AsmResolverMethod", originalCtor);
        var method = new MethodDefinition("Create", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        widgetDefinition.Methods.Add(method);

        IlGenerator.GenerateIl(caller, method);

        Assert.Multiple(() =>
        {
            Assert.That(widgetDefinition.Methods.Count(candidate =>
                candidate.Name == ".ctor" && candidate.Signature?.ParameterTypes.Count == 0), Is.EqualTo(1));
            Assert.That(method.CilMethodBody!.Instructions.Single(instruction => instruction.OpCode == CilOpCodes.Newobj)
                .Operand!.ToString(), Does.Contain("Tests.Widget::.ctor()"));
            Assert.That(method.CilMethodBody.Instructions.Any(instruction => instruction.OpCode == CilOpCodes.Castclass), Is.False);
        });
    }

    [Test]
    public void ObjectAllocationUsesConcreteReturnContractThroughAlias()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var widget = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Widget", app.SystemTypes.SystemObjectType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Class);
        var widgetCtor = widget.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public);
        var objectCtor = app.SystemTypes.SystemObjectType.Methods
            .First(method => method.Name == ".ctor" && method.Parameters.Count == 0);
        var temporary = new LocalVariable("temporary", new Register(null, "temporary"))
            { Type = app.SystemTypes.SystemObjectType };
        var alias = new LocalVariable("alias", new Register(null, "alias"))
            { Type = app.SystemTypes.SystemObjectType };
        var caller = widget.InjectMethodContext("Create", widget,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Newobj, temporary, app.SystemTypes.SystemObjectType),
            new(1, OpCode.CallVoid, objectCtor, temporary),
            new(2, OpCode.Move, alias, temporary),
            new(3, OpCode.Return, alias)]);
        caller.Locals = [temporary, alias];
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];

        var module = new ModuleDefinition("ConcreteObjectReturn.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var objectCtorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        app.SystemTypes.SystemObjectType.GetExtraData<TypeDefinition>("AsmResolverType")!
            .Methods.Add(objectCtorDefinition);
        objectCtor.PutExtraData("AsmResolverMethod", objectCtorDefinition);
        var widgetDefinition = new TypeDefinition("Tests", "Widget",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(widgetDefinition);
        widget.PutExtraData("AsmResolverType", widgetDefinition);
        var ctorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        widgetDefinition.Methods.Add(ctorDefinition);
        widgetCtor.PutExtraData("AsmResolverMethod", ctorDefinition);
        var method = new MethodDefinition("Create", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(widget.ToTypeSignature()));
        widgetDefinition.Methods.Add(method);

        IlGenerator.GenerateIl(caller, method);

        Assert.That(method.CilMethodBody!.Instructions.Single(instruction => instruction.OpCode == CilOpCodes.Newobj)
            .Operand!.ToString(), Does.Contain("Tests.Widget"));
    }

    private static IEnumerable<CilInstruction> TokenInstructions(MethodDefinition method) =>
        method.CilMethodBody!.Instructions.Where(i => i.OpCode.OperandType
            is CilOperandType.InlineMethod or CilOperandType.InlineType
            or CilOperandType.InlineField or CilOperandType.InlineTok);

    private static void AssertNoTokenNamesMarker(MethodDefinition method, string markerName = "Int32Enum")
    {
        Assert.That(TokenInstructions(method).All(i => i.Operand?.ToString()?.Contains(markerName) != true),
            Is.True, () => string.Join("\n", method.CilMethodBody!.Instructions.Select(i => i.ToString())));
        Assert.That(method.CilMethodBody!.LocalVariables.All(l => l.VariableType?.FullName?.Contains(markerName) != true),
            Is.True, "a local must not be declared with the invisible marker type");
    }

    [Test]
    public void CallOnSharedGenericOverInternalMarkerEmitsDiagnosticStub()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var listDefinition = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var add = listDefinition.Methods.FirstOrDefault(m => m.Name == "Add" && !m.IsStatic && m.Parameters.Count == 1);
        Assert.That(add, Is.Not.Null);
        var module = new ModuleDefinition("MarkerAdd.dll");
        var markerType = SeedInternalEnumMarker(app, module);
        SeedGenericListDefinition(listDefinition);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemVoidType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType);
        var callee = new ConcreteGenericMethodAnalysisContext(add!, [markerType], []);
        var listType = new GenericInstanceTypeAnalysisContext(listDefinition, [markerType]);
        var list = new LocalVariable("list", new Register(null, "list")) { Type = listType };
        var item = new LocalVariable("item", new Register(null, "item")) { Type = markerType };
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.CallVoid, callee, list, item),
            new(1, OpCode.Return)], [list, item]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Throw), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call && i.Operand?.ToString()?.Contains("Add") == true),
                Is.False, "List<Int32Enum>::Add cannot be named by the caller");
        });
        AssertNoTokenNamesMarker(method);
    }

    [Test]
    public void AddWithResizeOverInternalMarkerDoesNotSubstitute()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var listDefinition = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var addWithResize = listDefinition.Methods.FirstOrDefault(m => m.Name == "AddWithResize");
        Assert.That(addWithResize, Is.Not.Null, "2022 fixture corlib should expose List<T>.AddWithResize");
        var module = new ModuleDefinition("MarkerAddWithResize.dll");
        var markerType = SeedInternalEnumMarker(app, module);
        SeedGenericListDefinition(listDefinition);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemVoidType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType);
        var callee = new ConcreteGenericMethodAnalysisContext(addWithResize!, [markerType], []);
        var listType = new GenericInstanceTypeAnalysisContext(listDefinition, [markerType]);
        var list = new LocalVariable("list", new Register(null, "list")) { Type = listType };
        var item = new LocalVariable("item", new Register(null, "item")) { Type = markerType };
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.CallVoid, callee, list, item),
            new(1, OpCode.Return)], [list, item]);

        IlGenerator.GenerateIl(caller, method);

        // The honest substitute List<T>.Add exists, but over the marker it is just
        // as unnameable - the substitution must not resurrect the same violation.
        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Throw), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call && i.Operand?.ToString()?.Contains("Add") == true),
                Is.False, "neither AddWithResize nor the Add substitute may be named");
        });
        AssertNoTokenNamesMarker(method);
    }

    [Test]
    public void SharedGenericMethodArgumentOverInternalMarkerEmitsDiagnosticStub()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var activator = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Activator")!;
        var createInstance = activator.Methods.FirstOrDefault(m =>
            m.Name == "CreateInstance" && m.GenericParameters.Count == 1 && m.Parameters.Count == 0);
        Assert.That(createInstance, Is.Not.Null, "2022 fixture corlib should expose Activator.CreateInstance<T>()");
        var module = new ModuleDefinition("MarkerCreateInstance.dll");
        var markerType = SeedInternalEnumMarker(app, module);
        SeedCorLibTypes(app, module, activator, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemObjectType);
        var callee = new ConcreteGenericMethodAnalysisContext(createInstance!, [], [markerType]);
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemObjectType };
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Call, callee, result),
            new(1, OpCode.Return)], [result]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Throw), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call && i.Operand?.ToString()?.Contains("CreateInstance") == true),
                Is.False, "CreateInstance<Int32Enum> cannot be named by the caller");
        });
        AssertNoTokenNamesMarker(method);
    }

    [Test]
    public void NewobjOnSharedGenericOverInternalMarkerEmitsDiagnosticStub()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var listDefinition = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var parameterless = listDefinition.Methods.FirstOrDefault(m =>
            m.Name == ".ctor" && m.Parameters.Count == 0);
        Assert.That(parameterless, Is.Not.Null);
        var module = new ModuleDefinition("MarkerCtor.dll");
        var markerType = SeedInternalEnumMarker(app, module);
        SeedGenericListDefinition(listDefinition);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemVoidType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType);
        var ctor = new ConcreteGenericMethodAnalysisContext(parameterless!, [markerType], []);
        var listType = new GenericInstanceTypeAnalysisContext(listDefinition, [markerType]);
        var list = new LocalVariable("list", new Register(null, "list")) { Type = listType };
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Newobj, list),
            new(1, OpCode.CallVoid, ctor, list),
            new(2, OpCode.Return)], [list]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Throw), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Newobj && i.Operand?.ToString()?.Contains("List") == true),
                Is.False, "newobj List<Int32Enum>::.ctor cannot be named by the caller");
        });
        AssertNoTokenNamesMarker(method);
    }

    [Test]
    public void CastToSharedGenericOverInternalMarkerEmitsDefault()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var listDefinition = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var module = new ModuleDefinition("MarkerCast.dll");
        var markerType = SeedInternalEnumMarker(app, module);
        SeedGenericListDefinition(listDefinition);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemVoidType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType);
        var listType = new GenericInstanceTypeAnalysisContext(listDefinition, [markerType]);
        var source = new LocalVariable("source", new Register(null, "source"))
            { Type = app.SystemTypes.SystemObjectType };
        var cast = new LocalVariable("cast", new Register(null, "cast")) { Type = listType };
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, cast, new ReferenceCast(source, listType)),
            new(1, OpCode.Return)], [source, cast]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Castclass), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.True,
                "the honest value of an unnameable cast is a default of the slot");
        });
        AssertNoTokenNamesMarker(method);
    }

    [Test]
    public void NewArrOverInternalMarkerEmitsDefault()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("MarkerArray.dll");
        var markerType = SeedInternalEnumMarker(app, module);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemVoidType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType);
        var arrayType = new SzArrayTypeAnalysisContext(markerType);
        var array = new LocalVariable("array", new Register(null, "array")) { Type = arrayType };
        var length = new LocalVariable("length", new Register(null, "length"))
            { Type = app.SystemTypes.SystemInt32Type };
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.NewArr, array, arrayType, length),
            new(1, OpCode.Return)], [array, length]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Newarr), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.True,
                "the honest value of an unnameable array is a default of the slot");
        });
        AssertNoTokenNamesMarker(method);
    }
}
