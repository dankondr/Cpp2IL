using System;
using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using ReflectionMethodAttributes = System.Reflection.MethodAttributes;

namespace Cpp2IL.Core.Tests;

public class IlGeneratorTests
{
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
    [TestCase(10, false, OpCode.CheckEqual, false)]
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
        Assert.That(instructions.Select(i => i.OpCode), Does.Contain(CilOpCodes.Ldc_R8));
        Assert.That(instructions.Select(i => i.OpCode), Does.Contain(CilOpCodes.Conv_R8));
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
        // A non-void signature with an empty return stack must not acquire a guessed bound.
        var method = new MethodDefinition("Invalid", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32));
        type.Methods.Add(method);
        IlGenerator.GenerateIl(caller, method);
        Assert.That(method.CilMethodBody!.Instructions[0].OpCode, Is.EqualTo(CilOpCodes.Ret));
        Assert.That(method.CilMethodBody.MaxStack, Is.EqualTo(0));
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
    [TestCase(false, false, false)] // direct base/virtual calls must remain direct
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
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == (!isStatic && (isInterface || virtualDispatch) ? CilOpCodes.Callvirt : CilOpCodes.Call) && i.Operand == targetDefinition), Is.True);
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
}
