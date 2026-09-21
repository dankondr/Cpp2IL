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

    [TestCase(false)]
    [TestCase(true)]
    public void InterfaceCallPreservesRuntimeDispatch(bool isStatic)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = app.SystemTypes.SystemObjectType;
        var iface = new InjectedTypeAnalysisContext(owner.DeclaringAssembly, "Tests", "IDispatch", null,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Interface | System.Reflection.TypeAttributes.Abstract);
        var target = iface.InjectMethodContext("Invoke", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | (isStatic ? ReflectionMethodAttributes.Static : ReflectionMethodAttributes.Abstract | ReflectionMethodAttributes.Virtual));
        var caller = new InjectedMethodAnalysisContext(owner, "Caller", app.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([isStatic ? new(0, OpCode.CallVoid, target) : new(0, OpCode.CallVoid, target, new Immediate(0)), new(1, OpCode.Return)]);
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
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == (isStatic ? CilOpCodes.Call : CilOpCodes.Callvirt) && i.Operand == targetDefinition), Is.True);
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
}
