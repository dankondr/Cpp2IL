using System;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests;

public class AllocationConstructorTests
{
    [SetUp] public void Setup() { Cpp2IlApi.ResetInternalState(); TestGameLoader.LoadSimple2019Game(); }

    private sealed class NativeCtor(TypeAnalysisContext owner, ulong address) : InjectedMethodAnalysisContext(owner, ".ctor", owner.AppContext.SystemTypes.SystemVoidType, R.MethodAttributes.Public, [])
    {
        public override ulong UnderlyingPointer => address;
    }

    [TestCase(0)]
    [TestCase(1)] // Extra or different native semantics must not be guessed.
    [TestCase(2)] // Abstract types cannot be allocated.
    [TestCase(3)] // Unknown allocation type.
    [TestCase(4)] // Ordinary base constructor call, no allocation evidence.
    [TestCase(5)] // Value types are outside this reference-allocation rule.
    [TestCase(6)] // Open generic allocation is not a concrete reference type.
    [TestCase(7)] // A thunk to another target is not equivalent initialization.
    public void InlinedObjectConstructorDoesNotAllocateObjectInsteadOfConcreteType(int kind)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        app.InstructionSet = new NewArmV8InstructionSet();
        var allocated = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly, "Tests", "Capture", kind == 5 ? app.SystemTypes.SystemValueTypeType : app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | (kind == 2 ? R.TypeAttributes.Abstract : 0));
        var baseCtor = new NativeCtor(app.SystemTypes.SystemObjectType, 0x2000);
        var ctor = new NativeCtor(allocated, 0x1000) { RawBytes = new BinarySlice([0xe1, 0x03, 0x1f, 0xaa, 0xff, 0x03, 0x00, 0x14]) };
        allocated.Methods.Add(ctor);
        if (kind == 1) ctor.RawBytes = new BinarySlice([0xe0, 0x03, 0x1f, 0xaa, 0xff, 0x03, 0x00, 0x14]); // clobbers receiver
        if (kind == 7) ctor.RawBytes = new BinarySlice([0xe1, 0x03, 0x1f, 0xaa, 0xfe, 0x03, 0x00, 0x14]);
        var caller = new InjectedMethodAnalysisContext(allocated, "Create", app.SystemTypes.SystemVoidType, R.MethodAttributes.Static, []);
        var result = new LocalVariable("result", new Register(null, "result"), allocated);
        var allocation = new Instruction(0, OpCode.Newobj, result, allocated);
        if (kind == 3) allocation.SetOperand(1, new Immediate(123));
        if (kind == 4) allocation = new Instruction(0, OpCode.CallVoid, baseCtor, result);
        if (kind == 6) allocation.SetOperand(1, app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!);
        if (kind != 0)
        {
            Assert.That(AllocationConstructorRecovery.Resolve(allocation, baseCtor), Is.Null);
            return;
        }
        caller.ControlFlowGraph = new ISILControlFlowGraph([allocation, new(1, OpCode.CallVoid, baseCtor, result), new(2, OpCode.Return)]);
        caller.Locals = [result]; caller.ParameterLocals = []; caller.AnalysisWarnings = [];
        var module = new ModuleDefinition("Allocation.dll");
        var type = new TypeDefinition("Tests", "Capture", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        var baseType = new TypeDefinition("System", "Object", TypeAttributes.Public);
        module.TopLevelTypes.Add(type); module.TopLevelTypes.Add(baseType);
        var baseDefinition = new MethodDefinition(".ctor", MethodAttributes.Public, MethodSignature.CreateInstance(module.CorLibTypeFactory.Void)); baseType.Methods.Add(baseDefinition);
        var ctorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public, MethodSignature.CreateInstance(module.CorLibTypeFactory.Void)); type.Methods.Add(ctorDefinition);
        allocated.PutExtraData("AsmResolverType", type); ctor.PutExtraData("AsmResolverMethod", ctorDefinition); baseCtor.PutExtraData("AsmResolverMethod", baseDefinition);
        var definition = new MethodDefinition("Create", MethodAttributes.Public | MethodAttributes.Static, MethodSignature.CreateStatic(module.CorLibTypeFactory.Void)); type.Methods.Add(definition);
        IlGenerator.GenerateIl(caller, definition);
        Assert.That(definition.CilMethodBody!.Instructions.Single(i => i.OpCode == CilOpCodes.Newobj).Operand, Is.SameAs(ctorDefinition));
    }

    [Test]
    public void ConstructorCallBeforeAllocationIsFusedForTheSameLocal()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly, "Tests", "Capture",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var allocated = new InjectedTypeAnalysisContext(owner.DeclaringAssembly, "Tests", "Item",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var ctor = new NativeCtor(allocated, 0x1000);
        allocated.Methods.Add(ctor);
        var result = new LocalVariable("result", new Register(null, "result"), allocated);
        var caller = new InjectedMethodAnalysisContext(owner, "Create", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, ctor, result),
            new(1, OpCode.Newobj, result, allocated),
            new(2, OpCode.Return)]);
        caller.Locals = [result]; caller.ParameterLocals = []; caller.AnalysisWarnings = [];

        var module = new ModuleDefinition("AllocationOrder.dll");
        var type = new TypeDefinition("Tests", "Capture", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var itemType = new TypeDefinition("Tests", "Item", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(itemType);
        var ctorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        itemType.Methods.Add(ctorDefinition);
        allocated.PutExtraData("AsmResolverType", itemType);
        ctor.PutExtraData("AsmResolverMethod", ctorDefinition);
        var definition = new MethodDefinition("Create", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(definition);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Newobj), Is.EqualTo(1));
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call && i.Operand == ctorDefinition), Is.False);
    }

    [Test]
    public void ConstructorCallForDifferentLocalIsNotFused()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly, "Tests", "Capture",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var allocated = new InjectedTypeAnalysisContext(owner.DeclaringAssembly, "Tests", "Item",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var ctor = new NativeCtor(allocated, 0x1000);
        allocated.Methods.Add(ctor);
        var result = new LocalVariable("result", new Register(null, "result"), allocated);
        var other = new LocalVariable("other", new Register(null, "other"), allocated);
        var caller = new InjectedMethodAnalysisContext(owner, "Create", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, ctor, other),
            new(1, OpCode.Newobj, result, allocated),
            new(2, OpCode.Return)]);
        caller.Locals = [result, other]; caller.ParameterLocals = []; caller.AnalysisWarnings = [];

        var module = new ModuleDefinition("AllocationOrderNegative.dll");
        var type = new TypeDefinition("Tests", "Capture", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var itemType = new TypeDefinition("Tests", "Item", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(itemType);
        var ctorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        itemType.Methods.Add(ctorDefinition);
        allocated.PutExtraData("AsmResolverType", itemType);
        ctor.PutExtraData("AsmResolverMethod", ctorDefinition);
        var definition = new MethodDefinition("Create", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(definition);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Newobj), Is.EqualTo(1));
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call && i.Operand == ctorDefinition), Is.True);
    }

    [Test]
    public void BranchTargetingFusedConstructorCallRemainsAddressable()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly, "Tests", "Capture",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var allocated = new InjectedTypeAnalysisContext(owner.DeclaringAssembly, "Tests", "Item",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var ctor = new NativeCtor(allocated, 0x1000);
        allocated.Methods.Add(ctor);
        var result = new LocalVariable("result", new Register(null, "result"), allocated);
        var call = new Instruction(1, OpCode.CallVoid, ctor, result);
        var caller = new InjectedMethodAnalysisContext(owner, "Create", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Jump, call), call,
            new(2, OpCode.Newobj, result, allocated),
            new(3, OpCode.Return)]);
        caller.Locals = [result]; caller.ParameterLocals = []; caller.AnalysisWarnings = [];

        var module = new ModuleDefinition("AllocationBranchTarget.dll");
        var type = new TypeDefinition("Tests", "Capture", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var itemType = new TypeDefinition("Tests", "Item", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(itemType);
        var ctorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        itemType.Methods.Add(ctorDefinition);
        allocated.PutExtraData("AsmResolverType", itemType);
        ctor.PutExtraData("AsmResolverMethod", ctorDefinition);
        var definition = new MethodDefinition("Create", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(definition);

        Assert.DoesNotThrow(() => IlGenerator.GenerateIl(caller, definition));
        var il = definition.CilMethodBody!.Instructions;
        var branches = il.Where(i => i.OpCode == CilOpCodes.Br || i.OpCode == CilOpCodes.Br_S).ToList();
        Assert.That(branches, Is.Not.Empty);
        foreach (var branch in branches)
        {
            var target = branch.Operand as CilInstructionLabel;
            Assert.That(target, Is.Not.Null);
            Assert.That(il, Does.Contain(target!.Instruction));
        }
    }
}
