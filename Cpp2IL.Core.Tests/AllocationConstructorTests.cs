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
    public void InlinedReadonlyFieldInitializationRestoresConcreteConstructorCall()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Tests", "Owner", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var allocated = new InjectedTypeAnalysisContext(owner.DeclaringAssembly, "Tests", "Item",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var field = allocated.InjectFieldContext("_config", app.SystemTypes.SystemStringType,
            R.FieldAttributes.Private | R.FieldAttributes.InitOnly);
        var constructor = allocated.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public, app.SystemTypes.SystemStringType);
        var baseConstructor = new NativeCtor(app.SystemTypes.SystemObjectType, 0x2000);
        var result = new LocalVariable("result", new Register(null, "result"), app.SystemTypes.SystemObjectType);
        var config = new LocalVariable("config", new Register(null, "config"), app.SystemTypes.SystemStringType);
        var caller = new InjectedMethodAnalysisContext(owner, "Create", app.SystemTypes.SystemObjectType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, [app.SystemTypes.SystemStringType]);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Newobj, result, allocated),
            new(1, OpCode.CallVoid, baseConstructor, result),
            new(2, OpCode.Move, new FieldReference(field, result, 16), config),
            new(3, OpCode.Return, result)]);
        caller.Locals = [result, config];
        caller.ParameterLocals = [config];
        caller.AnalysisWarnings = [];

        var module = new ModuleDefinition("InlinedReadonlyCtor.dll");
        var ownerDefinition = new TypeDefinition("Tests", "Owner", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        var itemDefinition = new TypeDefinition("Tests", "Item", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        var objectDefinition = new TypeDefinition("System", "Object", TypeAttributes.Public);
        var stringDefinition = new TypeDefinition("System", "String", TypeAttributes.Public);
        module.TopLevelTypes.Add(ownerDefinition);
        module.TopLevelTypes.Add(itemDefinition);
        module.TopLevelTypes.Add(objectDefinition);
        module.TopLevelTypes.Add(stringDefinition);
        var baseDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        objectDefinition.Methods.Add(baseDefinition);
        var constructorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.String]));
        itemDefinition.Methods.Add(constructorDefinition);
        var fieldDefinition = new FieldDefinition("_config", FieldAttributes.Private | FieldAttributes.InitOnly,
            new FieldSignature(module.CorLibTypeFactory.String));
        itemDefinition.Fields.Add(fieldDefinition);
        owner.PutExtraData("AsmResolverType", ownerDefinition);
        allocated.PutExtraData("AsmResolverType", itemDefinition);
        app.SystemTypes.SystemObjectType.PutExtraData("AsmResolverType", objectDefinition);
        app.SystemTypes.SystemStringType.PutExtraData("AsmResolverType", stringDefinition);
        constructor.PutExtraData("AsmResolverMethod", constructorDefinition);
        baseConstructor.PutExtraData("AsmResolverMethod", baseDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);
        var definition = new MethodDefinition("Create", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Object, [module.CorLibTypeFactory.String]));
        definition.ParameterDefinitions.Add(new ParameterDefinition(1, "config", 0));
        ownerDefinition.Methods.Add(definition);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Single(instruction => instruction.OpCode == CilOpCodes.Newobj).Operand,
                Is.SameAs(constructorDefinition));
            Assert.That(il.Any(instruction => instruction.OpCode == CilOpCodes.Stfld), Is.False);
        });
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
        // A `call` to a reference-type .ctor on a foreign receiver is not legal IL;
        // the re-init is emitted as newobj + store back to the receiver slot.
        Assert.Multiple(() =>
        {
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Newobj), Is.EqualTo(2));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call && i.Operand == ctorDefinition), Is.False);
        });
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

    private static (InjectedTypeAnalysisContext GrandBase, InjectedTypeAnalysisContext Base,
        InjectedTypeAnalysisContext Derived, NativeCtor DistantCtor, NativeCtor BaseCtor,
        NativeCtor Context, LocalVariable This) ThisCtorFixture(ApplicationAnalysisContext app,
            int baseParameters = 0, int distantParameters = 0)
    {
        var assembly = app.SystemTypes.SystemObjectType.DeclaringAssembly;
        var grandBase = new InjectedTypeAnalysisContext(assembly, "Tests", "GrandBase",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var immediateBase = new InjectedTypeAnalysisContext(assembly, "Tests", "Base",
            grandBase, R.TypeAttributes.Public);
        var derived = new InjectedTypeAnalysisContext(assembly, "Tests", "Derived",
            immediateBase, R.TypeAttributes.Public);
        var parameterTypes = Enumerable.Repeat(app.SystemTypes.SystemInt32Type, Math.Max(baseParameters, distantParameters)).ToArray();
        var distantCtor = new NativeCtor(grandBase, 0x3000);
        foreach (var parameter in parameterTypes.Take(distantParameters))
            distantCtor.Parameters.Add(new InjectedParameterAnalysisContext(null, parameter, R.ParameterAttributes.None, distantCtor.Parameters.Count, distantCtor));
        var baseCtor = new NativeCtor(immediateBase, 0x2000);
        foreach (var parameter in parameterTypes.Take(baseParameters))
            baseCtor.Parameters.Add(new InjectedParameterAnalysisContext(null, parameter, R.ParameterAttributes.None, baseCtor.Parameters.Count, baseCtor));
        grandBase.Methods.Add(distantCtor);
        immediateBase.Methods.Add(baseCtor);
        var context = new NativeCtor(derived, 0x1000);
        var thisLocal = new LocalVariable("this", new Register(null, "this"), derived) { IsThis = true };
        context.Locals = [thisLocal];
        context.ParameterLocals = [thisLocal];
        context.AnalysisWarnings = [];
        return (grandBase, immediateBase, derived, distantCtor, baseCtor, context, thisLocal);
    }

    private static (MethodDefinition Distant, MethodDefinition Base, MethodDefinition Definition)
        ThisCtorDefinitions(ModuleDefinition module, InjectedTypeAnalysisContext grandBase,
            InjectedTypeAnalysisContext immediateBase, InjectedTypeAnalysisContext derived,
            NativeCtor distantCtor, NativeCtor baseCtor, NativeCtor context, int parameterCount)
    {
        var grandBaseType = new TypeDefinition("Tests", "GrandBase", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        var baseType = new TypeDefinition("Tests", "Base", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        var derivedType = new TypeDefinition("Tests", "Derived", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(grandBaseType);
        module.TopLevelTypes.Add(baseType);
        module.TopLevelTypes.Add(derivedType);
        var signature = MethodSignature.CreateInstance(module.CorLibTypeFactory.Void,
            Enumerable.Repeat(module.CorLibTypeFactory.Int32, parameterCount).ToArray());
        var distant = new MethodDefinition(".ctor", MethodAttributes.Public, signature);
        grandBaseType.Methods.Add(distant);
        var baseDefinition = new MethodDefinition(".ctor", MethodAttributes.Public, signature);
        baseType.Methods.Add(baseDefinition);
        var definition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        derivedType.Methods.Add(definition);
        grandBase.PutExtraData("AsmResolverType", grandBaseType);
        immediateBase.PutExtraData("AsmResolverType", baseType);
        derived.PutExtraData("AsmResolverType", derivedType);
        distantCtor.PutExtraData("AsmResolverMethod", distant);
        baseCtor.PutExtraData("AsmResolverMethod", baseDefinition);
        return (distant, baseDefinition, definition);
    }

    [Test]
    public void DistantParameterlessAncestorCallMovesImmediateBaseCallToPrologue()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var (grandBase, immediateBase, derived, distantCtor, baseCtor, context, thisLocal) = ThisCtorFixture(app);
        var field = derived.InjectFieldContext("level", app.SystemTypes.SystemInt32Type, R.FieldAttributes.Public);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, new FieldReference(field, thisLocal, 8), new Immediate(2)),
            new(1, OpCode.CallVoid, distantCtor, thisLocal),
            new(2, OpCode.Return)]);

        var module = new ModuleDefinition("ThisCtorPrologue.dll");
        var (distant, baseDefinition, definition) = ThisCtorDefinitions(module, grandBase,
            immediateBase, derived, distantCtor, baseCtor, context, 0);
        var fieldDefinition = new FieldDefinition("level", FieldAttributes.Public,
            new FieldSignature(module.CorLibTypeFactory.Int32));
        ((TypeDefinition)derived.GetExtraData<TypeDefinition>("AsmResolverType")!).Fields.Add(fieldDefinition);
        field.PutExtraData("AsmResolverField", fieldDefinition);

        IlGenerator.GenerateIl(context, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il[0].OpCode, Is.EqualTo(CilOpCodes.Ldarg_0));
            Assert.That(il[1].OpCode, Is.EqualTo(CilOpCodes.Call));
            Assert.That(il[1].Operand, Is.SameAs(baseDefinition));
            Assert.That(il.Any(i => i.Operand == distant), Is.False);
            Assert.That(il[^1].OpCode, Is.EqualTo(CilOpCodes.Ret));
        });
        // Base initialization now runs before the field store, matching managed order.
        Assert.That(il.Select(i => i.OpCode).ToList().IndexOf(CilOpCodes.Stfld),
            Is.GreaterThan(1));
    }

    [Test]
    public void DistantConstructorCallWithConstantArgumentsMovesToPrologue()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var (grandBase, immediateBase, derived, distantCtor, baseCtor, context, thisLocal) = ThisCtorFixture(app, 1, 1);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, distantCtor, thisLocal, new Immediate(5)),
            new(1, OpCode.Return)]);

        var module = new ModuleDefinition("ThisCtorArgPrologue.dll");
        var (distant, baseDefinition, definition) = ThisCtorDefinitions(module, grandBase,
            immediateBase, derived, distantCtor, baseCtor, context, 1);

        IlGenerator.GenerateIl(context, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il[0].OpCode, Is.EqualTo(CilOpCodes.Ldarg_0));
            Assert.That(il[1].OpCode, Is.EqualTo(CilOpCodes.Ldc_I4));
            Assert.That(il[1].Operand, Is.EqualTo(5));
            Assert.That(il[2].OpCode, Is.EqualTo(CilOpCodes.Call));
            Assert.That(il[2].Operand, Is.SameAs(baseDefinition));
            Assert.That(il.Any(i => i.Operand == distant), Is.False);
        });
    }

    [Test]
    public void DistantConstructorCallWithComputedArgumentsRetargetsInPlace()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var (grandBase, immediateBase, derived, distantCtor, baseCtor, context, thisLocal) = ThisCtorFixture(app, 1, 1);
        var computed = new LocalVariable("computed", new Register(null, "computed"), app.SystemTypes.SystemInt32Type);
        context.Locals.Add(computed);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, computed, new Immediate(5)),
            new(1, OpCode.CallVoid, distantCtor, thisLocal, computed),
            new(2, OpCode.Return)]);

        var module = new ModuleDefinition("ThisCtorArgInPlace.dll");
        var intType = new TypeDefinition("System", "Int32", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(intType);
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType", intType);
        var (distant, baseDefinition, definition) = ThisCtorDefinitions(module, grandBase,
            immediateBase, derived, distantCtor, baseCtor, context, 1);

        IlGenerator.GenerateIl(context, definition);

        var il = definition.CilMethodBody!.Instructions;
        var call = il.Single(i => i.OpCode == CilOpCodes.Call && i.Operand is MethodDefinition);
        Assert.Multiple(() =>
        {
            Assert.That(call.Operand, Is.SameAs(baseDefinition));
            Assert.That(il.Any(i => i.Operand == distant), Is.False);
            // The call stays at its original position: no prologue construction.
            Assert.That(il.IndexOf(call), Is.GreaterThan(2));
        });
    }

    [Test]
    public void DistantConstructorCallIsDroppedWhenOwnConstructorCallSurvives()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var (grandBase, immediateBase, derived, distantCtor, baseCtor, context, thisLocal) = ThisCtorFixture(app);
        var ownCtor = new NativeCtor(derived, 0x4000);
        ownCtor.Parameters.Add(new InjectedParameterAnalysisContext(null, app.SystemTypes.SystemInt32Type, R.ParameterAttributes.None, 0, ownCtor));
        derived.Methods.Add(ownCtor);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, ownCtor, thisLocal, new Immediate(3)),
            new(1, OpCode.CallVoid, distantCtor, thisLocal),
            new(2, OpCode.Return)]);

        var module = new ModuleDefinition("ThisCtorChain.dll");
        var (distant, baseDefinition, definition) = ThisCtorDefinitions(module, grandBase,
            immediateBase, derived, distantCtor, baseCtor, context, 0);
        var derivedType = (TypeDefinition)derived.GetExtraData<TypeDefinition>("AsmResolverType")!;
        var ownDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.Int32]));
        derivedType.Methods.Add(ownDefinition);
        ownCtor.PutExtraData("AsmResolverMethod", ownDefinition);

        IlGenerator.GenerateIl(context, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.Operand == ownDefinition), Is.True);
            Assert.That(il.Any(i => i.Operand == distant), Is.False);
            // The surviving own-constructor call already initializes `this`; no
            // additional base call is synthesized.
            Assert.That(il.Any(i => i.Operand == baseDefinition), Is.False);
        });
    }

    [Test]
    public void DistantConstructorCallWithoutSignatureMatchRetargetsToAccessibleBaseCtor()
    {
        // FeatureGroupDebugUI shape: IL2CPP inlined the whole base chain, so the
        // surviving call is the parameterless grandparent .ctor while the immediate
        // base only offers .ctor(int32). No signature match exists; the emitted call
        // must still initialize `this` through the accessible immediate-base .ctor.
        var app = Cpp2IlApi.CurrentAppContext!;
        var (grandBase, immediateBase, derived, distantCtor, baseCtor, context, thisLocal) = ThisCtorFixture(app, 1, 0);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, distantCtor, thisLocal),
            new(1, OpCode.Return)]);

        var module = new ModuleDefinition("ThisCtorNoMatch.dll");
        var (distant, _, definition) = ThisCtorDefinitions(module, grandBase,
            immediateBase, derived, distantCtor, baseCtor, context, 0);
        // The analysis base .ctor really takes an int32, so its AsmResolver
        // counterpart must too (ThisCtorDefinitions gave it the distant signature).
        var baseType = (TypeDefinition)immediateBase.GetExtraData<TypeDefinition>("AsmResolverType")!;
        baseType.Methods.Clear();
        var baseDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.Int32]));
        baseType.Methods.Add(baseDefinition);
        baseCtor.PutExtraData("AsmResolverMethod", baseDefinition);

        IlGenerator.GenerateIl(context, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call && i.Operand == distant), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            var call = il.Single(i => i.OpCode == CilOpCodes.Call && i.Operand is MethodDefinition);
            Assert.That(call.Operand, Is.SameAs(baseDefinition));
            // No matching parameter survived, so the slot is an honest default.
            Assert.That(il[il.IndexOf(call) - 1].OpCode, Is.EqualTo(CilOpCodes.Ldc_I4_0));
        });
    }

    [Test]
    public void DistantConstructorCallWithoutSameArityBaseCtorFallsBackToParameterless()
    {
        // Distant .ctor(int32) on `this`, but the immediate base only offers a
        // parameterless .ctor: same-arity keeps operand alignment, so without it the
        // parameterless base .ctor is the honest initialization and moves to the
        // prologue like any other parameterless replacement.
        var app = Cpp2IlApi.CurrentAppContext!;
        var (grandBase, immediateBase, derived, distantCtor, baseCtor, context, thisLocal) = ThisCtorFixture(app, 0, 1);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, distantCtor, thisLocal, new Immediate(7)),
            new(1, OpCode.Return)]);

        var module = new ModuleDefinition("ThisCtorArityMismatch.dll");
        var (distant, baseDefinition, definition) = ThisCtorDefinitions(module, grandBase,
            immediateBase, derived, distantCtor, baseCtor, context, 0);
        // distantCtor really takes an int32; give its definition that signature.
        var grandBaseType = (TypeDefinition)grandBase.GetExtraData<TypeDefinition>("AsmResolverType")!;
        grandBaseType.Methods.Clear();
        var realDistant = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.Int32]));
        grandBaseType.Methods.Add(realDistant);
        distantCtor.PutExtraData("AsmResolverMethod", realDistant);

        IlGenerator.GenerateIl(context, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.Operand == realDistant), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il[0].OpCode, Is.EqualTo(CilOpCodes.Ldarg_0));
            Assert.That(il[1].OpCode, Is.EqualTo(CilOpCodes.Call));
            Assert.That(il[1].Operand, Is.SameAs(baseDefinition));
        });
    }

    [Test]
    public void ConstructorCallOnThisOutsideConstructorBecomesNewobj()
    {
        // A `call` to a .ctor inside a non-.ctor method verifies on no receiver,
        // including `this` - IL2CPP re-initialization is emitted as newobj + store.
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.SystemTypes.SystemObjectType.DeclaringAssembly,
            "Tests", "Reinit", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var ctor = new NativeCtor(owner, 0x2000);
        owner.Methods.Add(ctor);
        var thisLocal = new LocalVariable("this", new Register(null, "this"), owner) { IsThis = true };
        var caller = new InjectedMethodAnalysisContext(owner, "Reset",
            app.SystemTypes.SystemVoidType, R.MethodAttributes.Public, []);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, ctor, thisLocal),
            new(1, OpCode.Return)]);
        caller.Locals = [thisLocal];
        caller.ParameterLocals = [thisLocal];
        caller.AnalysisWarnings = [];

        var module = new ModuleDefinition("Reinit.dll");
        var ownerType = new TypeDefinition("Tests", "Reinit", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(ownerType);
        var ctorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        ownerType.Methods.Add(ctorDefinition);
        owner.PutExtraData("AsmResolverType", ownerType);
        ctor.PutExtraData("AsmResolverMethod", ctorDefinition);
        var definition = new MethodDefinition("Reset", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        ownerType.Methods.Add(definition);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Newobj && i.Operand == ctorDefinition), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call && i.Operand == ctorDefinition), Is.False);
        });
    }

    // An abstract base type with a matching-arity derived type, wired for AsmResolver
    // emission. Mirrors the IL2CPP pattern where a derived .ctor's forwarding body is
    // inlined and the paired call ends up naming the abstract base .ctor.
    private static (InjectedTypeAnalysisContext AbstractBase, InjectedTypeAnalysisContext Derived,
        NativeCtor AbstractCtor, NativeCtor DerivedCtor, LocalVariable Result,
        InjectedMethodAnalysisContext Caller) AbstractAllocationFixture(ApplicationAnalysisContext app)
    {
        var assembly = app.SystemTypes.SystemObjectType.DeclaringAssembly;
        var abstractBase = new InjectedTypeAnalysisContext(assembly, "Tests", "AbstractBase",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Abstract);
        var derived = new InjectedTypeAnalysisContext(assembly, "Tests", "Derived",
            abstractBase, R.TypeAttributes.Public);
        var owner = new InjectedTypeAnalysisContext(assembly, "Tests", "Capture",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var abstractCtor = new NativeCtor(abstractBase, 0x2000);
        var derivedCtor = new NativeCtor(derived, 0x3000);
        abstractBase.Methods.Add(abstractCtor);
        derived.Methods.Add(derivedCtor);
        var result = new LocalVariable("result", new Register(null, "result"), abstractBase);
        var caller = new InjectedMethodAnalysisContext(owner, "Create", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        caller.Locals = [result]; caller.ParameterLocals = []; caller.AnalysisWarnings = [];
        return (abstractBase, derived, abstractCtor, derivedCtor, result, caller);
    }

    private static (MethodDefinition AbstractCtor, MethodDefinition DerivedCtor, MethodDefinition Caller)
        AbstractAllocationDefinitions(ModuleDefinition module, InjectedTypeAnalysisContext abstractBase,
            InjectedTypeAnalysisContext derived, NativeCtor abstractCtor, NativeCtor? derivedCtor,
            InjectedMethodAnalysisContext caller)
    {
        var abstractType = new TypeDefinition("Tests", "AbstractBase",
            TypeAttributes.Public | TypeAttributes.Abstract, module.CorLibTypeFactory.Object.Type);
        var derivedType = new TypeDefinition("Tests", "Derived", TypeAttributes.Public, abstractType);
        var captureType = new TypeDefinition("Tests", "Capture", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(abstractType);
        module.TopLevelTypes.Add(derivedType);
        module.TopLevelTypes.Add(captureType);
        var abstractCtorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        var derivedCtorDefinition = new MethodDefinition(".ctor", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        abstractType.Methods.Add(abstractCtorDefinition);
        derivedType.Methods.Add(derivedCtorDefinition);
        var definition = new MethodDefinition("Create", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        captureType.Methods.Add(definition);
        abstractBase.PutExtraData("AsmResolverType", abstractType);
        derived.PutExtraData("AsmResolverType", derivedType);
        abstractCtor.PutExtraData("AsmResolverMethod", abstractCtorDefinition);
        derivedCtor?.PutExtraData("AsmResolverMethod", derivedCtorDefinition);
        return (abstractCtorDefinition, derivedCtorDefinition, definition);
    }

    [Test]
    public void FusedAbstractConstructorReanchorsToTheAllocatedClassOperand()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var (abstractBase, derived, abstractCtor, derivedCtor, result, caller) = AbstractAllocationFixture(app);
        // object_new was invoked with the concrete class; the paired .ctor call resolved to
        // the abstract base (the derived .ctor's forwarding body was inlined).
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Newobj, result, derived),
            new(1, OpCode.CallVoid, abstractCtor, result),
            new(2, OpCode.Return)]);

        var module = new ModuleDefinition("AbstractFusedConcrete.dll");
        var (_, derivedCtorDefinition, definition) = AbstractAllocationDefinitions(module,
            abstractBase, derived, abstractCtor, derivedCtor, caller);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        var newobj = il.Single(i => i.OpCode == CilOpCodes.Newobj);
        Assert.That(newobj.Operand, Is.SameAs(derivedCtorDefinition));
    }

    [Test]
    public void FusedAbstractConstructorWithoutConcreteEvidenceEmitsNull()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var (abstractBase, derived, abstractCtor, _, result, caller) = AbstractAllocationFixture(app);
        // The class operand stayed an unresolved address and the destination local is typed
        // by the abstract base - no concrete type is provable, so no newobj may be emitted.
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Newobj, result, new Immediate(123)),
            new(1, OpCode.CallVoid, abstractCtor, result),
            new(2, OpCode.Return)]);

        var module = new ModuleDefinition("AbstractFusedNull.dll");
        var (_, _, definition) = AbstractAllocationDefinitions(module,
            abstractBase, derived, abstractCtor, null!, caller);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Newobj), Is.False);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.True);
        });
    }

    [Test]
    public void FusedAbstractConstructorWithoutSignatureMatchEmitsNull()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var (abstractBase, derived, abstractCtor, _, result, caller) = AbstractAllocationFixture(app);
        // The concrete type only declares a one-parameter .ctor, so the parameterless base
        // init cannot be re-anchored honestly (the real argument was consumed elsewhere).
        result.Type = derived;
        var derivedOnlyCtor = new NativeCtor(derived, 0x3000);
        derivedOnlyCtor.Parameters.Add(new InjectedParameterAnalysisContext(null,
            app.SystemTypes.SystemInt32Type, R.ParameterAttributes.None, 0, derivedOnlyCtor));
        derived.Methods.Clear();
        derived.Methods.Add(derivedOnlyCtor);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Newobj, result, derived),
            new(1, OpCode.CallVoid, abstractCtor, result),
            new(2, OpCode.Return)]);

        var module = new ModuleDefinition("AbstractFusedNoMatch.dll");
        var (_, _, definition) = AbstractAllocationDefinitions(module,
            abstractBase, derived, abstractCtor, null!, caller);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Newobj), Is.False);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.True);
        });
    }

    [Test]
    public void SelfContainedAbstractAllocationEmitsNull()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var (abstractBase, derived, abstractCtor, _, result, caller) = AbstractAllocationFixture(app);
        // No paired .ctor call: the allocation is self-contained but names an abstract type.
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Newobj, result, abstractBase),
            new(1, OpCode.Return)]);

        var module = new ModuleDefinition("AbstractBare.dll");
        var (_, _, definition) = AbstractAllocationDefinitions(module,
            abstractBase, derived, abstractCtor, null!, caller);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Newobj), Is.False);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.True);
        });
    }

    [Test]
    public void AbstractConstructorCallOnConcreteReceiverReanchors()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var (abstractBase, derived, abstractCtor, derivedCtor, _, caller) = AbstractAllocationFixture(app);
        // `call AbstractBase::.ctor(receiver)` on a non-this receiver is emitted as newobj +
        // store; the receiver's concrete type is the honest construction type.
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), derived);
        caller.Locals.Add(receiver);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, abstractCtor, receiver),
            new(1, OpCode.Return)]);

        var module = new ModuleDefinition("AbstractReinitConcrete.dll");
        var (_, derivedCtorDefinition, definition) = AbstractAllocationDefinitions(module,
            abstractBase, derived, abstractCtor, derivedCtor, caller);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        var newobj = il.Single(i => i.OpCode == CilOpCodes.Newobj);
        Assert.That(newobj.Operand, Is.SameAs(derivedCtorDefinition));
    }

    [Test]
    public void AbstractConstructorCallOnAbstractReceiverEmitsNull()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var (abstractBase, derived, abstractCtor, _, result, caller) = AbstractAllocationFixture(app);
        // The receiver is only known as the abstract base, so the re-init cannot be
        // reproduced as a newobj; the slot takes its default instead.
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, abstractCtor, result),
            new(1, OpCode.Return)]);

        var module = new ModuleDefinition("AbstractReinitNull.dll");
        var (_, _, definition) = AbstractAllocationDefinitions(module,
            abstractBase, derived, abstractCtor, null!, caller);

        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Newobj), Is.False);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldnull), Is.True);
        });
    }
}
