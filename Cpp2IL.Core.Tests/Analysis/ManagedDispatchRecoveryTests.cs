using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using NUnit.Framework;
using ReflectionMethodAttributes = System.Reflection.MethodAttributes;
using ReflectionTypeAttributes = System.Reflection.TypeAttributes;

namespace Cpp2IL.Core.Tests.Analysis;

// End-to-end fixtures for indirect managed dispatch: the passes own the ISIL rewrite and the
// generated IL asserts prove the recovered target survives emission as a real callvirt/call.
// Every fixture mirrors the shapes ARM64 il2cpp actually emits:
//   - class virtual call:  [klass + 0x138 + slot*sizeof(VirtualInvokeData)] where klass = [obj]
//   - interface call:      phi of the inlined GetInterfaceInvokeData slow/fast paths
//   - delegate invoke:     [delegate + 0x18] (invoke_impl) with the frame's own field loads
//   - phi'd construction:  Newobj/.ctor operands that are phi-carried, cloned per merge edge
public class ManagedDispatchRecoveryTests
{
    private const long VTableOffset = 0x138;
    private const int InvokeDataSize = 16; // 2 * pointer size on 64-bit
    private const long InvokeImplOffset = 24;

    // The test game is a Windows x64 PE: MSVC raw argument order is rcx,rdx,r8,r9 then xmm0-3.
    private static readonly string[] IntRegisters = ["rcx", "rdx", "r8", "r9"];
    private static readonly string[] FloatRegisters = ["xmm0", "xmm1", "xmm2", "xmm3"];

    [SetUp] public void Setup() { Cpp2IlApi.ResetInternalState(); TestGameLoader.LoadSimple2019Game(); }

    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;
    private static TypeAnalysisContext CorLib(string name) =>
        App.AssembliesByName["mscorlib"].GetTypeByFullName(name)!;

    private static LocalVariable L(string name, TypeAnalysisContext? type = null)
        => new(name, new Register(null, name), type);

    private static MemoryOperand Load(IOperand @base, long addend) => new(@base, null, addend, 0);

    private static ISILControlFlowGraph BuildGraph(List<Instruction> instructions)
    {
        foreach (var instruction in instructions)
            if (instruction.OpCode is OpCode.Jump or OpCode.ConditionalJump)
                instruction.SetOperand(0, instructions[(int)((Immediate)instruction.Operands[0]).Value]);
        return new ISILControlFlowGraph(instructions.ToList());
    }

    private static InjectedMethodAnalysisContext Caller(TypeAnalysisContext returnType,
        List<Instruction> instructions, params LocalVariable[] parameterLocals)
    {
        var owner = new InjectedTypeAnalysisContext(App.AssembliesByName["mscorlib"], "Tests",
            "DispatchCaller", App.SystemTypes.SystemObjectType,
            ReflectionTypeAttributes.Public | ReflectionTypeAttributes.Class);
        var method = owner.InjectMethodContext("Run", returnType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            parameterLocals.Select(p => p.Type ?? App.SystemTypes.SystemObjectType).ToArray());
        method.ControlFlowGraph = BuildGraph(instructions);
        method.DominatorInfo = new DominatorInfo(method.ControlFlowGraph);
        method.Locals = instructions.SelectMany(i => i.Operands).OfType<LocalVariable>()
            .Concat(instructions.SelectMany(i => i.Operands).OfType<MemoryOperand>()
                .Select(m => m.Base).OfType<LocalVariable>())
            .Concat(instructions.Select(i => i.Destination).OfType<LocalVariable>())
            .Distinct().ToList();
        method.ParameterLocals = parameterLocals.ToList();
        method.AnalysisWarnings = [];
        return method;
    }

    private static MethodAnalysisContext Ctor(TypeAnalysisContext type) =>
        type.Methods.First(m => m.Name == ".ctor" && m.Parameters.Count == 0);

    // The vtable index a real metadata type implements `name` at, resolved the same way
    // the pass does (through the il2cpp VTable metadata usage entries).
    private static int VTableSlotOf(TypeAnalysisContext type, string name)
    {
        var definition = type.Definition!;
        for (var i = 0; i < definition.VtableCount; i++)
            if (App.ResolveContextForMethod(definition.VTable[i]) is { IsStatic: false } method
                && method.Name == name)
                return i;
        throw new InconclusiveException($"{type.FullName} has no {name} vtable entry");
    }

    private static int InterfaceSlotOf(TypeAnalysisContext iface, string name) =>
        iface.Methods.First(m => m.Name == name).Definition!.slot;

    private static MethodAnalysisContext? RootOf(MethodAnalysisContext method)
    {
        while (method.BaseMethod is { } baseMethod)
            method = baseMethod;
        return method;
    }

    // A slot at which two receiver types carry vtable entries whose root declarations differ:
    // the proof obligation the pass requires of every receiver candidate cannot be met.
    private static int AmbiguousSlot(TypeAnalysisContext first, TypeAnalysisContext second)
    {
        var firstVTable = first.Definition!.VTable;
        var secondVTable = second.Definition!.VTable;
        var count = System.Math.Min(first.Definition.VtableCount, second.Definition.VtableCount);
        for (var i = 0; i < count; i++)
        {
            var firstImpl = App.ResolveContextForMethod(firstVTable[i]);
            var secondImpl = App.ResolveContextForMethod(secondVTable[i]);
            if (firstImpl is not { IsStatic: false } || secondImpl is not { IsStatic: false })
                continue;
            var firstRoot = RootOf(firstImpl);
            var secondRoot = RootOf(secondImpl);
            if (firstRoot != null && secondRoot != null && !ReferenceEquals(firstRoot, secondRoot))
                return i;
        }
        throw new InconclusiveException(
            $"{first.FullName} and {second.FullName} never disagree on a vtable root");
    }

    private static void SeedDescriptor(MethodAnalysisContext method, ModuleDefinition module)
    {
        if (method.GetExtraData<MethodDefinition>("AsmResolverMethod") == null)
            method.PutExtraData("AsmResolverMethod", new MethodDefinition(method.Name,
                MethodAttributes.Public | MethodAttributes.Static,
                MethodSignature.CreateStatic(module.CorLibTypeFactory.Void)));
    }

    private static void SeedType(TypeAnalysisContext type)
    {
        if (type.GetExtraData<TypeDefinition>("AsmResolverType") == null)
            type.PutExtraData("AsmResolverType",
                new TypeDefinition(type.Namespace, type.Name, TypeAttributes.Public));
    }

    private static List<CilInstruction> Emitted(ApplicationAnalysisContext app,
        InjectedMethodAnalysisContext context, TypeAnalysisContext returnType)
    {
        var module = new ModuleDefinition("ManagedDispatch.dll");
        var callerType = new TypeDefinition("Tests", "DispatchCaller", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(callerType);

        SeedType(returnType);
        foreach (var type in context.Locals.Select(l => l.Type).Where(t => t != null))
            SeedType(type!);
        foreach (var callee in context.ControlFlowGraph!.Instructions
            .SelectMany(i => i.Operands).OfType<MethodAnalysisContext>())
            SeedDescriptor(callee, module);

        var emit = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(returnType.ToTypeSignature()));
        callerType.Methods.Add(emit);
        IlGenerator.GenerateIl(context, emit);
        return emit.CilMethodBody!.Instructions.ToList();
    }

    // ===== class virtual dispatch =====

    private static List<Instruction> VirtualDispatchShape(TypeAnalysisContext klass,
        LocalVariable receiver, LocalVariable result, long targetAddend,
        bool tail, List<Instruction> constructorPrologue)
    {
        var klassLocal = L("klass");
        var target = L("target");
        var methodInfo = L("methodInfo");
        var instructions = new List<Instruction>(constructorPrologue)
        {
            new(20, OpCode.Move, klassLocal, Load(receiver, 0)),
            new(21, OpCode.Move, target, Load(klassLocal, targetAddend)),
            new(22, OpCode.Move, methodInfo, Load(klassLocal, targetAddend + 8)),
        };
        if (tail)
            instructions.Add(new Instruction(23, OpCode.IndirectJump, target, L("stale"), receiver, methodInfo));
        else
            instructions.Add(new Instruction(23, OpCode.IndirectCall, target, result, receiver, methodInfo));
        instructions.Add(new Instruction(24, OpCode.Return, result));
        return instructions;
    }

    [Test]
    public void OverriddenVirtualDispatchResolvesToRootDeclaration()
    {
        var exception = CorLib("System.Exception");
        var str = CorLib("System.String");
        var slot = VTableSlotOf(exception, "ToString");
        var receiver = L("receiver", exception);
        var result = L("result", str);
        var ctor = Ctor(exception);
        var method = Caller(str, VirtualDispatchShape(exception, receiver, result,
            VTableOffset + slot * InvokeDataSize, tail: false,
            [new Instruction(0, OpCode.Newobj, receiver, exception),
             new Instruction(1, OpCode.CallVoid, ctor, receiver)]));

        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);
        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.Call));
        Assert.That(dispatch.IsVirtualDispatch, Is.True);
        var resolved = (MethodAnalysisContext)dispatch.Operands[0];
        Assert.That(resolved.Name, Is.EqualTo("ToString"));
        Assert.That(resolved.DeclaringType!.FullName, Is.EqualTo("System.Object"));

        var emitted = Emitted(App, method, str);
        Assert.That(emitted.Any(i => i.OpCode == CilOpCodes.Callvirt
            && i.Operand?.ToString()?.Contains("ToString") == true), Is.True,
            () => string.Join("\n", emitted));
    }

    [Test]
    public void VirtualTailDispatchResolvesTargetAndAppendsReturn()
    {
        var exception = CorLib("System.Exception");
        var int32 = App.SystemTypes.SystemInt32Type;
        var slot = VTableSlotOf(exception, "GetHashCode");
        var receiver = L("receiver", exception);
        var ctor = Ctor(exception);
        var instructions = VirtualDispatchShape(exception, receiver, L("result", int32),
            VTableOffset + slot * InvokeDataSize, tail: true,
            [new Instruction(0, OpCode.Newobj, receiver, exception),
             new Instruction(1, OpCode.CallVoid, ctor, receiver)]);
        instructions.RemoveAll(i => i.OpCode == OpCode.Return);
        var method = Caller(int32, instructions);
        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectJump);

        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.Call));
        var resolved = (MethodAnalysisContext)dispatch.Operands[0];
        Assert.That(resolved.Name, Is.EqualTo("GetHashCode"));
        Assert.That(resolved.DeclaringType!.FullName, Is.EqualTo("System.Object"));
        Assert.That(method.ControlFlowGraph.Instructions.Last().OpCode, Is.EqualTo(OpCode.Return));
        Assert.That(method.ControlFlowGraph.Instructions.Last().Operands[0],
            Is.SameAs(dispatch.Operands[1]));
    }

    [Test]
    public void PhiReceiverVirtualDispatchResolvesSharedRoot()
    {
        var exception = CorLib("System.Exception");
        var stream = CorLib("System.IO.MemoryStream");
        var str = CorLib("System.String");
        var slot = VTableSlotOf(exception, "ToString");
        var receiver = L("receiver");
        var alt = L("alt");
        var merged = L("merged");
        var klassLocal = L("klass");
        var target = L("target");
        var methodInfo = L("methodInfo");
        var result = L("result", str);
        var targetAddend = VTableOffset + slot * InvokeDataSize;
        var instructions = new List<Instruction>
        {
            new(0, OpCode.CheckNotEqual, L("cond"), L("selector"), new Immediate(0)),
            new(1, OpCode.ConditionalJump, new Immediate(5)),
            new(2, OpCode.Newobj, receiver, exception),
            new(3, OpCode.CallVoid, Ctor(exception), receiver),
            new(4, OpCode.Jump, new Immediate(8)),
            new(5, OpCode.Newobj, alt, stream),
            new(6, OpCode.CallVoid, Ctor(stream), alt),
            new(7, OpCode.Jump, new Immediate(8)),
            new(8, OpCode.Phi, merged, receiver, alt),
            new(9, OpCode.Move, klassLocal, Load(merged, 0)),
            new(10, OpCode.Move, target, Load(klassLocal, targetAddend)),
            new(11, OpCode.Move, methodInfo, Load(klassLocal, targetAddend + 8)),
            new(12, OpCode.IndirectCall, target, result, merged, methodInfo),
            new(13, OpCode.Return, result),
        };
        var method = Caller(str, instructions);
        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);

        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.Call));
        var resolved = (MethodAnalysisContext)dispatch.Operands[0];
        Assert.That(resolved.Name, Is.EqualTo("ToString"));
        Assert.That(resolved.DeclaringType!.FullName, Is.EqualTo("System.Object"));
    }

    [Test]
    public void AmbiguousVirtualSlotStaysIndirect()
    {
        var exception = CorLib("System.Exception");
        var stream = CorLib("System.IO.MemoryStream");
        var slot = AmbiguousSlot(exception, stream);
        var receiver = L("receiver");
        var alt = L("alt");
        var merged = L("merged");
        var klassLocal = L("klass");
        var target = L("target");
        var methodInfo = L("methodInfo");
        var result = L("result");
        var targetAddend = VTableOffset + slot * InvokeDataSize;
        var instructions = new List<Instruction>
        {
            new(0, OpCode.CheckNotEqual, L("cond"), L("selector"), new Immediate(0)),
            new(1, OpCode.ConditionalJump, new Immediate(5)),
            new(2, OpCode.Newobj, receiver, exception),
            new(3, OpCode.CallVoid, Ctor(exception), receiver),
            new(4, OpCode.Jump, new Immediate(8)),
            new(5, OpCode.Newobj, alt, stream),
            new(6, OpCode.CallVoid, Ctor(stream), alt),
            new(7, OpCode.Jump, new Immediate(8)),
            new(8, OpCode.Phi, merged, receiver, alt),
            new(9, OpCode.Move, klassLocal, Load(merged, 0)),
            new(10, OpCode.Move, target, Load(klassLocal, targetAddend)),
            new(11, OpCode.Move, methodInfo, Load(klassLocal, targetAddend + 8)),
            new(12, OpCode.IndirectCall, target, result, merged, methodInfo),
            new(13, OpCode.Return, result),
        };
        var method = Caller(App.SystemTypes.SystemObjectType, instructions);
        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);

        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.IndirectCall));
    }

    [Test]
    public void VirtualDispatchWithoutProvenMethodInfoStaysIndirect()
    {
        var exception = CorLib("System.Exception");
        var slot = VTableSlotOf(exception, "ToString");
        var receiver = L("receiver", exception);
        var result = L("result");
        var klassLocal = L("klass");
        var target = L("target");
        var methodInfo = L("methodInfo");
        var targetAddend = VTableOffset + slot * InvokeDataSize;
        // The hidden argument is a different address entirely - not methodPtr's sibling.
        var method = Caller(App.SystemTypes.SystemObjectType, [
            new Instruction(0, OpCode.Newobj, receiver, exception),
            new Instruction(1, OpCode.CallVoid, Ctor(exception), receiver),
            new Instruction(2, OpCode.Move, klassLocal, Load(receiver, 0)),
            new Instruction(3, OpCode.Move, target, Load(klassLocal, targetAddend)),
            new Instruction(4, OpCode.Move, methodInfo, Load(klassLocal, 0x900)),
            new Instruction(5, OpCode.IndirectCall, target, result, receiver, methodInfo),
            new Instruction(6, OpCode.Return, result)]);

        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);
        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.IndirectCall));
    }

    [Test]
    public void VirtualDispatchWithUnprovenReceiverStaysIndirect()
    {
        var exception = CorLib("System.Exception");
        var slot = VTableSlotOf(exception, "ToString");
        var receiver = L("receiver", App.SystemTypes.SystemObjectType); // plain object, no def
        var result = L("result");
        var klassLocal = L("klass");
        var target = L("target");
        var methodInfo = L("methodInfo");
        var targetAddend = VTableOffset + slot * InvokeDataSize;
        var method = Caller(App.SystemTypes.SystemObjectType, [
            new Instruction(0, OpCode.Move, klassLocal, Load(receiver, 0)),
            new Instruction(1, OpCode.Move, target, Load(klassLocal, targetAddend)),
            new Instruction(2, OpCode.Move, methodInfo, Load(klassLocal, targetAddend + 8)),
            new Instruction(3, OpCode.IndirectCall, target, result, receiver, methodInfo),
            new Instruction(4, OpCode.Return, result)], receiver);

        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);
        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.IndirectCall));
    }

    // ===== interface dispatch =====

    private static List<Instruction> InterfaceDispatchShape(TypeAnalysisContext declaringInterface,
        int slot, bool nonVoid)
    {
        var receiver = L("receiver", App.SystemTypes.SystemObjectType);
        var klassLocal = L("klass");
        var entry = L("entryOffset");
        var index = L("index");
        var extended = L("extended");
        var shifted = L("shifted");
        var sum = L("sum");
        var vtableEntry = L("vtableEntry");
        var slow = L("slow");
        var iface = L("iface");
        var slotArg = L("slot");
        var invokeData = L("invokeData");
        var target = L("target");
        var methodInfo = L("methodInfo");
        var result = L("result");
        return
        [
            // head: klass load + branch into the two inlined paths
            new Instruction(0, OpCode.Move, klassLocal, Load(receiver, 0)),
            new Instruction(1, OpCode.CheckNotEqual, L("cond"), receiver, new Immediate(0)),
            new Instruction(2, OpCode.ConditionalJump, new Immediate(3)),
            // fast path block (index 3): klass + (SXTW(entryOffset + slot) << 4) + 0x138
            new Instruction(3, OpCode.Move, entry, Load(klassLocal, 16)),
            new Instruction(4, OpCode.Add, index, entry, new Immediate(slot)),
            new Instruction(5, OpCode.SignExtend32, extended, index),
            new Instruction(6, OpCode.ShiftLeft, shifted, extended, new Immediate(4)),
            new Instruction(7, OpCode.Add, sum, klassLocal, shifted),
            new Instruction(8, OpCode.Add, vtableEntry, sum, new Immediate(VTableOffset)),
            new Instruction(9, OpCode.Jump, new Immediate(13)),
            // slow path block (index 10): GetInterfaceInvokeDataFromVTableSlowPath(obj, iface, slot)
            new Instruction(10, OpCode.Move, iface, declaringInterface),
            new Instruction(11, OpCode.Move, slotArg, new Immediate(slot)),
            new Instruction(12, OpCode.Call, new Immediate(0x9000), slow, receiver, iface, slotArg),
            // merge (index 13): phi over the two VirtualInvokeData pointers, then the call
            new Instruction(13, OpCode.Phi, invokeData, slow, vtableEntry),
            new Instruction(14, OpCode.Move, target, Load(invokeData, 0)),
            new Instruction(15, OpCode.Move, methodInfo, Load(invokeData, 8)),
            nonVoid
                ? new Instruction(16, OpCode.IndirectCall, target, result, receiver, methodInfo)
                : new Instruction(16, OpCode.IndirectCall, target, L("junk"), receiver, methodInfo),
            new Instruction(17, OpCode.Return, nonVoid ? result : L("unused")),
        ];
    }

    [Test]
    public void ExplicitInterfaceDispatchResolvesDeclaredSlot()
    {
        var disposable = CorLib("System.IDisposable");
        var slot = InterfaceSlotOf(disposable, "Dispose");
        var method = Caller(App.SystemTypes.SystemVoidType, InterfaceDispatchShape(disposable, slot, false));
        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);

        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.CallVoid));
        var resolved = (MethodAnalysisContext)dispatch.Operands[0];
        Assert.That(resolved.Name, Is.EqualTo("Dispose"));
        Assert.That(resolved.DeclaringType!.FullName, Is.EqualTo("System.IDisposable"));

        var emitted = Emitted(App, method, App.SystemTypes.SystemVoidType);
        Assert.That(emitted.Any(i => i.OpCode == CilOpCodes.Callvirt
            && i.Operand?.ToString()?.Contains("Dispose") == true), Is.True,
            () => string.Join("\n", emitted));
    }

    [Test]
    public void InterfaceDispatchResolvesInheritedSlot()
    {
        var enumerator = CorLib("System.Collections.IEnumerator");
        var slot = InterfaceSlotOf(enumerator, "get_Current");
        Assert.That(slot, Is.GreaterThan(0));
        var method = Caller(App.SystemTypes.SystemObjectType, InterfaceDispatchShape(enumerator, slot, true));
        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);

        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.Call));
        var resolved = (MethodAnalysisContext)dispatch.Operands[0];
        Assert.That(resolved.Name, Is.EqualTo("get_Current"));
        Assert.That(resolved.DeclaringType!.FullName, Is.EqualTo("System.Collections.IEnumerator"));
    }

    [Test]
    public void InterfaceDispatchExcisesLookupAfterDeadCopyChain()
    {
        var disposable = CorLib("System.IDisposable");
        var instructions = InterfaceDispatchShape(disposable, InterfaceSlotOf(disposable, "Dispose"), false);
        var dispatch = instructions.Single(instruction => instruction.OpCode == OpCode.IndirectCall);
        var targetCopy = L("targetCopy");
        instructions.Insert(instructions.IndexOf(dispatch),
            new Instruction(16, OpCode.Move, targetCopy, dispatch.Operands[0]));
        dispatch.SetOperand(0, targetCopy);
        var method = Caller(App.SystemTypes.SystemVoidType, instructions);

        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.CallVoid));
        Assert.That(method.ControlFlowGraph!.Instructions, Has.None.Matches<Instruction>(instruction =>
            instruction != null && instruction.IsCall && instruction.Operands.Count > 0
                && instruction.Operands[0] is Immediate { Value: 0x9000 }));
    }

    [Test]
    public void GenericInterfaceDispatchResolvesInstantiatedSlot()
    {
        var comparable = CorLib("System.IComparable`1")
            .MakeGenericInstanceType(App.SystemTypes.SystemInt32Type);
        var slot = InterfaceSlotOf(comparable.GenericType, "CompareTo");
        var method = Caller(App.SystemTypes.SystemInt32Type, InterfaceDispatchShape(comparable, slot, true));
        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);

        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.Call));
        var resolved = (ConcreteGenericMethodAnalysisContext)dispatch.Operands[0];
        Assert.That(resolved.BaseMethodContext.Name, Is.EqualTo("CompareTo"));
        Assert.That(resolved.TypeGenericParameters, Has.Count.EqualTo(1));
        Assert.That(resolved.TypeGenericParameters[0].FullName, Is.EqualTo("System.Int32"));
    }

    [Test]
    public void GenericVirtualHelperDispatchResolvesConcreteInterfaceMethod()
    {
        var disposable = CorLib("System.IDisposable");
        var dispose = disposable.Methods.First(method => method.Name == "Dispose");
        dispose.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0,
            LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_MVAR, 0, dispose));
        var concrete = dispose.MakeGenericInstanceMethod(App.SystemTypes.SystemInt32Type);
        var concreteInfo = new RuntimeMethodInfoAnalysisContext(concrete, disposable.DeclaringAssembly);
        var instructions = InterfaceDispatchShape(disposable, InterfaceSlotOf(disposable, "Dispose"), false);
        var declaredMethodInfo = L("declaredMethodInfo",
            new RuntimeMethodInfoAnalysisContext(dispose, disposable.DeclaringAssembly));
        instructions[4].SetOperand(2, Load(declaredMethodInfo, 0x50));
        instructions[10].SetOperand(1, Load(declaredMethodInfo, 0x20));
        instructions[11].SetOperand(1, Load(declaredMethodInfo, 0x50));
        var receiver = (LocalVariable)((MemoryOperand)instructions[0].Operands[1]).Base!;
        var openMethodInfo = (LocalVariable)instructions[15].Destination!;
        var inflatedMethodInfo = L("inflatedMethodInfo");
        var helper = new Instruction(16, OpCode.Call, new Immediate(0xA000), inflatedMethodInfo,
            openMethodInfo, concreteInfo);
        var dispatch = new Instruction(17, OpCode.IndirectCall,
            Load(inflatedMethodInfo, App.Binary.PointerSizeBytes), L("junk"), receiver, inflatedMethodInfo);
        instructions[16] = helper;
        instructions.Insert(17, dispatch);
        var method = Caller(App.SystemTypes.SystemVoidType, instructions);

        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.CallVoid));
        Assert.That(dispatch.Operands[0], Is.SameAs(concrete));
        Assert.That(method.ControlFlowGraph!.Instructions, Has.None.Matches<Instruction>(instruction =>
            instruction.IsCall && instruction.Operands[0] is Immediate { Value: 0xA000 }));
    }

    // ===== ARM64 folded-slot and out-param interface dispatch =====

    // Jump operands are list indices, so shapes built in parts resolve them at the end.
    private static void ResolveJumps(List<Instruction> instructions, params (Instruction jump, Instruction target)[] edges)
    {
        foreach (var (jump, target) in edges)
            jump.SetOperand(0, new Immediate(instructions.IndexOf(target)));
    }

    // ARM64 codegen folds a constant interface slot into the vtable base:
    //   klass + (SXTW(entryOffset) << 4) + (vtableOffset + slot * sizeof(VirtualInvokeData))
    // with no index-side +slot at all. indexAddsSlot double-counts the slot (must stay indirect),
    // foldedSlot lets a test mis-fold the addend (must also stay indirect).
    private static List<Instruction> FoldedSlotInterfaceShape(TypeAnalysisContext declaringInterface,
        int slowSlot, int foldedSlot, bool indexAddsSlot)
    {
        var receiver = L("receiver", App.SystemTypes.SystemObjectType);
        var klassLocal = L("klass");
        var entry = L("entryOffset");
        var index = L("index");
        var shifted = L("shifted");
        var sum = L("sum");
        var vtableEntry = L("vtableEntry");
        var slow = L("slow");
        var iface = L("iface");
        var slotArg = L("slot");
        var invokeData = L("invokeData");
        var target = L("target");
        var methodInfo = L("methodInfo");
        var result = L("result");
        var extended = L("extended");
        var branch = new Instruction(2, OpCode.ConditionalJump, new Immediate(0));
        var jump = new Instruction(0, OpCode.Jump, new Immediate(0));
        var merge = new Instruction(0, OpCode.Phi, invokeData, slow, vtableEntry);
        var slowBlock = new Instruction(10, OpCode.Move, iface, declaringInterface);
        var instructions = new List<Instruction>
        {
            // head: klass load + branch into the two inlined paths
            new Instruction(0, OpCode.Move, klassLocal, Load(receiver, 0)),
            new Instruction(1, OpCode.CheckNotEqual, L("cond"), receiver, new Immediate(0)),
            branch,
            // fast path block: klass + (SXTW(entryOffset) << 4) + 0x138+slot*16
            new Instruction(3, OpCode.Move, entry, Load(klassLocal, 16)),
        };
        if (indexAddsSlot)
            instructions.Add(new Instruction(4, OpCode.Add, index, entry, new Immediate(slowSlot)));
        instructions.Add(new Instruction(5, OpCode.SignExtend32, extended, indexAddsSlot ? index : entry));
        instructions.Add(new Instruction(6, OpCode.ShiftLeft, shifted, extended, new Immediate(4)));
        instructions.Add(new Instruction(7, OpCode.Add, sum, klassLocal, shifted));
        instructions.Add(new Instruction(8, OpCode.Add, vtableEntry, sum,
            new Immediate(VTableOffset + foldedSlot * InvokeDataSize)));
        instructions.Add(jump);
        instructions.Add(slowBlock);
        instructions.AddRange([
            new Instruction(11, OpCode.Move, slotArg, new Immediate(slowSlot)),
            new Instruction(12, OpCode.Call, new Immediate(0x9000), slow, receiver, iface, slotArg),
            // merge
            merge,
            new Instruction(14, OpCode.Move, target, Load(invokeData, 0)),
            new Instruction(15, OpCode.Move, methodInfo, Load(invokeData, 8)),
            new Instruction(16, OpCode.IndirectCall, target, result, receiver, methodInfo),
            new Instruction(17, OpCode.Return, result),
        ]);
        ResolveJumps(instructions, (branch, slowBlock), (jump, merge));
        return instructions;
    }

    [Test]
    public void FoldedSlotInterfaceDispatchResolvesDeclaredSlot()
    {
        var enumerator = CorLib("System.Collections.IEnumerator");
        var slot = InterfaceSlotOf(enumerator, "get_Current");
        Assert.That(slot, Is.GreaterThan(0));
        var method = Caller(App.SystemTypes.SystemObjectType,
            FoldedSlotInterfaceShape(enumerator, slot, slot, indexAddsSlot: false));
        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);

        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.Call));
        var resolved = (MethodAnalysisContext)dispatch.Operands[0];
        Assert.That(resolved.Name, Is.EqualTo("get_Current"));
        Assert.That(resolved.DeclaringType!.FullName, Is.EqualTo("System.Collections.IEnumerator"));

        var emitted = Emitted(App, method, App.SystemTypes.SystemObjectType);
        Assert.That(emitted.Any(i => i.OpCode == CilOpCodes.Callvirt
            && i.Operand?.ToString()?.Contains("get_Current") == true), Is.True,
            () => string.Join("\n", emitted));
        Assert.That(method.ControlFlowGraph.Instructions, Has.None.Matches<Instruction>(instruction =>
            instruction.IsCall && instruction.Operands.Count > 0
                && instruction.Operands[0] is Immediate { Value: 0x9000 }));
    }

    [Test]
    public void FoldedSlotInterfaceDispatchWithWrongFoldStaysIndirect()
    {
        var enumerator = CorLib("System.Collections.IEnumerator");
        var slot = InterfaceSlotOf(enumerator, "get_Current");
        var method = Caller(App.SystemTypes.SystemObjectType,
            FoldedSlotInterfaceShape(enumerator, slot, slot + 1, indexAddsSlot: false));
        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);

        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.IndirectCall));
    }

    [Test]
    public void FoldedSlotInterfaceDispatchWithSlotCountedTwiceStaysIndirect()
    {
        var enumerator = CorLib("System.Collections.IEnumerator");
        var slot = InterfaceSlotOf(enumerator, "get_Current");
        var method = Caller(App.SystemTypes.SystemObjectType,
            FoldedSlotInterfaceShape(enumerator, slot, slot, indexAddsSlot: true));
        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);

        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.IndirectCall));
    }

    // il2cpp_codegen_get_generic_interface_method takes a VirtualInvokeData* out-param:
    //   methodDef = [invokeData+8]; internal(methodDef, method, &stack[n]); blr [stack[n]]
    // The invokeData phi exists but never forms the call target's base.
    private static List<Instruction> OutParamInterfaceShape(TypeAnalysisContext declaringInterface,
        IOperand methodInfoOperand, bool withMethodDefLoad)
    {
        var receiver = L("receiver", App.SystemTypes.SystemObjectType);
        var methodMI = L("methodMI", new RuntimeMethodInfoAnalysisContext(
            declaringInterface.Methods.First(), declaringInterface.DeclaringAssembly));
        var klassLocal = L("klass");
        var ifaceK = L("ifaceK");
        var slotLoad = L("slotLoad");
        var entry = L("entryOffset");
        var index = L("index");
        var extended = L("extended");
        var shifted = L("shifted");
        var sum = L("sum");
        var vtableEntry = L("vtableEntry");
        var slow = L("slow");
        var invokeData = L("invokeData");
        var methodDef = L("methodDef");
        var buffer = L("buffer");
        var target = L("target");
        var methodInfo = L("methodInfo");
        var result = L("result");
        var branch = new Instruction(4, OpCode.ConditionalJump, new Immediate(0));
        var jump = new Instruction(11, OpCode.Jump, new Immediate(0));
        var slowBlock = new Instruction(12, OpCode.Call, new Immediate(0x9000),
            slow, receiver, ifaceK, slotLoad);
        var merge = new Instruction(13, OpCode.Phi, invokeData, slow, vtableEntry);
        var instructions = new List<Instruction>
        {
            // head: klass + the method->klass/method->slot loads the helper needs
            new Instruction(0, OpCode.Move, klassLocal, Load(receiver, 0)),
            new Instruction(1, OpCode.Move, ifaceK, Load(methodMI, 0x20)),
            new Instruction(2, OpCode.Move, slotLoad, Load(methodMI, 0x50)),
            new Instruction(3, OpCode.CheckNotEqual, L("cond"), receiver, new Immediate(0)),
            branch,
            // fast path: runtime slot, so the index add can't fold
            new Instruction(5, OpCode.Move, entry, Load(klassLocal, 16)),
            new Instruction(6, OpCode.Add, index, entry, slotLoad),
            new Instruction(7, OpCode.SignExtend32, extended, index),
            new Instruction(8, OpCode.ShiftLeft, shifted, extended, new Immediate(4)),
            new Instruction(9, OpCode.Add, sum, klassLocal, shifted),
            new Instruction(10, OpCode.Add, vtableEntry, sum, new Immediate(VTableOffset)),
            jump,
            // slow path
            slowBlock,
            // merge: phi'd invokeData feeds only the out-param helper
            merge,
        };
        if (withMethodDefLoad)
            instructions.Add(new Instruction(14, OpCode.Move, methodDef, Load(invokeData, 8)));
        instructions.Add(new Instruction(15, OpCode.Move, buffer, new AddressOf(new StackOffset(16))));
        instructions.Add(new Instruction(16, OpCode.Call, new Immediate(0xA000), L("helperResult"),
            withMethodDefLoad ? methodDef : L("unrelated"), methodInfoOperand, buffer));
        // the dispatch reads the stack buffer the helper just filled
        instructions.Add(new Instruction(17, OpCode.Move, target, new StackOffset(16)));
        instructions.Add(new Instruction(18, OpCode.Move, methodInfo, new StackOffset(24)));
        instructions.Add(new Instruction(19, OpCode.IndirectCall, target, result, receiver, methodInfo));
        instructions.Add(new Instruction(20, OpCode.Return, result));
        ResolveJumps(instructions, (branch, slowBlock), (jump, merge));
        return instructions;
    }

    [Test]
    public void OutParamGenericInterfaceDispatchResolvesConcreteMethod()
    {
        var disposable = CorLib("System.IDisposable");
        var dispose = disposable.Methods.First(method => method.Name == "Dispose");
        dispose.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0,
            LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_MVAR, 0, dispose));
        var concrete = dispose.MakeGenericInstanceMethod(App.SystemTypes.SystemInt32Type);
        var concreteInfo = new RuntimeMethodInfoAnalysisContext(concrete, disposable.DeclaringAssembly);
        var method = Caller(App.SystemTypes.SystemVoidType,
            OutParamInterfaceShape(disposable, concreteInfo, withMethodDefLoad: true));
        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);

        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.CallVoid));
        Assert.That(dispatch.Operands[0], Is.SameAs(concrete));
        // the invokeData out-param slot the helper filled is rewritten to the proven MethodInfo
        Assert.That(dispatch.Operands, Has.Some.Matches<IOperand>(operand =>
            operand is RuntimeMethodInfoAnalysisContext info
            && ReferenceEquals(info.RepresentedMethod, concrete)));
        Assert.That(method.ControlFlowGraph.Instructions, Has.None.Matches<Instruction>(instruction =>
            instruction.IsCall && instruction.Operands.Count > 0
                && instruction.Operands[0] is Immediate { Value: 0xA000 }));
    }

    [Test]
    public void OutParamDispatchWithoutMethodInfoStaysIndirect()
    {
        var disposable = CorLib("System.IDisposable");
        var method = Caller(App.SystemTypes.SystemVoidType,
            OutParamInterfaceShape(disposable, L("unrelatedMethodInfo"), withMethodDefLoad: true));
        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);

        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.IndirectCall));
    }

    [Test]
    public void OutParamDispatchForClassMethodStaysIndirect()
    {
        // the same helper shape, but the RuntimeMethod* names a class method, not an interface one
        var disposable = CorLib("System.IDisposable");
        var owner = new InjectedTypeAnalysisContext(App.AssembliesByName["mscorlib"], "Tests",
            "OutParamHelper", App.SystemTypes.SystemObjectType,
            ReflectionTypeAttributes.Public | ReflectionTypeAttributes.Class);
        var classMethod = owner.InjectMethodContext("Compute", App.SystemTypes.SystemInt32Type,
            ReflectionMethodAttributes.Public, App.SystemTypes.SystemObjectType);
        classMethod.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0,
            LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_MVAR, 0, classMethod));
        var concrete = classMethod.MakeGenericInstanceMethod(App.SystemTypes.SystemObjectType);
        var concreteInfo = new RuntimeMethodInfoAnalysisContext(concrete, owner.DeclaringAssembly);
        var method = Caller(App.SystemTypes.SystemVoidType,
            OutParamInterfaceShape(disposable, concreteInfo, withMethodDefLoad: true));
        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);

        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.IndirectCall));
    }

    [Test]
    public void OutParamDispatchWithoutInvokeDataLoadStaysIndirect()
    {
        var disposable = CorLib("System.IDisposable");
        var dispose = disposable.Methods.First(method => method.Name == "Dispose");
        dispose.GenericParameters.Add(new GenericParameterTypeAnalysisContext("T", 0,
            LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_MVAR, 0, dispose));
        var concrete = dispose.MakeGenericInstanceMethod(App.SystemTypes.SystemInt32Type);
        var concreteInfo = new RuntimeMethodInfoAnalysisContext(concrete, disposable.DeclaringAssembly);
        var method = Caller(App.SystemTypes.SystemVoidType,
            OutParamInterfaceShape(disposable, concreteInfo, withMethodDefLoad: false));
        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);

        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.IndirectCall));
    }

    // ===== ARM64 lookup excision with merged register phis =====

    // The real residual form (Castle, Unity 6000.0.72f1 arm64): beside the invokeData phi the
    // merge also phis the scan's scratch registers, and those phis plus the methodInfo load result
    // feed phis/arguments in later join blocks. Excising the lookup must redirect such uses to the
    // register version reaching the head - after excision the head is the merge's only
    // predecessor, so that is exactly the value the machine leaves in the register.
    private static LocalVariable V(string name, string register) => new(name, new Register(null, register));

    private static List<Instruction> MergedScratchPhiInterfaceShape(TypeAnalysisContext declaringInterface,
        int slot, bool reachablePreHead)
    {
        var receiver = L("receiver", App.SystemTypes.SystemObjectType);
        var klassLocal = L("klass");
        var entry = L("entryOffset");
        var index = L("index");
        var extended = L("extended");
        var shifted = L("shifted");
        var sum = L("sum");
        var vtableEntry = L("vtableEntry");
        var slow = L("slow");
        var iface = L("iface");
        var slotArg = L("slot");
        var invokeData = L("invokeData");
        var target = L("target");
        var keep = L("keep");
        var keep2 = L("keep2");
        var keep3 = L("keep3");
        var scratchFast = V("scratchFast", "scratch");
        var scratchSlow = V("scratchSlow", "scratch");
        var scratchPhi = V("scratchPhi", "scratch");
        var scratchJoin = V("scratchJoin", "scratch");
        var scratchPre = V("scratchPre", "scratch");
        var methodInfo = V("methodInfo", "x1");
        var x1Pre = V("x1Pre", "x1");
        var x1Join = V("x1Join", "x1");
        var arg2Slow = V("arg2Slow", "arg2");
        var arg2Phi = V("arg2Phi", "arg2");
        var arg2Pre = V("arg2Pre", "arg2");
        // register that is never defined before the lookup head, so no reaching version exists
        var orphanFast = V("orphanFast", "orphan");
        var orphanSlow = V("orphanSlow", "orphan");
        var orphanPhi = V("orphanPhi", "orphan");
        var argPhiInputs = reachablePreHead
            ? new List<IOperand> { arg2Phi, arg2Pre, arg2Slow }
            : new List<IOperand> { orphanPhi, orphanFast, orphanSlow };

        var skip = new Instruction(0, OpCode.ConditionalJump, new Immediate(0));
        var branch = new Instruction(0, OpCode.ConditionalJump, new Immediate(0));
        var jump = new Instruction(0, OpCode.Jump, new Immediate(0));
        var slowBlock = new Instruction(0, OpCode.Move, iface, declaringInterface);
        // the fast path jumps at the head of the merge block: all merge phis land there
        var firstMergePhi = new Instruction(0, OpCode.Phi, scratchPhi, scratchFast, scratchSlow);
        var mergePhi = new Instruction(0, OpCode.Phi, invokeData, slow, vtableEntry);
        var joinPhi = new Instruction(0, OpCode.Phi, scratchJoin, scratchPre, scratchPhi);

        var instructions = new List<Instruction>
        {
            // pre-dispatch block: fallthrough into the lookup head, or jump straight to the join
            new Instruction(0, OpCode.Move, scratchPre, new Immediate(0)),
            new Instruction(1, OpCode.Move, x1Pre, new Immediate(0)),
            new Instruction(2, OpCode.Move, arg2Pre, new Immediate(0)),
            skip,
            // head: klass load + branch into the two inlined paths
            new Instruction(4, OpCode.Move, klassLocal, Load(receiver, 0)),
            new Instruction(5, OpCode.CheckNotEqual, L("cond"), receiver, new Immediate(0)),
            branch,
            // fast path: klass + (SXTW(entryOffset + slot) << 4) + 0x138
            new Instruction(7, OpCode.Move, entry, Load(klassLocal, 16)),
            new Instruction(8, OpCode.Add, index, entry, new Immediate(slot)),
            new Instruction(9, OpCode.SignExtend32, extended, index),
            new Instruction(10, OpCode.ShiftLeft, shifted, extended, new Immediate(4)),
            new Instruction(11, OpCode.Add, sum, klassLocal, shifted),
            new Instruction(12, OpCode.Add, vtableEntry, sum, new Immediate(VTableOffset)),
            new Instruction(13, OpCode.Move, scratchFast, new Immediate(1)),
            new Instruction(14, OpCode.Move, orphanFast, new Immediate(1)),
            jump,
            // slow path
            slowBlock,
            new Instruction(16, OpCode.Move, slotArg, new Immediate(slot)),
            new Instruction(17, OpCode.Call, new Immediate(0x9000), slow, receiver, iface, slotArg),
            new Instruction(18, OpCode.Move, scratchSlow, new Immediate(2)),
            new Instruction(19, OpCode.Move, arg2Slow, new Immediate(0)),
            new Instruction(20, OpCode.Move, orphanSlow, new Immediate(2)),
            // merge: the invokeData phi plus phis for the scratch and argument registers
            firstMergePhi,
            new Instruction(22, OpCode.Phi, argPhiInputs),
            mergePhi,
            new Instruction(23, OpCode.Move, target, Load(invokeData, 0)),
            new Instruction(24, OpCode.Move, methodInfo, Load(invokeData, 8)),
            new Instruction(25, OpCode.IndirectCall, target, L("junk"), receiver, methodInfo),
            // join: downstream phis and a real call consume the merged register values
            joinPhi,
            new Instruction(27, OpCode.Phi, x1Join, x1Pre, methodInfo),
            new Instruction(28, OpCode.Call, new Immediate(0x8000), L("callJunk"),
                reachablePreHead ? arg2Phi : orphanPhi),
            new Instruction(29, OpCode.Move, keep, scratchJoin),
            new Instruction(30, OpCode.Move, keep2, x1Join),
            new Instruction(31, OpCode.Add, keep3, keep, keep2),
            new Instruction(32, OpCode.Return, keep3),
        };
        ResolveJumps(instructions, (skip, joinPhi), (branch, slowBlock), (jump, firstMergePhi));
        return instructions;
    }

    [Test]
    public void InterfaceDispatchExcisesLookupThroughMergedRegisterPhis()
    {
        var disposable = CorLib("System.IDisposable");
        var instructions = MergedScratchPhiInterfaceShape(disposable,
            InterfaceSlotOf(disposable, "Dispose"), reachablePreHead: true);
        var dispatch = instructions.Single(i => i.OpCode == OpCode.IndirectCall);
        var methodInfoLoad = instructions.Single(i =>
            i.OpCode == OpCode.Move && i.Operands[1] is MemoryOperand { Addend: 8 });
        var scratchJoin = instructions.Where(i => i.OpCode == OpCode.Phi)
            .First(i => i.Operands[0] is LocalVariable { Name: "scratchJoin" });
        var sinkCall = instructions.Single(i => i.IsCall
            && i.Operands[0] is Immediate { Value: 0x8000 });
        var method = Caller(App.SystemTypes.SystemVoidType, instructions);

        InterfaceDispatchRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.CallVoid));
        Assert.That((MethodAnalysisContext)dispatch.Operands[0], Has.Property("Name").EqualTo("Dispose"));
        // the slow-lookup helper and its region are gone entirely
        Assert.That(method.ControlFlowGraph!.Instructions, Has.None.Matches<Instruction>(i =>
            i.IsCall && i.Operands[0] is Immediate { Value: 0x9000 }));
        // the scratch-register phi web was redirected to the version reaching the head
        Assert.That(scratchJoin.Operands.Skip(1).OfType<LocalVariable>(),
            Has.All.Matches<LocalVariable>(o => o.Name == "scratchPre"));
        // the argument-register phi's use in the later call was redirected the same way
        Assert.That(sinkCall.Operands.OfType<LocalVariable>(),
            Has.Some.Matches<LocalVariable>(o => o.Name == "arg2Pre")
                .And.None.Matches<LocalVariable>(o => o.Name == "arg2Phi"));
        // the live methodInfo load became a copy of the value entering the lookup
        Assert.That(methodInfoLoad.Operands[1] is LocalVariable { Name: "x1Pre" });
    }

    [Test]
    public void InterfaceDispatchKeepsHelperWhenMergedRegisterHasNoReachingValue()
    {
        var disposable = CorLib("System.IDisposable");
        var instructions = MergedScratchPhiInterfaceShape(disposable,
            InterfaceSlotOf(disposable, "Dispose"), reachablePreHead: false);
        var dispatch = instructions.Single(i => i.OpCode == OpCode.IndirectCall);
        var method = Caller(App.SystemTypes.SystemVoidType, instructions);

        InterfaceDispatchRecovery.Run(method);

        // the dispatch itself is still resolved, but the unprovable register value keeps the
        // helper call (and therefore its diagnostic) alive
        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.CallVoid));
        Assert.That(method.ControlFlowGraph!.Instructions, Has.Some.Matches<Instruction>(i =>
            i.IsCall && i.Operands[0] is Immediate { Value: 0x9000 }));
    }

    // ===== delegate invoke =====

    // Raw-layout delegate call: operand[2] is the invoke_impl_this carrier (first integer
    // register), the declared parameters follow, and the delegate's MethodInfo sits in the
    // integer register after them - exactly what the lifter leaves for an unknown callee,
    // once local typing has folded the field reads into FieldReference operands.
    private static List<Instruction> DelegateDispatchShape(TypeAnalysisContext delegateType,
        bool tail, int parameterCount)
    {
        var receiver = L("receiver", delegateType);
        var target = L("target");
        var result = L("result");
        var thisArg = L("rcx");
        var args = Enumerable.Range(0, parameterCount)
            .Select(i => L(IntRegisters[1 + i])).ToList();
        var methodInfo = L(IntRegisters[1 + parameterCount]);
        var methodField = CorLib("System.Delegate").Fields.First(f => f.Name == "method");

        var operands = new List<IOperand> { target, tail ? L("stale") : result, thisArg };
        operands.AddRange(args);
        operands.Add(methodInfo);
        foreach (var register in IntRegisters.Skip(2 + parameterCount))
            operands.Add(new Register(null, register));
        foreach (var register in FloatRegisters)
            operands.Add(new Register(null, register));

        var instructions = new List<Instruction>
        {
            new(0, OpCode.Move, target, Load(receiver, InvokeImplOffset)),
            new(1, OpCode.Move, thisArg, Load(receiver, 16)),
            new(2, OpCode.Move, methodInfo, new FieldReference(methodField, receiver, 8)),
            new(3, tail ? OpCode.IndirectJump : OpCode.IndirectCall, operands),
        };
        if (!tail)
            instructions.Add(new Instruction(4, OpCode.Return, result));
        return instructions;
    }

    [Test]
    public void ClosedDelegateCallBecomesInvoke()
    {
        var action = CorLib("System.Action");
        var receiverHolder = DelegateDispatchShape(action, tail: false, parameterCount: 0);
        var method = Caller(App.SystemTypes.SystemVoidType, receiverHolder);
        var receiver = (LocalVariable)((MemoryOperand)((Instruction)method.ControlFlowGraph!
            .Instructions[0]).Operands[1]).Base!;
        var dispatch = method.ControlFlowGraph.Instructions.First(i => i.OpCode == OpCode.IndirectCall);

        DelegateInvokeRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.CallVoid));
        var resolved = (MethodAnalysisContext)dispatch.Operands[0];
        Assert.That(resolved.Name, Is.EqualTo("Invoke"));
        Assert.That(resolved.DeclaringType!.FullName, Is.EqualTo("System.Action"));
        Assert.That(dispatch.Operands[1], Is.SameAs(receiver));

        var emitted = Emitted(App, method, App.SystemTypes.SystemVoidType);
        Assert.That(emitted.Any(i => i.OpCode == CilOpCodes.Call || i.OpCode == CilOpCodes.Callvirt)
            && emitted.Any(i => i.Operand?.ToString()?.Contains("Invoke") == true), Is.True,
            () => string.Join("\n", emitted));
    }

    [Test]
    public void MulticastDelegateCallBecomesInvokeWithResult()
    {
        var func = CorLib("System.Func`2")
            .MakeGenericInstanceType(App.SystemTypes.SystemObjectType, App.SystemTypes.SystemBooleanType);
        var method = Caller(App.SystemTypes.SystemBooleanType,
            DelegateDispatchShape(func, tail: false, parameterCount: 1));
        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);

        DelegateInvokeRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.Call));
        var resolved = (MethodAnalysisContext)dispatch.Operands[0];
        Assert.That(resolved.Name, Is.EqualTo("Invoke"));
        Assert.That(resolved.DeclaringType!.FullName,
            Is.EqualTo("System.Func`2<System.Object, System.Boolean>"));
    }

    [Test]
    public void DelegateTailInvokeBecomesCallAndReturn()
    {
        var func = CorLib("System.Func`1")
            .MakeGenericInstanceType(App.SystemTypes.SystemInt32Type);
        var method = Caller(App.SystemTypes.SystemInt32Type,
            DelegateDispatchShape(func, tail: true, parameterCount: 0));
        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectJump);

        DelegateInvokeRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.Call));
        var resolved = (MethodAnalysisContext)dispatch.Operands[0];
        Assert.That(resolved.Name, Is.EqualTo("Invoke"));
        Assert.That(method.ControlFlowGraph.Instructions.Last().OpCode, Is.EqualTo(OpCode.Return));
        Assert.That(method.ControlFlowGraph.Instructions.Last().Operands[0],
            Is.SameAs(dispatch.Operands[1]));
    }

    [Test]
    public void DelegateDispatchWithInvokeImplAsReceiverStaysIndirect()
    {
        var action = CorLib("System.Action");
        var receiver = L("receiver", action);
        var target = L("target");
        // The frame's receiver slot loads invoke_impl itself - not an honest receiver.
        var method = Caller(App.SystemTypes.SystemVoidType, [
            new Instruction(0, OpCode.Move, target, Load(receiver, InvokeImplOffset)),
            new Instruction(1, OpCode.IndirectCall, target, L("stale"),
                Load(receiver, InvokeImplOffset), Load(receiver, 8)),
            new Instruction(2, OpCode.Return)]);
        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);

        DelegateInvokeRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.IndirectCall));
    }

    [Test]
    public void DelegateDispatchWithForeignMethodInfoStaysIndirect()
    {
        var action = CorLib("System.Action");
        var receiver = L("receiver", action);
        var target = L("target");
        // The slot after the parameters is not a delegate-internal field - the frame
        // layout isn't the delegate's own, so nothing is proven.
        var method = Caller(App.SystemTypes.SystemVoidType, [
            new Instruction(0, OpCode.Move, target, Load(receiver, InvokeImplOffset)),
            new Instruction(1, OpCode.IndirectCall, target, L("stale"),
                Load(receiver, 16), L("unrelated")),
            new Instruction(2, OpCode.Return)]);
        var dispatch = method.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.IndirectCall);

        DelegateInvokeRecovery.Run(method);

        Assert.That(dispatch.OpCode, Is.EqualTo(OpCode.IndirectCall));
    }

    // ===== phi-carried construction distribution =====

    [Test]
    public void PhiedDelegateFunctionPointerDistributesConstruction()
    {
        var action = CorLib("System.Action");
        var actionCtor = action.Methods.First(m => m.Name == ".ctor" && m.Parameters.Count == 2);
        var owner = new InjectedTypeAnalysisContext(App.AssembliesByName["mscorlib"], "Tests",
            "DelegateTargets", App.SystemTypes.SystemObjectType,
            ReflectionTypeAttributes.Public | ReflectionTypeAttributes.Class);
        var add = owner.InjectMethodContext("Add", App.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static);
        var mul = owner.InjectMethodContext("Mul", App.SystemTypes.SystemVoidType,
            ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static);
        var allocated = L("allocated", action);
        var fnA = L("fnA");
        var fnB = L("fnB");
        var fnptr = L("fnptr");
        var target = L("target");
        var instructions = new List<Instruction>
        {
            new(0, OpCode.CheckNotEqual, L("cond"), L("selector"), new Immediate(0)),
            new(1, OpCode.ConditionalJump, new Immediate(4)),
            new(2, OpCode.Move, fnA, new RuntimeMethodInfoAnalysisContext(add, action.DeclaringAssembly)),
            new(3, OpCode.Jump, new Immediate(6)),
            new(4, OpCode.Move, fnB, new RuntimeMethodInfoAnalysisContext(mul, action.DeclaringAssembly)),
            new(5, OpCode.Jump, new Immediate(6)),
            new(6, OpCode.Phi, fnptr, fnA, fnB),
            new(7, OpCode.Newobj, allocated, action),
            new(8, OpCode.CallVoid, actionCtor, allocated, new Immediate(0), fnptr),
            new(9, OpCode.Move, target, Load(allocated, InvokeImplOffset)),
            new(10, OpCode.IndirectCall, target, L("stale"), Load(allocated, 16), Load(allocated, 8)),
            new(11, OpCode.Return),
        };
        var method = Caller(App.SystemTypes.SystemVoidType, instructions);

        InterfaceDispatchRecovery.Run(method);

        // The construction is cloned into each merge edge, each carrying its own constant target.
        var clones = method.ControlFlowGraph.Instructions
            .Where(i => i.OpCode == OpCode.CallVoid
                        && i.Operands is [MethodAnalysisContext { Name: ".ctor" }, ..])
            .ToList();
        Assert.That(clones, Has.Count.EqualTo(2));
        Assert.That(clones.Select(c => ((RuntimeMethodInfoAnalysisContext)c.Operands[3]).RepresentedMethod.Name),
            Is.EquivalentTo(new[] { "Add", "Mul" }));
        Assert.That(method.ControlFlowGraph.Instructions.Any(i => i.OpCode == OpCode.Phi
            && i.Operands[0] is LocalVariable), Is.True);
    }
}
