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

// End-to-end fixtures for TailCallRecovery: terminal IndirectJump (br reg) whose target provably
// loads a managed entry point - [methodof + 0|8] for methodPointer/virtualMethodPointer, or
// [klass + 0x138 + slot*16] where klass is Il2CppClass<T>-typed - becomes a managed call followed
// by Return. Everything else (jump tables, raw pointers, phi disagreement, return mismatches)
// keeps the indirect-jump diagnostic.
public class TailCallRecoveryTests
{
    private const long VTableOffset = 0x138;
    private const int InvokeDataSize = 16;
    private const long PointerSize = 8;

    // The test game is a Windows x64 PE: MSVC raw argument order is rcx,rdx,r8,r9 then xmm0-3,
    // and an indirect jump carries [target, staleResult, <raw arg registers>].
    private static readonly string[] IntRegisters = ["rcx", "rdx", "r8", "r9"];
    private static readonly string[] FloatRegisters = ["xmm0", "xmm1", "xmm2", "xmm3"];

    [SetUp] public void Setup() { Cpp2IlApi.ResetInternalState(); TestGameLoader.LoadSimple2019Game(); }

    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;
    private static TypeAnalysisContext CorLib(string name) =>
        App.AssembliesByName["mscorlib"].GetTypeByFullName(name)!;

    private static LocalVariable L(string name, TypeAnalysisContext? type = null)
        => new(name, new Register(null, name), type);

    // A frame argument local bound to a concrete argument register - HasRawArgumentLayout
    // and the managed-argument mapping match operands by register name.
    private static LocalVariable Arg(string register, TypeAnalysisContext? type = null)
        => new(register, new Register(null, register), type);

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
            "TailCaller", App.SystemTypes.SystemObjectType,
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

    // [target, staleResult, <arguments>, <remaining int regs>, xmm0..3] - the tail-jump frame.
    // Arguments occupy their registers' positions: arguments[i] must be named IntRegisters[i].
    private static Instruction RawTailJump(IOperand target, params IOperand[] arguments)
    {
        var operands = new List<IOperand> { target, L("stale") };
        operands.AddRange(arguments);
        operands.AddRange(IntRegisters.Skip(arguments.Length)
            .Select(r => (IOperand)new Register(null, r)));
        operands.AddRange(FloatRegisters.Select(r => (IOperand)new Register(null, r)));
        return new Instruction(20, OpCode.IndirectJump, operands);
    }

    private static RuntimeMethodInfoAnalysisContext MethodInfoOf(MethodAnalysisContext method)
        => new(method, method.DeclaringType!.DeclaringAssembly!);

    private static int VTableSlotOf(TypeAnalysisContext type, string name)
    {
        var definition = type.Definition!;
        for (var i = 0; i < definition.VtableCount; i++)
            if (App.ResolveContextForMethod(definition.VTable[i]) is { IsStatic: false } method
                && method.Name == name)
                return i;
        throw new InconclusiveException($"{type.FullName} has no {name} vtable entry");
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

    private static List<CilInstruction> Emitted(InjectedMethodAnalysisContext context,
        TypeAnalysisContext returnType)
    {
        var module = new ModuleDefinition("TailCallRecovery.dll");
        var callerType = new TypeDefinition("Tests", "TailCaller", TypeAttributes.Public,
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

    private static Block BlockOf(MethodAnalysisContext method, Instruction instruction)
        => method.ControlFlowGraph!.Blocks.Single(b => b.Instructions.Contains(instruction));

    // ===== methodPointer / virtualMethodPointer loads =====

    [Test]
    public void MethodInfoPointerTailJumpResolvesToCall()
    {
        var boolean = App.SystemTypes.SystemBooleanType;
        var isNullOrEmpty = CorLib("System.String").Methods.First(m =>
            m.Name == "IsNullOrEmpty" && m.Parameters.Count == 1);
        var argument = Arg("rcx", CorLib("System.String"));
        var methodInfo = Arg("rdx");
        var target = L("target");
        var jump = RawTailJump(target, argument, methodInfo);
        var method = Caller(boolean, [
            new Instruction(10, OpCode.Move, target, Load(MethodInfoOf(isNullOrEmpty), 0)),
            jump]);

        TailCallRecovery.Run(method);

        Assert.That(jump.OpCode, Is.EqualTo(OpCode.Call));
        Assert.That(jump.Operands[0], Is.SameAs(isNullOrEmpty));
        Assert.That(jump.Operands[2], Is.SameAs(argument));
        Assert.That(jump.Operands[^1], Is.SameAs(methodInfo));
        var ret = BlockOf(method, jump).Instructions[^1];
        Assert.That(ret.OpCode, Is.EqualTo(OpCode.Return));
        Assert.That(ret.Operands, Is.EqualTo(new[] { jump.Operands[1] }));
    }

    [Test]
    public void VirtualMethodPointerTailJumpResolvesToCall()
    {
        var str = CorLib("System.String");
        var toString = CorLib("System.Object").Methods.First(m => m.Name == "ToString");
        var receiver = Arg("rcx", CorLib("System.Exception"));
        var methodInfo = Arg("rdx");
        var target = L("target");
        var jump = RawTailJump(target, receiver, methodInfo);
        var method = Caller(str, [
            // virtualMethodPointer sits one pointer past methodPointer.
            new Instruction(10, OpCode.Move, target, Load(MethodInfoOf(toString), PointerSize)),
            jump]);

        TailCallRecovery.Run(method);

        Assert.That(jump.OpCode, Is.EqualTo(OpCode.Call));
        Assert.That(jump.Operands[0], Is.SameAs(toString));
        Assert.That(BlockOf(method, jump).Instructions[^1].OpCode, Is.EqualTo(OpCode.Return));
    }

    [Test]
    public void VoidCallerTailJumpToNonVoidCalleeBecomesCallVoidAndBareReturn()
    {
        var isNullOrEmpty = CorLib("System.String").Methods.First(m =>
            m.Name == "IsNullOrEmpty" && m.Parameters.Count == 1);
        var target = L("target");
        var jump = RawTailJump(target, Arg("rcx", CorLib("System.String")), Arg("rdx"));
        var method = Caller(App.SystemTypes.SystemVoidType, [
            new Instruction(10, OpCode.Move, target, Load(MethodInfoOf(isNullOrEmpty), 0)),
            jump]);

        TailCallRecovery.Run(method);

        // call+pop: the result is discarded, so no result operand and a bare Return.
        Assert.That(jump.OpCode, Is.EqualTo(OpCode.CallVoid));
        Assert.That(jump.Operands[0], Is.SameAs(isNullOrEmpty));
        var ret = BlockOf(method, jump).Instructions[^1];
        Assert.That(ret.OpCode, Is.EqualTo(OpCode.Return));
        Assert.That(ret.Operands, Has.Count.EqualTo(0));

        var emitted = Emitted(method, App.SystemTypes.SystemVoidType);
        Assert.That(emitted.Any(i => i.OpCode == CilOpCodes.Pop), Is.True,
            () => string.Join("\n", emitted));
    }

    // ===== vtable slot loads on an Il2CppClass<T>-typed pointer =====

    [Test]
    public void VTableTailJumpResolvesToVirtualDispatch()
    {
        var int32 = App.SystemTypes.SystemInt32Type;
        var exception = CorLib("System.Exception");
        var slot = VTableSlotOf(exception, "GetHashCode");
        var addend = VTableOffset + slot * InvokeDataSize;
        var klass = new LocalVariable("klass", new Register(null, "x9"),
            new RuntimeClassTypeAnalysisContext(exception, exception.DeclaringAssembly!));
        var receiver = Arg("rcx", exception);
        var methodInfo = Arg("rdx");
        var target = L("target");
        var jump = RawTailJump(target, receiver, methodInfo);
        var method = Caller(int32, [
            new Instruction(10, OpCode.Move, target, Load(klass, addend)),
            new Instruction(11, OpCode.Move, methodInfo, Load(klass, addend + PointerSize)),
            jump]);

        TailCallRecovery.Run(method);

        Assert.That(jump.OpCode, Is.EqualTo(OpCode.Call));
        Assert.That(jump.IsVirtualDispatch, Is.True);
        var resolved = (MethodAnalysisContext)jump.Operands[0];
        Assert.That(resolved.Name, Is.EqualTo("GetHashCode"));
        Assert.That(jump.Operands[2], Is.SameAs(receiver));
        // The hidden argument slot is named after the resolved MethodInfo.
        Assert.That(jump.Operands[^1], Is.InstanceOf<RuntimeMethodInfoAnalysisContext>());
    }

    // ===== phi-carried targets =====

    [Test]
    public void PhiCarriedMethodInfoTargetResolvesToCall()
    {
        var isNullOrEmpty = CorLib("System.String").Methods.First(m =>
            m.Name == "IsNullOrEmpty" && m.Parameters.Count == 1);
        var targetA = L("targetA");
        var targetB = L("targetB");
        var merged = L("merged");
        var jump = RawTailJump(merged, Arg("rcx", CorLib("System.String")), Arg("rdx"));
        var method = Caller(App.SystemTypes.SystemVoidType, [
            new Instruction(0, OpCode.CheckNotEqual, L("cond"), L("selector"), new Immediate(0)),
            new Instruction(1, OpCode.ConditionalJump, new Immediate(4)),
            new Instruction(2, OpCode.Move, targetA, Load(MethodInfoOf(isNullOrEmpty), 0)),
            new Instruction(3, OpCode.Jump, new Immediate(6)),
            new Instruction(4, OpCode.Move, targetB, Load(MethodInfoOf(isNullOrEmpty), 0)),
            new Instruction(5, OpCode.Jump, new Immediate(6)),
            new Instruction(6, OpCode.Phi, merged, targetA, targetB),
            jump]);

        TailCallRecovery.Run(method);

        Assert.That(jump.OpCode, Is.EqualTo(OpCode.CallVoid));
        Assert.That(jump.Operands[0], Is.SameAs(isNullOrEmpty));
        Assert.That(BlockOf(method, jump).Instructions[^1].OpCode, Is.EqualTo(OpCode.Return));
    }

    // ===== negatives =====

    [Test]
    public void JumpTableTargetStaysIndirect()
    {
        var target = L("target");
        var jump = RawTailJump(target, Arg("rcx"));
        var method = Caller(App.SystemTypes.SystemVoidType, [
            new Instruction(10, OpCode.Add, target, L("tableBase"), L("scaledIndex")),
            jump]);

        TailCallRecovery.Run(method);

        Assert.That(jump.OpCode, Is.EqualTo(OpCode.IndirectJump));
    }

    [Test]
    public void UnknownPointerTargetStaysIndirect()
    {
        var jump = RawTailJump(L("unknownTarget"), Arg("rcx"));
        var method = Caller(App.SystemTypes.SystemVoidType, [jump]);

        TailCallRecovery.Run(method);

        Assert.That(jump.OpCode, Is.EqualTo(OpCode.IndirectJump));
    }

    [Test]
    public void IncompatibleReturnStaysIndirect()
    {
        var exception = CorLib("System.Exception");
        var isNullOrEmpty = CorLib("System.String").Methods.First(m =>
            m.Name == "IsNullOrEmpty" && m.Parameters.Count == 1);
        var target = L("target");
        var jump = RawTailJump(target, Arg("rcx", CorLib("System.String")), Arg("rdx"));
        // bool is not assignable to Exception - the frame cannot be a tail call to it.
        var method = Caller(exception, [
            new Instruction(10, OpCode.Move, target, Load(MethodInfoOf(isNullOrEmpty), 0)),
            jump]);

        TailCallRecovery.Run(method);

        Assert.That(jump.OpCode, Is.EqualTo(OpCode.IndirectJump));
    }

    [Test]
    public void VoidCalleeIntoNonVoidCallerStaysIndirect()
    {
        var ctor = CorLib("System.Object").Methods.First(m =>
            m.Name == ".ctor" && m.Parameters.Count == 0);
        var target = L("target");
        var jump = RawTailJump(target, Arg("rcx"), Arg("rdx"));
        var method = Caller(App.SystemTypes.SystemInt32Type, [
            new Instruction(10, OpCode.Move, target, Load(MethodInfoOf(ctor), 0)),
            jump]);

        TailCallRecovery.Run(method);

        Assert.That(jump.OpCode, Is.EqualTo(OpCode.IndirectJump));
    }

    [Test]
    public void PhiWithDisagreeingSourcesStaysIndirect()
    {
        var isNullOrEmpty = CorLib("System.String").Methods.First(m =>
            m.Name == "IsNullOrEmpty" && m.Parameters.Count == 1);
        var toString = CorLib("System.Object").Methods.First(m => m.Name == "ToString");
        var targetA = L("targetA");
        var targetB = L("targetB");
        var merged = L("merged");
        var jump = RawTailJump(merged, Arg("rcx"), Arg("rdx"));
        var method = Caller(App.SystemTypes.SystemVoidType, [
            new Instruction(0, OpCode.CheckNotEqual, L("cond"), L("selector"), new Immediate(0)),
            new Instruction(1, OpCode.ConditionalJump, new Immediate(4)),
            new Instruction(2, OpCode.Move, targetA, Load(MethodInfoOf(isNullOrEmpty), 0)),
            new Instruction(3, OpCode.Jump, new Immediate(6)),
            new Instruction(4, OpCode.Move, targetB, Load(MethodInfoOf(toString), 0)),
            new Instruction(5, OpCode.Jump, new Immediate(6)),
            new Instruction(6, OpCode.Phi, merged, targetA, targetB),
            jump]);

        TailCallRecovery.Run(method);

        Assert.That(jump.OpCode, Is.EqualTo(OpCode.IndirectJump));
    }

    [Test]
    public void VTableAddendOffSlotBoundaryStaysIndirect()
    {
        var exception = CorLib("System.Exception");
        var slot = VTableSlotOf(exception, "GetHashCode");
        var klass = new LocalVariable("klass", new Register(null, "x9"),
            new RuntimeClassTypeAnalysisContext(exception, exception.DeclaringAssembly!));
        var target = L("target");
        var jump = RawTailJump(target, Arg("rcx", exception), Arg("rdx"));
        var method = Caller(App.SystemTypes.SystemInt32Type, [
            // Half a VirtualInvokeData off - not a slot entry.
            new Instruction(10, OpCode.Move, target,
                Load(klass, VTableOffset + slot * InvokeDataSize + PointerSize)),
            jump]);

        TailCallRecovery.Run(method);

        Assert.That(jump.OpCode, Is.EqualTo(OpCode.IndirectJump));
    }

    // ===== delegate tail jumps go through DelegateInvokeRecovery =====

    [Test]
    public void GenericInstanceDelegateTailJumpResolvesToInvoke()
    {
        var action = CorLib("System.Action`1")
            .MakeGenericInstanceType(App.SystemTypes.SystemInt32Type);
        var del = new LocalVariable("del", new Register(null, "x1"), action);
        var methodPtr = Arg("rcx");
        var argument = Arg("rdx", App.SystemTypes.SystemInt32Type);
        var methodField = Arg("r8");
        var target = L("target");
        // (method_ptr, arg, method): the receiver register carries a delegate-internal field.
        var jump = RawTailJump(target, methodPtr, argument, methodField);
        var method = Caller(App.SystemTypes.SystemVoidType, [
            new Instruction(10, OpCode.Move, target, Load(del, PointerSize * 3)),
            new Instruction(11, OpCode.Move, methodPtr, Load(del, PointerSize)),
            new Instruction(12, OpCode.Move, methodField, Load(del, PointerSize * 2)),
            jump]);

        DelegateInvokeRecovery.Run(method);

        Assert.That(jump.OpCode, Is.EqualTo(OpCode.CallVoid));
        var resolved = (MethodAnalysisContext)jump.Operands[0];
        Assert.That(resolved.Name, Is.EqualTo("Invoke"));
        Assert.That(jump.Operands[1], Is.SameAs(del));
        Assert.That(BlockOf(method, jump).Instructions[^1].OpCode, Is.EqualTo(OpCode.Return));
    }

    [Test]
    public void FuncDelegateTailJumpReturnsInvokeResult()
    {
        var int32 = App.SystemTypes.SystemInt32Type;
        var func = CorLib("System.Func`1").MakeGenericInstanceType(int32);
        var del = new LocalVariable("del", new Register(null, "x1"), func);
        var methodPtr = Arg("rcx");
        var methodField = Arg("rdx");
        var target = L("target");
        var jump = RawTailJump(target, methodPtr, methodField);
        var method = Caller(int32, [
            new Instruction(10, OpCode.Move, target, Load(del, PointerSize * 3)),
            new Instruction(11, OpCode.Move, methodPtr, Load(del, PointerSize)),
            new Instruction(12, OpCode.Move, methodField, Load(del, PointerSize * 2)),
            jump]);

        DelegateInvokeRecovery.Run(method);

        Assert.That(jump.OpCode, Is.EqualTo(OpCode.Call));
        var resolved = (MethodAnalysisContext)jump.Operands[0];
        Assert.That(resolved.Name, Is.EqualTo("Invoke"));
        var ret = BlockOf(method, jump).Instructions[^1];
        Assert.That(ret.OpCode, Is.EqualTo(OpCode.Return));
        Assert.That(ret.Operands, Has.Count.EqualTo(1));
    }

    [Test]
    public void UntypedInvokeImplLoadStaysIndirect()
    {
        // [x + 0x18] where x is an untyped load - no delegate evidence, stays a diagnostic.
        var source = L("source");
        var target = L("target");
        var jump = RawTailJump(target, Arg("rcx"), Arg("rdx"));
        var method = Caller(App.SystemTypes.SystemVoidType, [
            new Instruction(10, OpCode.Move, source, Load(L("outer"), 0)),
            new Instruction(11, OpCode.Move, target, Load(source, PointerSize * 3)),
            jump]);

        DelegateInvokeRecovery.Run(method);
        TailCallRecovery.Run(method);

        Assert.That(jump.OpCode, Is.EqualTo(OpCode.IndirectJump));
    }
}
