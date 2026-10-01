using System;
using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

public class ExceptionRegionRecoveryTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    // A native cleanup action runs Dispose with the same enumerator address, then
    // resumes the original unwind. A different argument or hidden store is no proof.
    [TestCase(false, false, false, false, false)]
    [TestCase(true, false, false, false, false)]
    [TestCase(false, true, false, false, false)]
    [TestCase(false, false, true, false, false)]
    [TestCase(false, false, false, true, false)]
    [TestCase(false, false, false, false, true)]
    public void ForeachCleanupRequiresMatchingArgumentsAndAllEffects(bool differentArgument, bool extraStore,
        bool constantDispatch, bool indirectClobber, bool reloadedHeap)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = owner.InjectMethodContext("M", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        var cleanup = owner.InjectMethodContext("Dispose", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        var work = owner.InjectMethodContext("MoveNext", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        var enumerator = new Register(null, "X19");
        var exception = new Register(null, "X20");
        Instruction At(ulong address, OpCode opcode, params IOperand[] operands)
            => new(0, opcode, operands.ToList()) { NativeAddress = address };
        var protectedCall = At(0x1004, OpCode.CallVoid, work);
        var dispose = At(0x1008, OpCode.CallVoid, cleanup, enumerator);
        var ret = At(0x100C, OpCode.Return);
        caller.ConvertedIsil = [At(0x1000, OpCode.Move, enumerator, new Immediate(42)),
            protectedCall, dispose, ret,
            At(0x2000, OpCode.Move, exception, new Register(null, "X0"))];
        if (reloadedHeap)
        {
            var memory = new MemoryOperand(addend: 0x9000);
            caller.ConvertedIsil[0].SetOperand(1, memory);
            caller.ConvertedIsil.Add(At(0x2001, OpCode.Move, enumerator, memory));
        }
        if (indirectClobber)
        {
            var scratch = new Register(null, "X9");
            caller.ConvertedIsil.InsertRange(1, [At(0x1001, OpCode.Move, scratch, new Immediate(42)),
                At(0x1002, OpCode.IndirectCall, new Immediate(0x3000), new Register(null, "X0")),
                At(0x1003, OpCode.Move, enumerator, scratch)]);
        }
        if (constantDispatch)
        {
            var flag = new Register(null, "X21");
            caller.ConvertedIsil.AddRange([At(0x2001, OpCode.CheckLess, flag, new Immediate(3), new Immediate(4)),
                At(0x2002, OpCode.Xor, flag, flag, new Immediate(1)),
                At(0x2003, OpCode.ConditionalJump, ret, flag)]);
        }
        if (extraStore) caller.ConvertedIsil.Add(At(0x2004, OpCode.MemorySet, enumerator, new Immediate(0), new Immediate(8)));
        caller.ConvertedIsil.AddRange([
            At(0x2008, OpCode.CallVoid, cleanup, differentArgument ? new Immediate(43) : indirectClobber ? new Immediate(42) : enumerator),
            At(0x200C, OpCode.CallVoid, new StringLiteral("_Unwind_Resume"), exception)]);
        caller.UnwindInfo = new EhFunctionInfo { Start = 0x1000, Size = 0x1010 };
        caller.UnwindInfo.CallSites.Add(new EhCallSiteInfo(0x1004, 4, 0x2000, 0)
            { Actions = [new EhActionInfo(0, null)] });
        EhRegionPartition.Partition(caller);

        var module = new ModuleDefinition("Regions.dll");
        var definition = new MethodDefinition("M", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        definition.CilMethodBody = new CilMethodBody();
        var callee = new MethodDefinition("Dispose", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        var workDefinition = new MethodDefinition("MoveNext", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        cleanup.PutExtraData("AsmResolverMethod", callee);
        var map = new Dictionary<Instruction, List<CilInstruction>>
        {
            [protectedCall] = [new(CilOpCodes.Call, workDefinition)],
            [dispose] = [new(CilOpCodes.Call, callee)],
            [ret] = [new(CilOpCodes.Ret)]
        };
        foreach (var instruction in map.Values.SelectMany(x => x)) definition.CilMethodBody.Instructions.Add(instruction);
        ExceptionRegionRecovery.Apply(caller, definition, map);
        var body = definition.CilMethodBody;
        if (differentArgument || extraStore || indirectClobber || reloadedHeap)
        {
            Assert.That(body.ExceptionHandlers, Is.Empty);
            Assert.That(caller.AnalysisWarnings, Has.Count.EqualTo(1));
            Assert.That(body.Instructions.Count, Is.EqualTo(3));
            return;
        }
        var clause = body.ExceptionHandlers.Single();
        Assert.That(clause.HandlerType, Is.EqualTo(CilExceptionHandlerType.Finally));
        var first = body.Instructions.IndexOf(((CilInstructionLabel)clause.HandlerStart!).Instruction!);
        Assert.That(body.Instructions[first].Operand, Is.SameAs(callee));
        Assert.That(body.Instructions[first + 1].OpCode, Is.EqualTo(CilOpCodes.Endfinally));
        Assert.That(body.Instructions.Count(i => i.Operand == callee), Is.EqualTo(1));
        Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Leave), Is.True);
        Assert.That(caller.AnalysisWarnings, Is.Empty);
        Assert.That(body.ComputeMaxStack(), Is.EqualTo(0));
    }
    [TestCase(8, true, null, false)]
    [TestCase(16, false, null, false)]
    [TestCase(8, true, "il2cpp_value_box", true)]
    [TestCase(8, false, null, true)]
    [TestCase(8, true, "il2cpp_codegen_write_barrier", true)]
    [TestCase(8, false, "il2cpp_gc_wbarrier_set_field", true)]
    [TestCase(8, true, "barrier-alias", true)]
    public void CallInvalidationRespectsTheWidthOfAnAdjacentSavedFramePointer(int width, bool proven, string? helper, bool earlierArgument)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Frame",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        MethodAnalysisContext Method(string name) => owner.InjectMethodContext(name, app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        var caller = Method("M");
        var work = Method("Work");
        var cleanup = Method("Dispose");
        var saved = new StackOffset(8);
        var storage = new AddressOf(new StackOffset(16));
        var receiver = new Register(null, "X19");
        var exception = new Register(null, "X20");
        Instruction At(ulong address, OpCode op, params IOperand[] operands)
            => new(0, op, operands.ToList()) { NativeAddress = address };
        var store = At(0x1000, OpCode.Move, saved, storage);
        store.NativeStoreWidthBytes = width;
        var keys = app.GetOrCreateKeyFunctionAddresses();
        const ulong alias = 0xABCDEF;
        if (helper == "barrier-alias") keys.WriteBarrierAliases.Add(alias);
        caller.ConvertedIsil = [store,
            At(0x1004, OpCode.CallVoid, helper == "barrier-alias" ? new Immediate((long)alias)
                : helper != null ? new StringLiteral(helper) : work,
                earlierArgument ? new AddressOf(new StackOffset(4)) : storage),
            At(0x1008, OpCode.CallVoid, cleanup, storage), At(0x100C, OpCode.Return),
            At(0x2000, OpCode.Move, exception, new Register(null, "X0")),
            At(0x2004, OpCode.Move, receiver, saved),
            At(0x2008, OpCode.CallVoid, cleanup, receiver),
            At(0x200C, OpCode.CallVoid, new StringLiteral("_Unwind_Resume"), exception)];
        caller.UnwindInfo = new EhFunctionInfo { Start = 0x1000, Size = 0x1010 };
        caller.UnwindInfo.CallSites.Add(new EhCallSiteInfo(0x1004, 4, 0x2000, 0)
            { Actions = [new EhActionInfo(0, null)] });
        EhRegionPartition.Partition(caller);
        try { Assert.That(new NativeExceptionRegionProof(caller).Find().Count, Is.EqualTo(proven ? 1 : 0)); }
        finally { if (helper == "barrier-alias") keys.WriteBarrierAliases.Remove(alias); }
    }

    [TestCase(false)]
    [TestCase(true)]
    public void CompoundCleanupCannotReuseMemoryFactsAcrossTheFirstCall(bool reloadChangedStorage)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "CompoundWrites",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        MethodAnalysisContext Method(string name) => owner.InjectMethodContext(name, app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        var caller = Method("M");
        var first = Method("First");
        var second = Method("Second");
        var receiver = new Register(null, "X19");
        var exception = new Register(null, "X20");
        var storage = new StackOffset(0);
        Instruction At(ulong address, OpCode op, params IOperand[] operands)
            => new(0, op, operands.ToList()) { NativeAddress = address };
        caller.ConvertedIsil = [At(0x1000, OpCode.Move, receiver, new Immediate(42)),
            At(0x1004, OpCode.Move, storage, receiver),
            At(0x1008, OpCode.CallVoid, Method("Work")),
            At(0x100C, OpCode.CallVoid, first, new AddressOf(storage)),
            At(0x1010, OpCode.CallVoid, second, receiver), At(0x1014, OpCode.Return),
            At(0x2000, OpCode.Move, exception, new Register(null, "X0")),
            At(0x2004, OpCode.CallVoid, first, new AddressOf(storage)),
            At(0x2008, OpCode.CallVoid, second, reloadChangedStorage ? storage : receiver),
            At(0x200C, OpCode.CallVoid, new StringLiteral("_Unwind_Resume"), exception)];
        caller.UnwindInfo = new EhFunctionInfo { Start = 0x1000, Size = 0x1010 };
        caller.UnwindInfo.CallSites.Add(new EhCallSiteInfo(0x1008, 4, 0x2000, 0)
            { Actions = [new EhActionInfo(0, null)] });
        EhRegionPartition.Partition(caller);
        var proofs = new NativeExceptionRegionProof(caller).Find();
        Assert.That(proofs.Count, Is.EqualTo(reloadChangedStorage ? 0 : 1));
        if (!reloadChangedStorage) Assert.That(proofs[0].CleanupCalls.Count, Is.EqualTo(2));
    }

    [Test]
    public void SwitchCasesLeaveFinallyAndPreserveTheDefaultPath()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "SwitchOwner",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        MethodAnalysisContext Method(string name) => owner.InjectMethodContext(name, app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        var caller = Method("M"); var cleanup = Method("Cleanup"); var work = Method("Work");
        Instruction At(ulong address, OpCode op, params IOperand[] operands) => new(0, op, operands.ToList()) { NativeAddress = address };
        var call = At(0x1000, OpCode.CallVoid, work);
        var first = At(0x1008, OpCode.CallVoid, cleanup);
        var second = At(0x1010, OpCode.CallVoid, cleanup);
        var ret = At(0x1014, OpCode.Return);
        var dispatch = At(0x1004, OpCode.ConditionalJump, second, new Register(null, "X8"));
        var join = At(0x100C, OpCode.Jump, ret);
        var exception = new Register(null, "X20");
        caller.ConvertedIsil = [call, dispatch, first, join, second, ret,
            At(0x2000, OpCode.Move, exception, new Register(null, "X0")),
            At(0x2004, OpCode.CallVoid, cleanup),
            At(0x2008, OpCode.CallVoid, new StringLiteral("_Unwind_Resume"), exception)];
        caller.UnwindInfo = new EhFunctionInfo { Start = 0x1000, Size = 0x100C };
        caller.UnwindInfo.CallSites.Add(new EhCallSiteInfo(0x1000, 4, 0x2000, 0) { Actions = [new EhActionInfo(0, null)] });
        EhRegionPartition.Partition(caller);
        var module = new ModuleDefinition("SwitchRegions.dll");
        var runtimeOwner = new TypeDefinition("Tests", "SwitchOwner", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(runtimeOwner);
        MethodDefinition Definition(string name, params TypeSignature[] parameters)
        {
            var method = new MethodDefinition(name, AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
                | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
                MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, parameters));
            runtimeOwner.Methods.Add(method); method.CilMethodBody = new(); return method;
        }
        var definition = Definition("M", module.CorLibTypeFactory.Int32);
        var cleanupDefinition = Definition("Cleanup");
        var workDefinition = Definition("Work");
        workDefinition.CilMethodBody!.Instructions.Add(CilOpCodes.Ret);
        var trace = new FieldDefinition("Trace", AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Static, module.CorLibTypeFactory.Int32);
        runtimeOwner.Fields.Add(trace);
        var cleanupIl = cleanupDefinition.CilMethodBody!.Instructions;
        cleanupIl.Add(CilOpCodes.Ldsfld, trace); cleanupIl.Add(CilOpCodes.Ldc_I4_1); cleanupIl.Add(CilOpCodes.Add);
        cleanupIl.Add(CilOpCodes.Stsfld, trace); cleanupIl.Add(CilOpCodes.Ret);
        cleanup.PutExtraData("AsmResolverMethod", cleanupDefinition);
        var a = new CilInstruction(CilOpCodes.Call, cleanupDefinition);
        var b = new CilInstruction(CilOpCodes.Call, cleanupDefinition);
        var done = new CilInstruction(CilOpCodes.Ret);
        var selection = new CilInstruction(CilOpCodes.Switch, new ICilLabel[] { new CilInstructionLabel(a), new CilInstructionLabel(b) });
        var map = new Dictionary<Instruction, List<CilInstruction>>
        {
            [call] = [new(CilOpCodes.Call, workDefinition)], [dispatch] = [new(CilOpCodes.Ldarg_0), selection],
            [first] = [a], [join] = [new(CilOpCodes.Br, new CilInstructionLabel(done))], [second] = [b], [ret] = [done]
        };
        foreach (var instruction in map.Values.SelectMany(i => i)) definition.CilMethodBody!.Instructions.Add(instruction);
        ExceptionRegionRecovery.Apply(caller, definition, map);
        Assert.That(definition.CilMethodBody!.ExceptionHandlers, Has.Count.EqualTo(1));
        Assert.That(caller.AnalysisWarnings, Is.Empty);
        Assert.That(((IList<ICilLabel>)selection.Operand!).Cast<CilInstructionLabel>()
            .All(l => l.Instruction!.OpCode == CilOpCodes.Leave), Is.True);
        var type = Load(module).GetType("Tests.SwitchOwner")!;
        foreach (var value in new[] { -1, 0, 1, 99 })
        {
            type.GetField("Trace")!.SetValue(null, 0);
            type.GetMethod("M")!.Invoke(null, [value]);
            Assert.That(type.GetField("Trace")!.GetValue(null), Is.EqualTo(1));
        }
    }

    [TestCase(true)]
    [TestCase(false)]
    public void HandlerLocalMustBeAssignedOnEveryIncomingPath(bool assignRight)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Diamond",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = owner.InjectMethodContext("M", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        var cleanup = owner.InjectMethodContext("Cleanup", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, [app.SystemTypes.SystemInt32Type]);
        var work = owner.InjectMethodContext("Work", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        Instruction At(ulong address, OpCode op, params IOperand[] operands)
            => new(0, op, operands.ToList()) { NativeAddress = address };
        var receiver = new Register(null, "X19");
        var exception = new Register(null, "X20");
        var left = At(0x1004, OpCode.Move, receiver, new Immediate(42));
        var right = At(0x100C, OpCode.Move, receiver, new Immediate(42));
        var call = At(0x1010, OpCode.CallVoid, work);
        var branch = At(0x1000, OpCode.ConditionalJump, right, new Register(null, "X8"));
        var join = At(0x1008, OpCode.Jump, call);
        var dispose = At(0x1014, OpCode.CallVoid, cleanup, receiver);
        var ret = At(0x1018, OpCode.Return);
        caller.ConvertedIsil = [branch, left, join, right, call, dispose, ret,
            At(0x2000, OpCode.Move, exception, new Register(null, "X0")),
            At(0x2004, OpCode.CallVoid, cleanup, receiver),
            At(0x2008, OpCode.CallVoid, new StringLiteral("_Unwind_Resume"), exception)];
        caller.UnwindInfo = new EhFunctionInfo { Start = 0x1000, Size = 0x100C };
        caller.UnwindInfo.CallSites.Add(new EhCallSiteInfo(0x1010, 4, 0x2000, 0) { Actions = [new EhActionInfo(0, null)] });
        EhRegionPartition.Partition(caller);
        var module = new ModuleDefinition("Diamond.dll");
        var definition = new MethodDefinition("M", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.Boolean]));
        definition.CilMethodBody = new();
        var local = new CilLocalVariable(module.CorLibTypeFactory.Int32);
        definition.CilMethodBody.LocalVariables.Add(local);
        var cleanupDefinition = new MethodDefinition("Cleanup", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.Int32]));
        cleanup.PutExtraData("AsmResolverMethod", cleanupDefinition);
        var workDefinition = new MethodDefinition("Work", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        var rightStart = new CilInstruction(assignRight ? CilOpCodes.Ldc_I4 : CilOpCodes.Nop);
        if (assignRight) rightStart.Operand = 42;
        var workCall = new CilInstruction(CilOpCodes.Call, workDefinition);
        var map = new Dictionary<Instruction, List<CilInstruction>>
        {
            [branch] = [new(CilOpCodes.Ldarg_0), new(CilOpCodes.Brtrue, new CilInstructionLabel(rightStart))],
            [left] = [new(CilOpCodes.Ldc_I4, 42), new(CilOpCodes.Stloc, local)],
            [join] = [new(CilOpCodes.Br, new CilInstructionLabel(workCall))],
            [right] = assignRight ? [rightStart, new(CilOpCodes.Stloc, local)] : [rightStart],
            [call] = [workCall],
            [dispose] = [new(CilOpCodes.Ldloc, local), new(CilOpCodes.Call, cleanupDefinition)],
            [ret] = [new(CilOpCodes.Ret)]
        };
        foreach (var instruction in map.Values.SelectMany(i => i)) definition.CilMethodBody.Instructions.Add(instruction);
        ExceptionRegionRecovery.Apply(caller, definition, map);
        Assert.That(definition.CilMethodBody.ExceptionHandlers.Count, Is.EqualTo(assignRight ? 1 : 0));
        Assert.That(caller.AnalysisWarnings.Count, Is.EqualTo(assignRight ? 0 : 1));
        Assert.That(definition.CilMethodBody.ComputeMaxStack(), Is.EqualTo(1));
    }

    [TestCase(true)]
    [TestCase(false)]
    public void CleanupSequencesPreserveFlatOrNestedSemantics(bool nested)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Nested",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = owner.InjectMethodContext("M", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        MethodAnalysisContext Method(string name) => owner.InjectMethodContext(name, app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        var outer = Method("DisposeOuter");
        var inner = Method("DisposeInner");
        var work = Method("Work");
        Instruction At(ulong address, OpCode opcode, params IOperand[] operands)
            => new(0, opcode, operands.ToList()) { NativeAddress = address };
        var outerWork = At(0x1000, OpCode.CallVoid, work);
        var innerWork = At(0x1004, OpCode.CallVoid, work);
        var innerCopy = At(0x1008, OpCode.CallVoid, inner);
        var outerCopy = At(0x100C, OpCode.CallVoid, outer);
        var ret = At(0x1010, OpCode.Return);
        var exception = new Register(null, "X20");
        caller.ConvertedIsil = [outerWork, innerWork, innerCopy, outerCopy, ret,
            At(0x2000, OpCode.Move, exception, new Register(null, "X0")),
            At(0x2004, OpCode.CallVoid, inner), At(0x2008, OpCode.CallVoid, outer),
            At(0x200C, OpCode.CallVoid, new StringLiteral("_Unwind_Resume"), exception),
            At(0x3000, OpCode.Move, exception, new Register(null, "X0")),
            At(0x3004, OpCode.CallVoid, outer),
            At(0x3008, OpCode.CallVoid, new StringLiteral("_Unwind_Resume"), exception)];
        caller.UnwindInfo = new EhFunctionInfo { Start = 0x1000, Size = 0x2010 };
        foreach (var (start, pad) in nested ? new (ulong, ulong)[] { (0x1000, 0x3000), (0x1004, 0x2000), (0x1008, 0x3000) }
                     : new (ulong, ulong)[] { (0x1000, 0x2000), (0x1004, 0x2000) })
            caller.UnwindInfo.CallSites.Add(new EhCallSiteInfo(start, 4, pad, 0) { Actions = [new EhActionInfo(0, null)] });
        if (!nested) caller.ConvertedIsil.RemoveRange(caller.ConvertedIsil.Count - 3, 3);
        EhRegionPartition.Partition(caller);
        var module = new ModuleDefinition("NestedRegions.dll");
        MethodDefinition Definition(string name) => new(name, AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        var definition = Definition("M");
        definition.CilMethodBody = new();
        var outerDefinition = Definition("DisposeOuter");
        var innerDefinition = Definition("DisposeInner");
        var workDefinition = Definition("Work");
        outer.PutExtraData("AsmResolverMethod", outerDefinition);
        inner.PutExtraData("AsmResolverMethod", innerDefinition);
        var map = new Dictionary<Instruction, List<CilInstruction>>
        {
            [outerWork] = [new(CilOpCodes.Call, workDefinition)],
            [innerWork] = [new(CilOpCodes.Call, workDefinition)],
            [innerCopy] = [new(CilOpCodes.Call, innerDefinition)],
            [outerCopy] = [new(CilOpCodes.Call, outerDefinition)],
            [ret] = [new(CilOpCodes.Ret)]
        };
        foreach (var instruction in map.Values.SelectMany(x => x)) definition.CilMethodBody.Instructions.Add(instruction);
        ExceptionRegionRecovery.Apply(caller, definition, map);
        var body = definition.CilMethodBody;
        Assert.That(body.ExceptionHandlers, Has.Count.EqualTo(nested ? 2 : 1));
        int Position(ICilLabel? label) => body.Instructions.ToList().FindIndex(i => ReferenceEquals(i, ((CilInstructionLabel)label!).Instruction));
        var clauses = body.ExceptionHandlers.OrderBy(c => Position(c.TryStart)).ToList();
        if (nested)
        {
            Assert.That(Position(clauses[0].TryStart), Is.LessThan(Position(clauses[1].TryStart)));
            Assert.That(Position(clauses[1].HandlerEnd), Is.LessThan(Position(clauses[0].TryEnd)));
            Assert.That(body.Instructions[Position(clauses[0].HandlerStart)].Operand, Is.SameAs(outerDefinition));
            Assert.That(body.Instructions[Position(clauses[1].HandlerStart)].Operand, Is.SameAs(innerDefinition));
        }
        else
        {
            var start = Position(clauses[0].HandlerStart);
            Assert.That(body.Instructions[start].Operand, Is.SameAs(innerDefinition));
            Assert.That(body.Instructions[start + 1].Operand, Is.SameAs(outerDefinition));
        }
        Assert.That(caller.AnalysisWarnings, Is.Empty);
        Assert.That(body.ComputeMaxStack(), Is.EqualTo(0));

        var runtimeOwner = new TypeDefinition("Tests", "Nested", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(runtimeOwner);
        foreach (var method in new[] { definition, outerDefinition, innerDefinition, workDefinition })
        { method.Attributes |= AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public; runtimeOwner.Methods.Add(method); }
        var trace = new FieldDefinition("Trace", AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Static, module.CorLibTypeFactory.Int32);
        var fail = new FieldDefinition("Fail", AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Static, module.CorLibTypeFactory.Boolean);
        var failCleanup = new FieldDefinition("FailCleanup", AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Static, module.CorLibTypeFactory.Boolean);
        runtimeOwner.Fields.Add(trace);
        runtimeOwner.Fields.Add(fail);
        runtimeOwner.Fields.Add(failCleanup);
        foreach (var (method, digit) in new[] { (workDefinition, 1), (innerDefinition, 2), (outerDefinition, 3) })
        {
            method.CilMethodBody = new();
            var il = method.CilMethodBody.Instructions;
            il.Add(CilOpCodes.Ldsfld, trace); il.Add(CilOpCodes.Ldc_I4, 10); il.Add(CilOpCodes.Mul);
            il.Add(CilOpCodes.Ldc_I4, digit); il.Add(CilOpCodes.Add); il.Add(CilOpCodes.Stsfld, trace);
            if (method == workDefinition)
            {
                var done = new CilInstruction(CilOpCodes.Ret);
                il.Add(CilOpCodes.Ldsfld, fail); il.Add(CilOpCodes.Brfalse, new CilInstructionLabel(done));
                il.Add(CilOpCodes.Ldsfld, trace); il.Add(CilOpCodes.Ldc_I4, 11); il.Add(CilOpCodes.Bne_Un, new CilInstructionLabel(done));
                il.Add(CilOpCodes.Newobj, module.DefaultImporter.ImportMethod(typeof(Exception).GetConstructor(Type.EmptyTypes)!));
                il.Add(CilOpCodes.Throw); il.Add(done);
            }
            else if (method == innerDefinition)
            {
                var done = new CilInstruction(CilOpCodes.Ret);
                il.Add(CilOpCodes.Ldsfld, failCleanup); il.Add(CilOpCodes.Brfalse, new CilInstructionLabel(done));
                il.Add(CilOpCodes.Newobj, module.DefaultImporter.ImportMethod(typeof(Exception).GetConstructor(Type.EmptyTypes)!));
                il.Add(CilOpCodes.Throw); il.Add(done);
            }
            else il.Add(CilOpCodes.Ret);
        }
        var runtimeType = Load(module).GetType("Tests.Nested")!;
        var run = runtimeType.GetMethod("M")!;
        run.Invoke(null, null);
        Assert.That(runtimeType.GetField("Trace")!.GetValue(null), Is.EqualTo(1123), "normal exit runs inner, then outer cleanup once");
        runtimeType.GetField("Trace")!.SetValue(null, 0);
        runtimeType.GetField("Fail")!.SetValue(null, true);
        Assert.That(Assert.Throws<R.TargetInvocationException>(() => run.Invoke(null, null))!.InnerException, Is.TypeOf<Exception>());
        Assert.That(runtimeType.GetField("Trace")!.GetValue(null), Is.EqualTo(1123), "exceptional exit preserves the same cleanup order");
        runtimeType.GetField("Trace")!.SetValue(null, 0);
        runtimeType.GetField("Fail")!.SetValue(null, false);
        runtimeType.GetField("FailCleanup")!.SetValue(null, true);
        Assert.That(Assert.Throws<R.TargetInvocationException>(() => run.Invoke(null, null))!.InnerException, Is.TypeOf<Exception>());
        Assert.That(runtimeType.GetField("Trace")!.GetValue(null), Is.EqualTo(nested ? 1123 : 112),
            "a failed inner finally still runs its parent; a failed first call in one finally skips the second call");
    }

    [TestCase(0, 16, false)]
    [TestCase(1, 16, false)]
    [TestCase(2, 16, false)]
    [TestCase(3, 16, false)]
    [TestCase(4, 16, false)]
    [TestCase(0, 24, false)]
    [TestCase(0, 16, true)]
    public void DefaultsObjectCatchRequiresMatchingClassAndUnwind(int sourceShape, int offset, bool mismatchReturns)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimpleV106Game();
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "ObjectCatchOwner",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        MethodAnalysisContext Method(string name) => owner.InjectMethodContext(name, app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        var caller = Method("M"); var work = Method("Work"); var report = Method("Report");
        Instruction At(ulong address, OpCode op, params IOperand[] operands) => new(0, op, operands.ToList()) { NativeAddress = address };
        var x0 = new Register(null, "X0"); var saved = new Register(null, "X19");
        var exception = new Register(null, "X20"); var klass = new Register(null, "X21"); var flag = new Register(null, "condition");
        var call = At(0x1010, OpCode.CallVoid, work); var ret = At(0x1014, OpCode.Return);
        var mismatch = mismatchReturns ? At(0x2100, OpCode.Return)
            : At(0x2100, OpCode.CallVoid, new StringLiteral("il2cpp_raise_exception"), exception);
        var alternate = At(0x1008, OpCode.Move, saved, new MemoryOperand(addend: sourceShape == 3 ? 0xB100 : 0xA100));
        var source = sourceShape == 4 ? (IOperand)new Register(null, "unknown") : new MemoryOperand(addend: 0xA100);
        caller.ConvertedIsil = sourceShape is 2 or 3
            ? [At(0x1000, OpCode.ConditionalJump, alternate, flag), At(0x1004, OpCode.Move, saved, source),
                At(0x1006, OpCode.Jump, call), alternate, call, ret]
            : [At(0x1000, OpCode.Move, saved, source), call, ret];
        caller.ConvertedIsil.AddRange([
            At(0x2000, OpCode.Call, new StringLiteral("__cxa_begin_catch"), x0, x0),
            At(0x2004, OpCode.Move, exception, new MemoryOperand(x0)),
            At(0x2008, OpCode.Move, klass, new MemoryOperand(saved, addend: offset))]);
        if (sourceShape == 1) caller.ConvertedIsil.Add(At(0x200A, OpCode.Move, saved, klass));
        caller.ConvertedIsil.AddRange([
            At(0x200C, OpCode.Call, new StringLiteral("il2cpp_class_is_assignable_from"), x0,
                sourceShape == 1 ? saved : klass, new MemoryOperand(exception)),
            At(0x2010, OpCode.CheckEqual, flag, x0, new Immediate(0)),
            At(0x2014, OpCode.ConditionalJump, mismatch, flag), At(0x2018, OpCode.CallVoid, report),
            At(0x201C, OpCode.CallVoid, new StringLiteral("__cxa_end_catch")), At(0x2020, OpCode.Jump, ret), mismatch]);
        caller.UnwindInfo = new EhFunctionInfo { Start = 0x1000, Size = 0x1104 };
        caller.UnwindInfo.CallSites.Add(new EhCallSiteInfo(0x1010, 4, 0x2000, 1) { Actions = [new EhActionInfo(1, 0xABC)] });
        EhRegionPartition.Partition(caller);
        var proofs = new NativeExceptionRegionProof(caller).FindCatches(a => a == 0xABC);
        if (sourceShape is 3 or 4 || offset != 16 || mismatchReturns)
        {
            Assert.That(proofs, Is.Empty);
            Assert.That(caller.AnalysisWarnings, Has.Count.EqualTo(1)); return;
        }
        Assert.That(proofs, Has.Count.EqualTo(1));
        Assert.That(proofs[0].Type, Is.SameAs(app.SystemTypes.SystemObjectType));
        var module = new ModuleDefinition("ObjectCatch.dll");
        var type = new TypeDefinition("Tests", "ObjectCatchOwner", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var captured = new FieldDefinition("Caught", AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public | AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Static, module.CorLibTypeFactory.Boolean);
        type.Fields.Add(captured);
        MethodDefinition RuntimeMethod(string name)
        {
            var definition = new MethodDefinition(name, AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
                MethodSignature.CreateStatic(module.CorLibTypeFactory.Void)) { CilMethodBody = new() };
            type.Methods.Add(definition); return definition;
        }
        var throwing = RuntimeMethod("Work");
        // CLI catch System.Object must also accept a thrown non-Exception object.
        throwing.CilMethodBody!.Instructions.Add(CilOpCodes.Newobj, module.DefaultImporter.ImportMethod(typeof(object).GetConstructor(Type.EmptyTypes)!));
        throwing.CilMethodBody.Instructions.Add(CilOpCodes.Throw);
        var reporting = RuntimeMethod("Report");
        reporting.CilMethodBody!.Instructions.Add(CilOpCodes.Ldc_I4_1); reporting.CilMethodBody.Instructions.Add(CilOpCodes.Stsfld, captured); reporting.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        work.PutExtraData("AsmResolverMethod", throwing); report.PutExtraData("AsmResolverMethod", reporting);
        SyntheticFixture.SeedCorLibTypes(app, module, app.SystemTypes.SystemVoidType, app.SystemTypes.SystemStringType, app.SystemTypes.SystemObjectType);
        caller.ControlFlowGraph = new Cpp2IL.Core.Graphs.ISILControlFlowGraph([call, ret]); caller.Locals = [];
        var method = RuntimeMethod("M"); IlGenerator.GenerateIl(caller, method, proofs);
        Assert.That(method.CilMethodBody!.ExceptionHandlers, Has.Count.EqualTo(1));
        Assert.That(method.CilMethodBody.ExceptionHandlers[0].ExceptionType!.FullName, Is.EqualTo("System.Object"));
        // The fixture uses detached corlib definitions; bind the serialized references.
        method.CilMethodBody.ExceptionHandlers[0].ExceptionType = module.CorLibTypeFactory.Object.Type;
        foreach (var local in method.CilMethodBody.LocalVariables) local.VariableType = module.CorLibTypeFactory.Object;
        var runtime = Load(module).GetType("Tests.ObjectCatchOwner")!;
        Assert.DoesNotThrow(() => runtime.GetMethod("M")!.Invoke(null, null));
        Assert.That(runtime.GetField("Caught")!.GetValue(null), Is.True);
    }

    [TestCase(true, false, false, false)]
    [TestCase(false, false, false, false)]
    [TestCase(true, true, false, false)]
    [TestCase(false, true, false, false)]
    [TestCase(true, true, true, false)]
    [TestCase(true, true, true, true)]
    [TestCase(true, true, false, false, true)]
    [TestCase(true, true, true, false, false, true)]
    public void RecognizedTypeTestProducesCatchAndLeavesToNormalMerge(bool recognizedTypeTest, bool classTest, bool multipleCalls, bool returningHandler, bool normalTail = false, bool deadIncoming = false)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "CatchOwner",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var exceptionType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "SpecificException",
            app.SystemTypes.SystemExceptionType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = owner.InjectMethodContext("M", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        var work = owner.InjectMethodContext("Work", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        var report = owner.InjectMethodContext("Report", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, [exceptionType]);
        Instruction At(ulong address, OpCode opcode, params IOperand[] operands)
            => new(0, opcode, operands.ToList()) { NativeAddress = address };
        var x0 = new Register(null, "X0");
        var exception = new Register(null, "X19");
        var condition = new Register(null, "condition");
        var protectedCall = At(0x1000, OpCode.CallVoid, work);
        var secondCall = At(0x1004, OpCode.CallVoid, work);
        var merge = At(0x1008, OpCode.Return);
        var mismatch = At(0x2020, OpCode.CallVoid, new StringLiteral("il2cpp_raise_exception"), exception);
        caller.ConvertedIsil = [protectedCall, merge,
            At(0x2000, OpCode.Call, new StringLiteral("__cxa_begin_catch"), x0, x0),
            At(0x2004, OpCode.Move, exception, new MemoryOperand(x0, null, 0)),
            At(0x2008, OpCode.Call, new StringLiteral(recognizedTypeTest ? classTest ? "il2cpp_class_is_assignable_from" : "il2cpp_vm_object_is_inst" : "unknown_class_check"),
                x0, classTest ? exceptionType : exception, classTest ? new MemoryOperand(exception, null, 0) : exceptionType),
            At(0x200C, OpCode.CheckEqual, condition, x0, new Immediate(0)),
            At(0x2010, OpCode.ConditionalJump, mismatch, condition),
            At(0x2014, OpCode.CallVoid, report, exception),
            At(0x2018, OpCode.CallVoid, new StringLiteral("__cxa_end_catch")),
            returningHandler ? At(0x201C, OpCode.Return) : At(0x201C, OpCode.Jump, merge), mismatch];
        var deadJump = At(0x1010, OpCode.Jump, secondCall);
        if (deadIncoming) caller.ConvertedIsil.Insert(2, deadJump);
        if (multipleCalls || normalTail) caller.ConvertedIsil.Insert(1, secondCall);
        caller.UnwindInfo = new EhFunctionInfo { Start = 0x1000, Size = 0x1030 };
        caller.UnwindInfo.CallSites.Add(new EhCallSiteInfo(0x1000, multipleCalls ? 8UL : 4UL, 0x2000, 1)
            { Actions = [new EhActionInfo(1, 0xABC)] });
        EhRegionPartition.Partition(caller);
        // Synthetic RTTI fact. Actual action-chain and RTTI decoding is tested separately;
        // no game binary or metadata address is a condition in the recognizer.
        var proofs = new NativeExceptionRegionProof(caller).FindCatches(address => address == 0xABC);
        if (!recognizedTypeTest)
        {
            Assert.That(proofs, Is.Empty);
            Assert.That(caller.AnalysisWarnings, Has.Count.EqualTo(1));
            return;
        }
        var proof = proofs.Single();
        Assert.That(proof.Type, Is.SameAs(exceptionType));
        Assert.That(proof.ExceptionLocal.Type, Is.SameAs(exceptionType));
        Assert.That(proof.Handler.Single().Operands[1], Is.SameAs(proof.ExceptionLocal));
        var module = new ModuleDefinition("CatchRegions.dll");
        var catchTypeDefinition = new TypeDefinition("Tests", "SpecificException",
            AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public, module.DefaultImporter.ImportType(typeof(Exception)));
        module.TopLevelTypes.Add(catchTypeDefinition);
        exceptionType.PutExtraData("AsmResolverType", catchTypeDefinition);
        var definition = new MethodDefinition("M", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void)) { CilMethodBody = new() };
        var workDefinition = new MethodDefinition("Work", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        var reportDefinition = new MethodDefinition("Report", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [new TypeDefOrRefSignature(catchTypeDefinition, false)]));
        var local = new CilLocalVariable(new TypeDefOrRefSignature(catchTypeDefinition, false));
        definition.CilMethodBody.LocalVariables.Add(local);
        var map = new Dictionary<Instruction, List<CilInstruction>>
        {
            [protectedCall] = [new(CilOpCodes.Call, workDefinition)], [merge] = [new(CilOpCodes.Ret)]
        };
        if (multipleCalls || normalTail)
        {
            map.Remove(merge);
            map[secondCall] = [new(CilOpCodes.Call, workDefinition)];
            map[merge] = [new(CilOpCodes.Ret)];
        }
        foreach (var instruction in map.Values.SelectMany(x => x)) definition.CilMethodBody.Instructions.Add(instruction);
        if (deadIncoming)
        {
            map[deadJump] = [new(CilOpCodes.Br, new CilInstructionLabel(map[secondCall][0]))];
            definition.CilMethodBody.Instructions.Add(map[deadJump][0]);
        }
        ExceptionRegionRecovery.Apply(caller, definition, map, new()
        {
            [proof] = [new(CilOpCodes.Stloc, local), new(CilOpCodes.Ldloc, local), new(CilOpCodes.Call, reportDefinition)]
        });
        var clause = definition.CilMethodBody.ExceptionHandlers.Single();
        Assert.That(clause.HandlerType, Is.EqualTo(CilExceptionHandlerType.Exception));
        if (normalTail)
        {
            var instructions = definition.CilMethodBody.Instructions.ToList();
            var tail = instructions.FindIndex(i => ReferenceEquals(i, map[secondCall][0]));
            var start = instructions.IndexOf(((CilInstructionLabel)clause.TryStart!).Instruction!);
            var end = instructions.IndexOf(((CilInstructionLabel)clause.TryEnd!).Instruction!);
            Assert.That(tail < start || tail >= end, Is.True, "An uncovered SetResult must stay outside the try.");
        }
        Assert.That(clause.ExceptionType!.FullName, Is.EqualTo(catchTypeDefinition.FullName));
        var handlerStart = definition.CilMethodBody.Instructions.ToList().FindIndex(i => ReferenceEquals(i, ((CilInstructionLabel)clause.HandlerStart!).Instruction));
        var emitted = definition.CilMethodBody.Instructions.Skip(handlerStart).Take(4).ToList();
        Assert.That(emitted.Select(i => i.OpCode), Is.EqualTo(new[] { CilOpCodes.Stloc, CilOpCodes.Ldloc, CilOpCodes.Call, CilOpCodes.Leave }));
        Assert.That(((CilInstructionLabel)emitted[^1].Operand!).Instruction, Is.SameAs(map[merge][0]));
        Assert.That(caller.AnalysisWarnings, Is.Empty);
        Assert.That(definition.CilMethodBody.ComputeMaxStack(), Is.EqualTo(1));
        var runtimeOwner = new TypeDefinition("Tests", "CatchOwner", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(runtimeOwner);
        foreach (var method in new[] { definition, workDefinition, reportDefinition })
        { method.Attributes |= AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public; runtimeOwner.Methods.Add(method); }
        var captured = new FieldDefinition("Captured", AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Static, module.CorLibTypeFactory.Object);
        runtimeOwner.Fields.Add(captured);
        var ctor = new MethodDefinition(".ctor", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.SpecialName | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.RuntimeSpecialName,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void)) { CilMethodBody = new() };
        catchTypeDefinition.Methods.Add(ctor);
        ctor.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        ctor.CilMethodBody.Instructions.Add(CilOpCodes.Call, module.DefaultImporter.ImportMethod(typeof(Exception).GetConstructor(Type.EmptyTypes)!));
        ctor.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        workDefinition.CilMethodBody = new();
        workDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Newobj, ctor);
        workDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Throw);
        reportDefinition.CilMethodBody = new();
        reportDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        reportDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Stsfld, captured);
        reportDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        // Exercise the real emitter too: the catch's defining stloc is outside
        // the normal ISIL graph and must still define the exception argument.
        SyntheticFixture.SeedCorLibTypes(app, module, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemStringType, app.SystemTypes.SystemObjectType);
        work.PutExtraData("AsmResolverMethod", workDefinition);
        report.PutExtraData("AsmResolverMethod", reportDefinition);
        caller.ControlFlowGraph = new Cpp2IL.Core.Graphs.ISILControlFlowGraph(
            multipleCalls || normalTail ? [protectedCall, secondCall, merge] : [protectedCall, merge]);
        if (deadIncoming) caller.ControlFlowGraph = new Cpp2IL.Core.Graphs.ISILControlFlowGraph([protectedCall, secondCall, merge, deadJump]);
        caller.Locals = [];
        IlGenerator.GenerateIl(caller, definition, proofs);
        Assert.That(definition.CilMethodBody.ExceptionHandlers.Count, Is.EqualTo(1));
        Assert.That(definition.CilMethodBody.Instructions.Any(i => i.Operand is string text
            && text.Contains("Undefined local caughtException")), Is.False);
        var runtimeType = Load(module).GetType("Tests.CatchOwner")!;
        Assert.DoesNotThrow(() => runtimeType.GetMethod("M")!.Invoke(null, null));
        Assert.That(runtimeType.GetField("Captured")!.GetValue(null)!.GetType().FullName, Is.EqualTo("Tests.SpecificException"));
    }

    [TestCase(0, false, false)]
    [TestCase(1, false, false)]
    [TestCase(2, false, false)]
    [TestCase(3, false, false)]
    [TestCase(0, true, false)]
    [TestCase(0, false, true)]
    [TestCase(4, false, false)]
    [TestCase(5, false, false)]
    [TestCase(6, false, false)]
    [TestCase(6, true, false)]
    [TestCase(7, false, false)]
    public void CatchReturnPreservesItsOwnValue(int returnKind, bool unknownReturn, bool effectInEpilogue)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        TypeAnalysisContext resultType = returnKind == 4 ? new PointerTypeAnalysisContext(app.SystemTypes.SystemInt32Type)
            : returnKind == 5 ? new ByRefTypeAnalysisContext(app.SystemTypes.SystemInt32Type)
            : returnKind is 0 or 7 ? app.SystemTypes.SystemInt32Type : returnKind == 3 ? app.SystemTypes.SystemBooleanType : returnKind is 1 or 6 ? app.SystemTypes.SystemStringType : app.SystemTypes.SystemObjectType;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "ReturnCatch", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var caller = owner.InjectMethodContext("M", resultType, R.MethodAttributes.Public | R.MethodAttributes.Static,
            returnKind == 1 ? new[] { app.SystemTypes.SystemStringType }
                : returnKind == 6 ? new[] { app.SystemTypes.SystemStringType, app.SystemTypes.SystemStringType } : []);
        var work = owner.InjectMethodContext("Work", app.SystemTypes.SystemVoidType, R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        var text = owner.InjectMethodContext("Text", app.SystemTypes.SystemStringType, R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        Instruction At(ulong a, OpCode op, params IOperand[] args) => new(0, op, args.ToList()) { NativeAddress = a };
        var x0 = new Register(null, "X0"); var exception = new Register(null, "X20"); var saved = new Register(null, "X21"); var flag = new Register(null, "flag");
        var call = At(0x1000, OpCode.CallVoid, work);
        var ret = At(0x1010, OpCode.Return, x0);
        var merge = effectInEpilogue ? At(0x1008, OpCode.Move, new MemoryOperand(addend: 0x9000), new Immediate(1)) : ret;
        var mismatch = At(0x2100, OpCode.CallVoid, new StringLiteral("il2cpp_raise_exception"), exception);
        caller.ConvertedIsil = [call, At(0x1004, OpCode.Move, x0, new Immediate(7))];
        if (returnKind == 6)
        {
            caller.ParameterLocals = caller.Parameters.Select((p, i) =>
                new LocalVariable(p.ParameterName, new Register(null, "X" + i), p.ParameterType)).ToList();
            caller.ParameterOperands = caller.ParameterLocals.Select(l => (IOperand)l.Register).ToList();
            caller.ConvertedIsil.Insert(0, At(0xFFC, OpCode.Move, saved, new Register(null, "X1")));
        }
        if (returnKind == 7)
            caller.ConvertedIsil.InsertRange(0, [At(0xFF8, OpCode.Move, new Register(null, "X22"), new Immediate(0x9000)),
                At(0xFFC, OpCode.Move, new MemoryOperand(new Register(null, "X22")), new Immediate(7))]);
        if (effectInEpilogue) caller.ConvertedIsil.Add(merge);
        caller.ConvertedIsil.AddRange([ret,
            At(0x2000, OpCode.Call, new StringLiteral("__cxa_begin_catch"), x0, x0),
            At(0x2004, OpCode.Move, exception, new MemoryOperand(x0)),
            At(0x2008, OpCode.Call, new StringLiteral("il2cpp_class_is_assignable_from"), x0, app.SystemTypes.SystemExceptionType, new MemoryOperand(exception)),
            At(0x200C, OpCode.CheckEqual, flag, x0, new Immediate(0)), At(0x2010, OpCode.ConditionalJump, mismatch, flag)]);
        if (returnKind == 1) caller.ConvertedIsil.AddRange([At(0x2014, OpCode.Call, text, x0), At(0x2018, OpCode.Move, saved, x0)]);
        caller.ConvertedIsil.AddRange([
            At(0x201C, OpCode.CallVoid, new StringLiteral("__cxa_end_catch")),
            At(0x2020, OpCode.Move, x0, unknownReturn ? new Register(null, "unknown")
                : returnKind == 7 ? new MemoryOperand(new Register(null, "X22")) : returnKind == 0 ? new Immediate(-9) : returnKind is 3 or 4 or 5 ? new Immediate(0) : returnKind is 1 or 6 ? saved : exception),
            returnKind == 2 ? At(0x2024, OpCode.Return, x0) : At(0x2024, OpCode.Jump, merge), mismatch]);
        caller.UnwindInfo = new EhFunctionInfo { Start = returnKind == 7 ? 0xFF8UL : returnKind == 6 ? 0xFFCUL : 0x1000UL, Size = 0x1108 };
        caller.UnwindInfo.CallSites.Add(new EhCallSiteInfo(0x1000, 4, 0x2000, 1) { Actions = [new EhActionInfo(1, 0xABC)] });
        EhRegionPartition.Partition(caller);
        var proofs = new NativeExceptionRegionProof(caller).FindCatches(a => a == 0xABC);
        if (unknownReturn || effectInEpilogue || returnKind is 4 or 5 or 7)
        {
            Assert.That(proofs, Is.Empty); Assert.That(caller.AnalysisWarnings, Has.Count.EqualTo(1)); return;
        }
        Assert.That(proofs, Has.Count.EqualTo(1)); Assert.That(proofs[0].Return, Is.Not.Null);
        var module = new ModuleDefinition("ReturnCatch.dll");
        var runtimeOwner = new TypeDefinition("Tests", "ReturnCatch", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(runtimeOwner);
        var fail = new FieldDefinition("Fail", AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public | AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Static, module.CorLibTypeFactory.Boolean);
        var original = new FieldDefinition("Original", AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public | AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Static,
            new TypeDefOrRefSignature(module.DefaultImporter.ImportType(typeof(Exception)), false));
        runtimeOwner.Fields.Add(fail); runtimeOwner.Fields.Add(original);
        MethodDefinition RuntimeMethod(string name, TypeSignature result)
        {
            var m = new MethodDefinition(name, AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
                MethodSignature.CreateStatic(result)) { CilMethodBody = new() };
            runtimeOwner.Methods.Add(m); return m;
        }
        var workDefinition = RuntimeMethod("Work", module.CorLibTypeFactory.Void);
        var done = new CilInstruction(CilOpCodes.Ret);
        workDefinition.CilMethodBody!.Instructions.Add(CilOpCodes.Ldsfld, fail);
        workDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Brfalse, new CilInstructionLabel(done));
        workDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Ldsfld, original); workDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Throw); workDefinition.CilMethodBody.Instructions.Add(done);
        var textDefinition = RuntimeMethod("Text", module.CorLibTypeFactory.String);
        textDefinition.CilMethodBody!.Instructions.Add(CilOpCodes.Ldstr, "caught"); textDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        work.PutExtraData("AsmResolverMethod", workDefinition); text.PutExtraData("AsmResolverMethod", textDefinition);
        SyntheticFixture.SeedCorLibTypes(app, module, app.SystemTypes.SystemVoidType, app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemStringType, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemExceptionType);
        var normal = At(0x1010, OpCode.Return, returnKind == 0 ? new Immediate(7) : returnKind == 3 ? new Immediate(1) : new StringLiteral("normal"));
        caller.ControlFlowGraph = new Cpp2IL.Core.Graphs.ISILControlFlowGraph([call, normal]); caller.Locals = [];
        var definition = RuntimeMethod("M", returnKind == 0 ? module.CorLibTypeFactory.Int32 : returnKind == 3 ? module.CorLibTypeFactory.Boolean : returnKind is 1 or 6 ? module.CorLibTypeFactory.String : module.CorLibTypeFactory.Object);
        foreach (var p in caller.Parameters)
        {
            definition.Signature!.ParameterTypes.Add(module.CorLibTypeFactory.String);
            definition.ParameterDefinitions.Add(new ParameterDefinition((ushort)(p.ParameterIndex + 1), p.ParameterName, default));
        }
        IlGenerator.GenerateIl(caller, definition, proofs);
        var body = definition.CilMethodBody!; Assert.That(body.ExceptionHandlers, Has.Count.EqualTo(1)); Assert.That(caller.AnalysisWarnings, Is.Empty);
        body.ExceptionHandlers[0].ExceptionType = module.DefaultImporter.ImportType(typeof(Exception));
        foreach (var local in body.LocalVariables)
            local.VariableType = local.VariableType.FullName == "System.String" ? module.CorLibTypeFactory.String : new TypeDefOrRefSignature(module.DefaultImporter.ImportType(typeof(Exception)), false);
        var runtime = Load(module).GetType("Tests.ReturnCatch")!; var run = runtime.GetMethod("M")!;
        object[]? inputs = returnKind == 1 ? ["parameter"] : returnKind == 6 ? ["first", "second"] : null;
        Assert.That(run.Invoke(null, inputs), Is.EqualTo(returnKind == 0 ? (object)7 : returnKind == 3 ? true : "normal"));
        var thrown = new Exception("original"); runtime.GetField("Original")!.SetValue(null, thrown); runtime.GetField("Fail")!.SetValue(null, true);
        var value = run.Invoke(null, inputs);
        if (returnKind == 2) Assert.That(value, Is.SameAs(thrown));
        else Assert.That(value, Is.EqualTo(returnKind == 0 ? (object)(-9) : returnKind == 3 ? false : returnKind == 6 ? "second" : "caught"));
        var clause = body.ExceptionHandlers[0];
        var handlerStart = body.Instructions.IndexOf(((CilInstructionLabel)clause.HandlerStart!).Instruction!);
        var handlerEnd = body.Instructions.IndexOf(((CilInstructionLabel)clause.HandlerEnd!).Instruction!);
        Assert.That(body.Instructions.Skip(handlerStart).Take(handlerEnd-handlerStart).Any(i=>i.OpCode.Code==CilCode.Ret), Is.False);
    }

    [Test]
    public void DisjointCatchRangesLeaveInterveningCallUnprotected()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "SplitCatch",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var caller = owner.InjectMethodContext("M", app.SystemTypes.SystemVoidType, R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        var work = owner.InjectMethodContext("Work", app.SystemTypes.SystemVoidType, R.MethodAttributes.Public | R.MethodAttributes.Static, [app.SystemTypes.SystemInt32Type]);
        var report = owner.InjectMethodContext("Report", app.SystemTypes.SystemVoidType, R.MethodAttributes.Public | R.MethodAttributes.Static, [app.SystemTypes.SystemExceptionType]);
        Instruction At(ulong address, OpCode op, params IOperand[] operands) => new(0, op, operands.ToList()) { NativeAddress = address };
        var first = At(0x1000, OpCode.CallVoid, work, new Immediate(1));
        var uncovered = At(0x1004, OpCode.CallVoid, work, new Immediate(2));
        var last = At(0x1008, OpCode.CallVoid, work, new Immediate(3));
        var ret = At(0x100C, OpCode.Return);
        var x0 = new Register(null, "X0"); var exception = new Register(null, "X19"); var flag = new Register(null, "flag");
        var mismatch = At(0x2100, OpCode.CallVoid, new StringLiteral("il2cpp_raise_exception"), exception);
        caller.ConvertedIsil = [first, uncovered, last, ret,
            At(0x2000, OpCode.Call, new StringLiteral("__cxa_begin_catch"), x0, x0),
            At(0x2004, OpCode.Move, exception, new MemoryOperand(x0)),
            At(0x2008, OpCode.Call, new StringLiteral("il2cpp_class_is_assignable_from"), x0, app.SystemTypes.SystemExceptionType, new MemoryOperand(exception)),
            At(0x200C, OpCode.CheckEqual, flag, x0, new Immediate(0)),
            At(0x2010, OpCode.ConditionalJump, mismatch, flag),
            At(0x2014, OpCode.CallVoid, report, exception),
            At(0x2018, OpCode.CallVoid, new StringLiteral("__cxa_end_catch")), At(0x201C, OpCode.Jump, ret), mismatch];
        caller.UnwindInfo = new EhFunctionInfo { Start = 0x1000, Size = 0x1104 };
        foreach (var address in new ulong[] { 0x1000, 0x1008 })
            caller.UnwindInfo.CallSites.Add(new EhCallSiteInfo(address, 4, 0x2000, 1) { Actions = [new EhActionInfo(1, 0xABC)] });
        EhRegionPartition.Partition(caller);
        var proofs = new NativeExceptionRegionProof(caller).FindCatches(a => a == 0xABC);
        Assert.That(proofs, Has.Count.EqualTo(1));
        var module = new ModuleDefinition("SplitCatch.dll");
        var runtimeOwner = new TypeDefinition("Tests", "SplitCatch", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(runtimeOwner);
        var exceptionType = new TypeDefinition("Tests", "SplitException", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public, module.DefaultImporter.ImportType(typeof(Exception)));
        module.TopLevelTypes.Add(exceptionType);
        var ctor = new MethodDefinition(".ctor", AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.SpecialName | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.RuntimeSpecialName,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void)) { CilMethodBody = new() };
        exceptionType.Methods.Add(ctor);
        ctor.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_0);
        ctor.CilMethodBody.Instructions.Add(CilOpCodes.Call, module.DefaultImporter.ImportMethod(typeof(Exception).GetConstructor(Type.EmptyTypes)!));
        ctor.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        var throwAt = new FieldDefinition("ThrowAt", AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public | AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Static, module.CorLibTypeFactory.Int32);
        var caught = new FieldDefinition("Caught", throwAt.Attributes, module.CorLibTypeFactory.Int32);
        runtimeOwner.Fields.Add(throwAt); runtimeOwner.Fields.Add(caught);
        MethodDefinition Method(string name, params TypeSignature[] parameters)
        {
            var method = new MethodDefinition(name, AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static,
                MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, parameters)) { CilMethodBody = new() };
            runtimeOwner.Methods.Add(method); return method;
        }
        var workDefinition = Method("Work", module.CorLibTypeFactory.Int32);
        var workRet = new CilInstruction(CilOpCodes.Ret);
        var body = workDefinition.CilMethodBody!.Instructions;
        body.Add(CilOpCodes.Ldarg_0); body.Add(CilOpCodes.Ldsfld, throwAt); body.Add(CilOpCodes.Bne_Un, new CilInstructionLabel(workRet));
        body.Add(CilOpCodes.Newobj, ctor); body.Add(CilOpCodes.Throw); body.Add(workRet);
        var reportDefinition = Method("Report", module.DefaultImporter.ImportTypeSignature(typeof(Exception)));
        reportDefinition.CilMethodBody!.Instructions.Add(CilOpCodes.Ldc_I4_1); reportDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Stsfld, caught); reportDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        work.PutExtraData("AsmResolverMethod", workDefinition); report.PutExtraData("AsmResolverMethod", reportDefinition);
        SyntheticFixture.SeedCorLibTypes(app, module, app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemStringType, app.SystemTypes.SystemInt32Type);
        app.SystemTypes.SystemExceptionType.PutExtraData("AsmResolverType", exceptionType);
        caller.ControlFlowGraph = new Cpp2IL.Core.Graphs.ISILControlFlowGraph([first, uncovered, last, ret]); caller.Locals = [];
        var definition = Method("M"); IlGenerator.GenerateIl(caller, definition, proofs);
        Assert.That(definition.CilMethodBody!.ExceptionHandlers, Has.Count.EqualTo(2));
        var runtime = Load(module).GetType("Tests.SplitCatch")!;
        foreach (var index in new[] { 0, 1, 2, 3 })
        {
            runtime.GetField("ThrowAt")!.SetValue(null, index); runtime.GetField("Caught")!.SetValue(null, 0);
            if (index == 2) Assert.Throws<R.TargetInvocationException>(() => runtime.GetMethod("M")!.Invoke(null, null));
            else Assert.DoesNotThrow(() => runtime.GetMethod("M")!.Invoke(null, null));
            Assert.That(runtime.GetField("Caught")!.GetValue(null), Is.EqualTo(index is 1 or 3 ? 1 : 0));
        }
    }

    [TestCase(false, false, false)]
    [TestCase(true, false, false)]
    [TestCase(false, true, false)]
    [TestCase(false, false, true)]
    [TestCase(true, false, false, 1)]
    [TestCase(true, false, false, 2)]
    [TestCase(true, false, false, 3)]
    public void CatchVirtualResultAndClassInitializationExecute(bool initializeClass, bool wrongMethodInfo, bool wrongReceiver, int badGuard = 0)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "VirtualCatchOwner",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var caughtType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "DerivedException",
            app.SystemTypes.SystemExceptionType, R.TypeAttributes.Public);
        var marker = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Initialized",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var caller = owner.InjectMethodContext("M", app.SystemTypes.SystemVoidType, R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        var work = owner.InjectMethodContext("Work", app.SystemTypes.SystemVoidType, R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        var report = owner.InjectMethodContext("Report", app.SystemTypes.SystemVoidType, R.MethodAttributes.Public | R.MethodAttributes.Static,
            [app.SystemTypes.SystemStringType, app.SystemTypes.SystemStringType]);
        if (initializeClass)
        {
            // This fixture strips the public helper; seed the normal BCL contract.
            var core = app.SystemTypes.SystemObjectType.DeclaringAssembly;
            var helpers = core.Types.FirstOrDefault(t => t.FullName == "System.Runtime.CompilerServices.RuntimeHelpers");
            if (helpers == null)
            {
                helpers = new InjectedTypeAnalysisContext(core, "System.Runtime.CompilerServices", "RuntimeHelpers", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
                core.Types.Add(helpers);
            }
            var handle = core.Types.Single(t => t.FullName == "System.RuntimeTypeHandle");
            helpers.Methods.Add(new InjectedMethodAnalysisContext(helpers, "RunClassConstructor", app.SystemTypes.SystemVoidType,
                R.MethodAttributes.Public | R.MethodAttributes.Static, [handle]));
        }
        var getter = app.SystemTypes.SystemExceptionType.Methods.Single(m => m.Name == "get_Message");
        var slotOffset = Il2CppClassUsefulOffsets.GetVtableOffset(app.MetadataVersion, false) + 16 * getter.Definition!.slot;
        var x0 = new Register(null, "X0");
        var x1 = new Register(null, "X1");
        var exception = new Register(null, "X19");
        var savedResult = new Register(null, "X20");
        var klass = new Register(null, "X8");
        var target = new Register(null, "X9");
        var condition = new Register(null, "condition");
        Instruction At(ulong address, OpCode op, params IOperand[] operands) => new(0, op, operands.ToList()) { NativeAddress = address };
        var protectedCall = At(0x1000, OpCode.CallVoid, work);
        var ret = At(0x1004, OpCode.Return);
        var mismatch = At(0x2100, OpCode.CallVoid, new StringLiteral("il2cpp_raise_exception"), exception);
        var reportCall = At(0x2040, OpCode.CallVoid, report, savedResult, new StringLiteral(" suffix"));
        caller.ConvertedIsil = [protectedCall, ret,
            At(0x2000, OpCode.Call, new StringLiteral("__cxa_begin_catch"), x0, x0),
            At(0x2004, OpCode.Move, exception, new MemoryOperand(x0)),
            At(0x2008, OpCode.Call, new StringLiteral("il2cpp_class_is_assignable_from"), x0, caughtType, new MemoryOperand(exception)),
            At(0x200C, OpCode.CheckEqual, condition, x0, new Immediate(0)),
            At(0x2010, OpCode.ConditionalJump, mismatch, condition),
            At(0x2014, OpCode.Move, klass, new MemoryOperand(exception)),
            At(0x2018, OpCode.Move, target, new MemoryOperand(klass, addend: slotOffset)),
            At(0x201C, OpCode.Move, x1, new MemoryOperand(klass, addend: slotOffset + (wrongMethodInfo ? 24 : 8))),
            At(0x2020, OpCode.Move, x0, wrongReceiver ? new Immediate(0) : exception),
            At(0x2024, OpCode.IndirectCall, target, x0, x0, x1),
            At(0x2028, OpCode.Move, savedResult, x0)];
        if (initializeClass)
            caller.ConvertedIsil.AddRange([
                At(0x202C, OpCode.Move, x0, marker),
                At(0x2030, OpCode.Move, klass, new MemoryOperand(x0, addend: (app.MetadataVersion >= 29 ? 0xE4 : 0xE0) + (badGuard == 1 ? 4 : 0))),
                At(0x2034, OpCode.CheckEqual, condition, klass, new Immediate(0)),
                At(0x2034, OpCode.Not, condition, condition),
                At(0x2034, OpCode.ConditionalJump, reportCall, condition),
                At(0x2038, OpCode.CallVoid, new StringLiteral("il2cpp_codegen_runtime_class_init"), badGuard == 2 ? owner : x0)]);
        if (badGuard == 3) caller.ConvertedIsil.Add(At(0x203C, OpCode.Move, new MemoryOperand(exception), new Immediate(0)));
        caller.ConvertedIsil.AddRange([reportCall,
            At(0x2044, OpCode.CallVoid, new StringLiteral("__cxa_end_catch")), At(0x2048, OpCode.Jump, ret), mismatch]);
        caller.UnwindInfo = new EhFunctionInfo { Start = 0x1000, Size = 0x1104 };
        caller.UnwindInfo.CallSites.Add(new EhCallSiteInfo(0x1000, 4, 0x2000, 1) { Actions = [new EhActionInfo(1, 0xABC)] });
        EhRegionPartition.Partition(caller);
        var proofs = new NativeExceptionRegionProof(caller).FindCatches(a => a == 0xABC);
        if (wrongMethodInfo || wrongReceiver || badGuard != 0) { Assert.That(proofs, Is.Empty); return; }
        Assert.That(proofs, Has.Count.EqualTo(1));

        var module = new ModuleDefinition("VirtualCatch.dll");
        const AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes publicMethod = AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Public;
        var runtimeOwner = new TypeDefinition("Tests", "VirtualCatchOwner", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        var baseException = new TypeDefinition("Tests", "BaseException", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public, module.DefaultImporter.ImportType(typeof(Exception)));
        var derivedException = new TypeDefinition("Tests", "DerivedException", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public, baseException);
        var initializedType = new TypeDefinition("Tests", "Initialized", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        foreach (var type in new[] { runtimeOwner, baseException, derivedException, initializedType }) module.TopLevelTypes.Add(type);
        caughtType.PutExtraData("AsmResolverType", derivedException);
        marker.PutExtraData("AsmResolverType", initializedType);
        var captured = new FieldDefinition("Captured", AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public | AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Static, module.CorLibTypeFactory.String);
        var initCount = new FieldDefinition("InitCount", captured.Attributes, module.CorLibTypeFactory.Int32);
        runtimeOwner.Fields.Add(captured); runtimeOwner.Fields.Add(initCount);
        MethodDefinition Method(TypeDefinition type, string name, MethodSignature signature, AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes attributes = publicMethod)
        {
            var method = new MethodDefinition(name, attributes, signature) { CilMethodBody = new() };
            type.Methods.Add(method); return method;
        }
        MethodDefinition Constructor(TypeDefinition type, IMethodDescriptor parent)
        {
            var constructor = Method(type, ".ctor", MethodSignature.CreateInstance(module.CorLibTypeFactory.Void), publicMethod
                | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.SpecialName | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.RuntimeSpecialName);
            constructor.CilMethodBody!.Instructions.Add(CilOpCodes.Ldarg_0);
            constructor.CilMethodBody.Instructions.Add(CilOpCodes.Call, parent);
            constructor.CilMethodBody.Instructions.Add(CilOpCodes.Ret); return constructor;
        }
        var ctor = Constructor(derivedException, Constructor(baseException, module.DefaultImporter.ImportMethod(typeof(Exception).GetConstructor(Type.EmptyTypes)!)));
        var virtualGetter = Method(baseException, "get_Message", MethodSignature.CreateInstance(module.CorLibTypeFactory.String), publicMethod
            | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Virtual | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.NewSlot);
        virtualGetter.CilMethodBody!.Instructions.Add(CilOpCodes.Ldstr, "base"); virtualGetter.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        var overrideGetter = Method(derivedException, "get_Message", virtualGetter.Signature!, publicMethod | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Virtual);
        overrideGetter.CilMethodBody!.Instructions.Add(CilOpCodes.Ldstr, "derived"); overrideGetter.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        getter.PutExtraData("AsmResolverMethod", virtualGetter);
        var workDefinition = Method(runtimeOwner, "Work", MethodSignature.CreateStatic(module.CorLibTypeFactory.Void), publicMethod | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static);
        workDefinition.CilMethodBody!.Instructions.Add(CilOpCodes.Newobj, ctor); workDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Throw);
        var reportDefinition = Method(runtimeOwner, "Report", MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [module.CorLibTypeFactory.String, module.CorLibTypeFactory.String]), workDefinition.Attributes);
        reportDefinition.CilMethodBody!.Instructions.Add(CilOpCodes.Ldarg_0); reportDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Ldarg_1);
        reportDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Call, module.DefaultImporter.ImportMethod(typeof(string).GetMethod("Concat", [typeof(string), typeof(string)])!));
        reportDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Stsfld, captured); reportDefinition.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        work.PutExtraData("AsmResolverMethod", workDefinition); report.PutExtraData("AsmResolverMethod", reportDefinition);
        var initializer = Method(initializedType, ".cctor", MethodSignature.CreateStatic(module.CorLibTypeFactory.Void), AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.Static
            | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.SpecialName | AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes.RuntimeSpecialName);
        initializer.CilMethodBody!.Instructions.Add(CilOpCodes.Ldsfld, initCount); initializer.CilMethodBody.Instructions.Add(CilOpCodes.Ldc_I4_1); initializer.CilMethodBody.Instructions.Add(CilOpCodes.Add); initializer.CilMethodBody.Instructions.Add(CilOpCodes.Stsfld, initCount); initializer.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        if (initializeClass)
        {
            var run = proofs[0].Handler.Select(i => i.Operands[0]).OfType<MethodAnalysisContext>().Single(m => m.Name == "RunClassConstructor");
            var wrapper = Method(runtimeOwner, "RunClassConstructor", MethodSignature.CreateStatic(module.CorLibTypeFactory.Void, [module.DefaultImporter.ImportTypeSignature(typeof(RuntimeTypeHandle))]), workDefinition.Attributes);
            wrapper.CilMethodBody!.Instructions.Add(CilOpCodes.Ldarg_0);
            wrapper.CilMethodBody.Instructions.Add(CilOpCodes.Call, module.DefaultImporter.ImportMethod(typeof(System.Runtime.CompilerServices.RuntimeHelpers).GetMethod("RunClassConstructor")!));
            wrapper.CilMethodBody.Instructions.Add(CilOpCodes.Ret); run.PutExtraData("AsmResolverMethod", wrapper);
        }
        SyntheticFixture.SeedCorLibTypes(app, module, app.SystemTypes.SystemVoidType, app.SystemTypes.SystemStringType, app.SystemTypes.SystemObjectType);
        caller.ControlFlowGraph = new Cpp2IL.Core.Graphs.ISILControlFlowGraph([protectedCall, ret]); caller.Locals = [];
        var definition = Method(runtimeOwner, "M", workDefinition.Signature!, workDefinition.Attributes);
        IlGenerator.GenerateIl(caller, definition, proofs);
        Assert.That(definition.CilMethodBody!.ExceptionHandlers, Has.Count.EqualTo(1));
        // Fixture type definitions are detached; bind reference-result locals to corlib.
        foreach (var local in definition.CilMethodBody.LocalVariables.Where(l => l.VariableType.FullName == "System.String"))
            local.VariableType = module.CorLibTypeFactory.String;
        var runtime = Load(module).GetType("Tests.VirtualCatchOwner")!;
        runtime.GetMethod("M")!.Invoke(null, null);
        runtime.GetMethod("M")!.Invoke(null, null);
        Assert.That(runtime.GetField("Captured")!.GetValue(null), Is.EqualTo("derived suffix"));
        Assert.That(runtime.GetField("InitCount")!.GetValue(null), Is.EqualTo(initializeClass ? 1 : 0));
    }

    [TestCase(4, false, true)]
    [TestCase(8, false, false)]
    [TestCase(4, true, false)]
    public void CatchPreservesStateStoreAndBuilderReceiver(int storeWidth, bool lostReceiver, bool expected)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "StateMachine",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var builder = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Builder",
            app.AllTypes.Single(t => t.FullName == "System.ValueType"), R.TypeAttributes.Public | R.TypeAttributes.SequentialLayout);
        var stateField = owner.InjectFieldContext("State", app.SystemTypes.SystemInt32Type, R.FieldAttributes.Public);
        stateField.Offset = 16;
        var builderField = owner.InjectFieldContext("Builder", builder, R.FieldAttributes.Public);
        builderField.Offset = 24;
        var setException = builder.InjectMethodContext("SetException", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public, [app.SystemTypes.SystemExceptionType]);
        var caller = owner.InjectMethodContext("MoveNext", app.SystemTypes.SystemVoidType, R.MethodAttributes.Public, []);
        var work = owner.InjectMethodContext("Work", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        var x0 = new Register(null, "X0");
        var self = new Register(null, lostReceiver ? "X9" : "X19");
        var exception = new Register(null, "X20");
        var condition = new Register(null, "condition");
        caller.ParameterOperands = [x0];
        caller.ParameterLocals = [new LocalVariable("this", x0, owner) { IsThis = true }];
        Instruction At(ulong address, OpCode op, params IOperand[] operands)
            => new(0, op, operands.ToList()) { NativeAddress = address };
        var merge = At(0x1010, OpCode.Return);
        var mismatch = At(0x2030, OpCode.CallVoid, new StringLiteral("il2cpp_raise_exception"), exception);
        var store = At(0x2014, OpCode.Move, new MemoryOperand(self, null, 16), new Immediate(-2));
        store.NativeStoreWidthBytes = storeWidth;
        caller.ConvertedIsil = [At(0x1000, OpCode.Move, self, x0), At(0x1004, OpCode.CallVoid, work), merge,
            At(0x2000, OpCode.Call, new StringLiteral("__cxa_begin_catch"), x0, x0),
            At(0x2004, OpCode.Move, exception, new MemoryOperand(x0)),
            At(0x2008, OpCode.Call, new StringLiteral("il2cpp_class_is_assignable_from"), x0,
                app.SystemTypes.SystemExceptionType, new MemoryOperand(exception)),
            At(0x200C, OpCode.CheckEqual, condition, x0, new Immediate(0)),
            At(0x2010, OpCode.ConditionalJump, mismatch, condition), store,
            At(0x2018, OpCode.Add, x0, self, new Immediate(24)),
            At(0x201C, OpCode.CallVoid, setException, x0, exception),
            At(0x2020, OpCode.CallVoid, new StringLiteral("__cxa_end_catch")),
            At(0x2024, OpCode.Jump, merge), mismatch];
        caller.UnwindInfo = new EhFunctionInfo { Start = 0x1000, Size = 0x1040 };
        caller.UnwindInfo.CallSites.Add(new EhCallSiteInfo(0x1004, 4, 0x2000, 1) { Actions = [new EhActionInfo(1, 0xABC)] });
        EhRegionPartition.Partition(caller);
        var proofs = new NativeExceptionRegionProof(caller).FindCatches(a => a == 0xABC);
        Assert.That(proofs.Count, Is.EqualTo(expected ? 1 : 0));
        if (!expected) return;
        var handler = proofs.Single().Handler;
        Assert.That(handler.Count, Is.EqualTo(2));
        Assert.That(((FieldReference)handler[0].Operands[0]).Field, Is.SameAs(stateField));
        Assert.That(((Immediate)handler[0].Operands[1]).Value, Is.EqualTo(-2));
        Assert.That(((FieldReference)((AddressOf)handler[1].Operands[1]).Target).Field, Is.SameAs(builderField));
        Assert.That(handler[1].Operands[2], Is.SameAs(proofs[0].ExceptionLocal));
    }

    [TestCase(false, false, false, true)]
    [TestCase(true, false, false, false)]
    [TestCase(false, true, false, false)]
    [TestCase(false, false, true, false)]
    [TestCase(false, false, false, true, 0)]
    [TestCase(false, false, false, true, 8)]
    public void ReturningCleanupClosureMustContinueToOriginalUnwind(bool differentArgument, bool extraStore,
        bool returnsInsteadOfUnwinding, bool expected, int scale = -1)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "ClosureOwner",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        MethodAnalysisContext Method(string name) => owner.InjectMethodContext(name, app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, []);
        var caller = Method("Caller");
        var work = Method("Work");
        var cleanup = Method("Dispose");
        var x0 = new Register(null, "X0");
        var exception = new Register(null, "X20");
        var receiver = new StackOffset(8);
        Instruction At(ulong address, OpCode op, params IOperand[] operands)
            => new(0, op, operands.ToList()) { NativeAddress = address };
        caller.ConvertedIsil = [At(0x1000, OpCode.Move, receiver, new Immediate(42)),
            At(0x1004, OpCode.CallVoid, work), At(0x1008, OpCode.CallVoid, cleanup, new Immediate(42)),
            At(0x100C, OpCode.Return), At(0x2000, OpCode.Move, exception, x0),
            At(0x2004, OpCode.Move, x0, new AddressOf(scale >= 0 ? new StackOffset(0) : receiver)),
            At(0x2008, OpCode.CallVoid, new Immediate(0x3000), x0),
            returnsInsteadOfUnwinding ? At(0x200C, OpCode.Return)
                : At(0x200C, OpCode.CallVoid, new StringLiteral("_Unwind_Resume"), exception)];
        var closure = new List<Instruction> {
            At(0x3000, OpCode.ShiftStack, new Immediate(-16)),
            At(0x3004, OpCode.Move, new StackOffset(0), exception),
            At(0x3008, OpCode.Move, x0, differentArgument ? new Immediate(43)
                : new MemoryOperand(x0, scale >= 0 ? new Register(null, "X21") : null, scale: scale >= 0 ? scale : 0)),
            At(0x300C, OpCode.CallVoid, cleanup, x0),
            At(0x3010, OpCode.Move, exception, new StackOffset(0)),
            At(0x3014, OpCode.ShiftStack, new Immediate(16)), At(0x3018, OpCode.Return) };
        if (scale >= 0) closure.Insert(2, At(0x3006, OpCode.Move, new Register(null, "X21"), new Immediate(scale > 1 ? 1 : 8)));
        if (extraStore) closure.Insert(3, At(0x300A, OpCode.Move, new MemoryOperand(addend: 0x9000), new Immediate(1)));
        caller.UnwindInfo = new EhFunctionInfo { Start = 0x1000, Size = 0x1010 };
        caller.UnwindInfo.CallSites.Add(new EhCallSiteInfo(0x1004, 4, 0x2000, 0) { Actions = [new EhActionInfo(0, null)] });
        EhRegionPartition.Partition(caller);
        var proofs = new NativeExceptionRegionProof(caller, address => address == 0x3000 ? closure : null).Find();
        Assert.That(proofs.Count, Is.EqualTo(expected ? 1 : 0));
        if (expected) Assert.That(proofs[0].CleanupCalls.Single(), Is.EqualTo(new[] { 0x1008UL }));
    }

    [TestCase(false)]
    [TestCase(true)]
    [TestCase(false, true)]
    public void SharedCatchGroupsCompareTheFullCalleeSignature(bool differentOverload, bool differentAssembly = false)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Overloads",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var attributes = R.MethodAttributes.Public | R.MethodAttributes.Static;
        var caller = owner.InjectMethodContext("M", app.SystemTypes.SystemVoidType, attributes, []);
        var work = owner.InjectMethodContext("Work", app.SystemTypes.SystemVoidType, attributes, []);
        var report = owner.InjectMethodContext("Report", app.SystemTypes.SystemVoidType, attributes,
            [app.SystemTypes.SystemExceptionType, app.SystemTypes.SystemInt32Type]);
        var otherOwner = differentAssembly ? new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Overloads", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class) : owner;
        var other = differentOverload || differentAssembly ? otherOwner.InjectMethodContext("Report", app.SystemTypes.SystemVoidType, attributes,
            [app.SystemTypes.SystemExceptionType, differentOverload ? app.SystemTypes.SystemInt64Type : app.SystemTypes.SystemInt32Type]) : report;
        Instruction At(ulong address, OpCode op, params IOperand[] operands)
            => new(0, op, operands.ToList()) { NativeAddress = address };
        var ret = At(0x1008, OpCode.Return);
        caller.ConvertedIsil = [At(0x1000, OpCode.CallVoid, work), At(0x1004, OpCode.CallVoid, work), ret];
        caller.UnwindInfo = new EhFunctionInfo { Start = 0x1000, Size = 0x2040 };
        foreach (var (pad, start, target) in new[] { (0x2000UL, 0x1000UL, report), (0x3000UL, 0x1004UL, other) })
        {
            var x0 = new Register(null, "X0");
            var exception = new Register(null, "X19");
            var condition = new Register(null, "condition");
            var mismatch = At(pad + 32, OpCode.CallVoid, new StringLiteral("il2cpp_raise_exception"), exception);
            caller.ConvertedIsil.AddRange([
                At(pad, OpCode.Call, new StringLiteral("__cxa_begin_catch"), x0, x0),
                At(pad + 4, OpCode.Move, exception, new MemoryOperand(x0)),
                At(pad + 8, OpCode.Call, new StringLiteral("il2cpp_class_is_assignable_from"), x0,
                    app.SystemTypes.SystemExceptionType, new MemoryOperand(exception)),
                At(pad + 12, OpCode.CheckEqual, condition, x0, new Immediate(0)),
                At(pad + 16, OpCode.ConditionalJump, mismatch, condition),
                At(pad + 20, OpCode.CallVoid, target, exception, new Immediate(1)),
                At(pad + 24, OpCode.CallVoid, new StringLiteral("__cxa_end_catch")),
                At(pad + 28, OpCode.Jump, ret), mismatch]);
            caller.UnwindInfo.CallSites.Add(new EhCallSiteInfo(start, 4, pad, 1) { Actions = [new EhActionInfo(1, 0xABC)] });
        }
        EhRegionPartition.Partition(caller);
        Assert.That(new NativeExceptionRegionProof(caller).FindCatches(a => a == 0xABC).Count,
            Is.EqualTo(differentOverload || differentAssembly ? 2 : 1));
    }

    private static R.Assembly Load(ModuleDefinition module)
    {
        var assembly = new AssemblyDefinition("ExceptionRegions" + Guid.NewGuid().ToString("N"), new Version(1, 0));
        assembly.Modules.Add(module);
        using var stream = new System.IO.MemoryStream();
        module.Write(stream);
        return R.Assembly.Load(stream.ToArray());
    }

}
