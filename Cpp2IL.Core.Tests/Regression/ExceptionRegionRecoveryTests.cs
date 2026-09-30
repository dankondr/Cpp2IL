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
    [TestCase(8, true, false, false)]
    [TestCase(16, false, false, false)]
    [TestCase(8, true, true, true)]
    [TestCase(8, false, false, true)]
    public void CallInvalidationRespectsTheWidthOfAnAdjacentSavedFramePointer(int width, bool proven, bool boxesValue, bool earlierArgument)
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
        caller.ConvertedIsil = [store,
            At(0x1004, OpCode.CallVoid, boxesValue ? new StringLiteral("il2cpp_value_box") : work,
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
        Assert.That(new NativeExceptionRegionProof(caller).Find().Count, Is.EqualTo(proven ? 1 : 0));
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

    [TestCase(true, false, false, false)]
    [TestCase(false, false, false, false)]
    [TestCase(true, true, false, false)]
    [TestCase(false, true, false, false)]
    [TestCase(true, true, true, false)]
    [TestCase(true, true, true, true)]
    [TestCase(true, true, false, false, true)]
    public void RecognizedTypeTestProducesCatchAndLeavesToNormalMerge(bool recognizedTypeTest, bool classTest, bool multipleCalls, bool returningHandler, bool normalTail = false)
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
        caller.Locals = [];
        IlGenerator.GenerateIl(caller, definition, proofs);
        Assert.That(definition.CilMethodBody.ExceptionHandlers.Count, Is.EqualTo(1));
        Assert.That(definition.CilMethodBody.Instructions.Any(i => i.Operand is string text
            && text.Contains("Undefined local caughtException")), Is.False);
        var runtimeType = Load(module).GetType("Tests.CatchOwner")!;
        Assert.DoesNotThrow(() => runtimeType.GetMethod("M")!.Invoke(null, null));
        Assert.That(runtimeType.GetField("Captured")!.GetValue(null)!.GetType().FullName, Is.EqualTo("Tests.SpecificException"));
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
    public void ReturningCleanupClosureMustContinueToOriginalUnwind(bool differentArgument, bool extraStore,
        bool returnsInsteadOfUnwinding, bool expected)
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
            At(0x2004, OpCode.Move, x0, new AddressOf(receiver)),
            At(0x2008, OpCode.CallVoid, new Immediate(0x3000), x0),
            returnsInsteadOfUnwinding ? At(0x200C, OpCode.Return)
                : At(0x200C, OpCode.CallVoid, new StringLiteral("_Unwind_Resume"), exception)];
        var closure = new List<Instruction> {
            At(0x3000, OpCode.ShiftStack, new Immediate(-16)),
            At(0x3004, OpCode.Move, new StackOffset(0), exception),
            At(0x3008, OpCode.Move, x0, differentArgument ? new Immediate(43) : new MemoryOperand(x0)),
            At(0x300C, OpCode.CallVoid, cleanup, x0),
            At(0x3010, OpCode.Move, exception, new StackOffset(0)),
            At(0x3014, OpCode.ShiftStack, new Immediate(16)), At(0x3018, OpCode.Return) };
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
    public void SharedCatchGroupsCompareTheFullCalleeSignature(bool differentOverload)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Overloads",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var attributes = R.MethodAttributes.Public | R.MethodAttributes.Static;
        var caller = owner.InjectMethodContext("M", app.SystemTypes.SystemVoidType, attributes, []);
        var work = owner.InjectMethodContext("Work", app.SystemTypes.SystemVoidType, attributes, []);
        var report = owner.InjectMethodContext("Report", app.SystemTypes.SystemVoidType, attributes,
            [app.SystemTypes.SystemExceptionType, app.SystemTypes.SystemInt32Type]);
        var other = differentOverload ? owner.InjectMethodContext("Report", app.SystemTypes.SystemVoidType, attributes,
            [app.SystemTypes.SystemExceptionType, app.SystemTypes.SystemInt64Type]) : report;
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
            Is.EqualTo(differentOverload ? 2 : 1));
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
