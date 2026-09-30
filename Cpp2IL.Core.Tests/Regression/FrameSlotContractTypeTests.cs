using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Utils.AsmResolver;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL.BinaryStructures;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: ISIL→IL emission — frame-slot/spill locals typed by the
// contracts their loads feed. IL2CPP shared generics marshal each T{N}
// argument through the slot as that T{N}, so a resolved callee's parameter
// proves the cell's content. When every use names one caller-emittable type,
// the slot and the untyped spill that stored it adopt it; a source that
// cannot take the type keeps the slot diagnosed instead.
public class FrameSlotContractTypeTests
{
    // A caller whose declaring type owns generic parameter T; the returned
    // callerType injects the callees the test's ISIL calls.
    private static (MethodAnalysisContext caller, MethodDefinition method,
        GenericParameterTypeAnalysisContext typeArgument, InjectedTypeAnalysisContext callerType)
        GenericHost(ApplicationAnalysisContext app, ModuleDefinition module,
            List<LocalVariable> locals)
    {
        var (caller, method) = ForeignCaller(app, module, [], locals);
        var callerType = (InjectedTypeAnalysisContext)caller.DeclaringType!;
        var typeArgument = new GenericParameterTypeAnalysisContext("T", 0,
            Il2CppTypeEnum.IL2CPP_TYPE_VAR, 0, callerType);
        callerType.GenericParameters.Add(typeArgument);
        return (caller, method, typeArgument, callerType);
    }

    private static MethodAnalysisContext InjectTake(InjectedTypeAnalysisContext callerType,
        ModuleDefinition module, MethodDefinition hostMethod,
        GenericParameterTypeAnalysisContext argumentType)
    {
        var take = callerType.InjectMethodContext("Take", argumentType.AppContext.SystemTypes.SystemVoidType,
            System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static,
            argumentType);
        var takeDefinition = new MethodDefinition("Take",
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
                [argumentType.ToTypeSignature()]));
        hostMethod.DeclaringType!.Methods.Add(takeDefinition);
        take.PutExtraData("AsmResolverMethod", takeDefinition);
        return take;
    }

    [Test]
    public void SharedGenericContractTypesSlotAndSpillSource()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("SlotContract.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        var frame = new LocalVariable("frame", new Register(null, "X29_v1"));
        var spill = new LocalVariable("spill", new Register(null, "spill"));
        var proven = new LocalVariable("proven", new Register(null, "proven"));
        var (caller, method, typeArgument, callerType) =
            GenericHost(app, module, [frame, spill, proven]);
        proven.Type = typeArgument;
        var take = InjectTake(callerType, module, method, typeArgument);
        var memory = new MemoryOperand(frame, addend: -0x18, accessSize: 8);
        // spill := a T-typed local, then [x29 - 0x18] := spill, then the slot
        // feeds Take's T parameter. Before contract typing the untyped spill
        // makes the slot Object and the argument throws a conversion
        // diagnostic; afterwards the slot, the store and the call all agree
        // on T.
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(-1, OpCode.Move, proven, new Immediate(0)),
            new(0, OpCode.Move, spill, proven),
            new(1, OpCode.Move, memory, spill),
            new(2, OpCode.CallVoid, take, memory),
            new(3, OpCode.Return)]);

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        Assert.Multiple(() =>
        {
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString().Contains("Take") == true), Is.True,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
        });
    }

    [Test]
    public void StackSlotLoadAdoptsSharedGenericContract()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("StackContract.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        var stack = new LocalVariable("stack", new Register(null, "stack_-180"));
        var (caller, method, typeArgument, callerType) =
            GenericHost(app, module, [stack]);
        var take = InjectTake(callerType, module, method, typeArgument);
        var memory = new MemoryOperand(stack, addend: 0, accessSize: 8);
        // No store ever types a stack_-180 cell: on development the load dies
        // as an unmanaged memory load. The callee's T contract materializes a
        // typed frame_sp_180 local instead.
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.CallVoid, take, memory),
            new(1, OpCode.Return)]);

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        Assert.Multiple(() =>
        {
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldloc), Is.True,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
        });
    }

    [Test]
    public void UnadoptableSourceKeepsConversionDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("SlotVeto.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType);
        var frame = new LocalVariable("frame", new Register(null, "X29_v1"));
        // A store source already proven Object cannot adopt the slot's T
        // contract, so the slot stays untyped and the argument diagnosed.
        var source = new LocalVariable("source", new Register(null, "source"))
            { Type = app.SystemTypes.SystemObjectType };
        var (caller, method, typeArgument, callerType) =
            GenericHost(app, module, [frame, source]);
        var take = InjectTake(callerType, module, method, typeArgument);
        var memory = new MemoryOperand(frame, addend: -0x18, accessSize: 8);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, memory, source),
            new(1, OpCode.CallVoid, take, memory),
            new(2, OpCode.Return)]);

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr
                && i.Operand is string text && text.Contains("operand to T")), Is.True,
            () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
    }
}
