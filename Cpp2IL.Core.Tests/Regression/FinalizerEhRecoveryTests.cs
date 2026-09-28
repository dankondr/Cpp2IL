using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: finalizer try/finally (castle-recovery#120). A C# ~T() lowers to
// try { body } finally { base.Finalize(); }; IL2CPP inlines the finally body on the
// normal path before each return and emits a second copy inside the unwind landing
// pad, which no managed edge reaches. An unreachable call to the same base Finalize
// is the native evidence that the cleanup region exists - without it nothing is
// recovered.
public class FinalizerEhRecoveryTests
{
    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    // Derived.Finalize overriding Base.Finalize, both synthetic: no game names, tokens
    // or addresses.
    private static (InjectedMethodAnalysisContext caller, MethodDefinition method,
            InjectedMethodAnalysisContext baseFinalize)
        NewFixture(ApplicationAnalysisContext app)
    {
        var baseType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Base",
            app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var baseFinalize = baseType.InjectMethodContext("Finalize", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Family | R.MethodAttributes.Virtual | R.MethodAttributes.HideBySig, []);
        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Derived",
            baseType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = owner.InjectMethodContext("Finalize", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Family | R.MethodAttributes.Virtual | R.MethodAttributes.HideBySig, []);

        var module = new ModuleDefinition("FinalizerFrame.dll");
        var baseDefinition = new TypeDefinition("Tests", "Base",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(baseDefinition);
        baseType.PutExtraData("AsmResolverType", baseDefinition);
        var baseFinalizeDefinition = new MethodDefinition("Finalize",
            MethodAttributes.Family | MethodAttributes.Virtual | MethodAttributes.HideBySig,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        baseDefinition.Methods.Add(baseFinalizeDefinition);
        baseFinalize.PutExtraData("AsmResolverMethod", baseFinalizeDefinition);

        var ownerDefinition = new TypeDefinition("Tests", "Derived",
            TypeAttributes.Public | TypeAttributes.Class, baseDefinition);
        module.TopLevelTypes.Add(ownerDefinition);
        owner.PutExtraData("AsmResolverType", ownerDefinition);
        var method = new MethodDefinition("Finalize",
            MethodAttributes.Family | MethodAttributes.Virtual | MethodAttributes.HideBySig,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        ownerDefinition.Methods.Add(method);

        return (caller, method, baseFinalize);
    }

    private static void Analyze(InjectedMethodAnalysisContext caller, List<Instruction> isil)
    {
        caller.ConvertedIsil = isil;
        caller.ControlFlowGraph = new ISILControlFlowGraph(isil);
        // StackAnalyzer.Analyze removes the unwind pad as unreachable before SSA.
        caller.ControlFlowGraph.RemoveUnreachableBlocks();
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph);
        caller.AnalysisWarnings = [];

        SsaForm.Build(caller);
        LocalVariables.CreateAll(caller);
        LocalVariables.ResolveTypesAndFields(caller);
        SsaSimplifier.Run(caller);
        SsaForm.Remove(caller);
        CopyCoalescer.Run(caller);
        LocalVariables.ResolveLateGeneratedTypes(caller);
    }

    // MetadataResolver.ResolveAll calls MergeCallBlocks, which folds a fall-through
    // call+return pair into one block; both layouts must recover the same region.
    [TestCase(false)]
    [TestCase(true)]
    public void LandingPadBaseCallRecoversTryFinally(bool mergeReturnIntoCallBlock)
    {
        var app = App;
        var thisRegister = new Register(null, "X0");
        var slot = new Register(null, "slot");
        var record = new Register(null, "X8");
        var (caller, method, baseFinalize) = NewFixture(app);
        caller.ParameterOperands = [thisRegister];

        var isil = new List<Instruction>
        {
            // The frame record the pad reads `this` back through.
            new(0, OpCode.Move, slot, thisRegister),
            new(1, OpCode.Move, record, new AddressOf(slot)),
            // The finally body inlined on the normal path.
            new(2, OpCode.CallVoid, baseFinalize, thisRegister),
            new(3, OpCode.Return),
            // Unwind landing pad: entered only by the unwinder, reloads `this` through the
            // record and runs the same finally body before resuming the unwind.
            new(4, OpCode.Move, thisRegister,
                new MemoryOperand(new Register(null, "record"), null, 8)),
            new(5, OpCode.CallVoid, baseFinalize, thisRegister),
            new(6, OpCode.Return),
        };
        Analyze(caller, isil);
        if (mergeReturnIntoCallBlock)
            caller.ControlFlowGraph!.MergeCallBlocks();

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        var handler = body.ExceptionHandlers.SingleOrDefault();
        Assert.That(handler, Is.Not.Null,
            () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
        Assert.That(handler!.HandlerType, Is.EqualTo(CilExceptionHandlerType.Finally));

        var instructions = body.Instructions;
        var handlerStart = instructions.IndexOf(((CilInstructionLabel)handler.HandlerStart!).Instruction!);
        var handlerEnd = instructions.IndexOf(((CilInstructionLabel)handler.HandlerEnd!).Instruction!);
        var emitted = instructions.Skip(handlerStart).Take(handlerEnd - handlerStart).ToList();

        Assert.That(emitted.Select(i => i.OpCode.Code),
            Is.EqualTo(new[] { CilCode.Ldarg_0, CilCode.Call, CilCode.Endfinally }));
        Assert.That(emitted[1].Operand is IMethodDescriptor callee && callee.Name?.ToString() == "Finalize",
            "the finally handler must hold the base.Finalize call");

        // The inlined copy on the normal path becomes a leave out of the try; no direct
        // base call may survive there.
        var tryStart = instructions.IndexOf(((CilInstructionLabel)handler.TryStart!).Instruction!);
        var tryEnd = instructions.IndexOf(((CilInstructionLabel)handler.TryEnd!).Instruction!);
        Assert.That(tryEnd, Is.EqualTo(handlerStart));
        var tryBody = instructions.Skip(tryStart).Take(tryEnd - tryStart).ToList();
        Assert.That(tryBody.Any(i => i.OpCode.Code is CilCode.Leave or CilCode.Leave_S));
        Assert.That(tryBody.All(i => i.OpCode.Code is not (CilCode.Call or CilCode.Callvirt)
            || i.Operand is not IMethodDescriptor d || d.Name?.ToString() != "Finalize"),
            "no base.Finalize call may remain inside the try region");
        Assert.That(instructions.Last().OpCode.Code, Is.EqualTo(CilCode.Ret));
    }

    [Test]
    public void NoLandingPadLeavesFlatBodyAndDiagnoses()
    {
        var app = App;
        var thisRegister = new Register(null, "X0");
        var slot = new Register(null, "slot");
        var (caller, method, baseFinalize) = NewFixture(app);
        caller.ParameterOperands = [thisRegister];

        // Same normal path, no unwind pad: the region has no native evidence, so the
        // body stays flat and keeps an explicit diagnostic instead.
        var isil = new List<Instruction>
        {
            new(0, OpCode.Move, slot, thisRegister),
            new(1, OpCode.CallVoid, baseFinalize, thisRegister),
            new(2, OpCode.Return),
        };
        Analyze(caller, isil);

        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        Assert.That(body.ExceptionHandlers, Is.Empty);
        Assert.That(caller.AnalysisWarnings.Any(w => w.Contains("landing pad")));
        Assert.That(body.Instructions.Any(i => i.OpCode.Code is CilCode.Call or CilCode.Callvirt
            && i.Operand is IMethodDescriptor callee && callee.Name?.ToString() == "Finalize"),
            "without pad evidence the base call is emitted as-is, not synthesized into a region");
    }
}
