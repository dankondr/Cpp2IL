using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;

namespace Cpp2IL.Core.Analysis;

// Recovers the try/finally that every C# finalizer carries (~T() lowers to
// try { body } finally { base.Finalize(); }) from its native unwind landing pad.
//
// IL2CPP compiles the finally body twice: inlined on the normal path before each
// return, and again inside the cleanup landing pad the unwinder enters - a region no
// managed edge reaches, so the CFG drops it as unreachable. A call to the same base
// Finalize in both places is the native evidence that makes the emitted EH clause a
// recovery rather than an invention; anything else is diagnosed and left alone.
public static class FinalizerEhRecovery
{
    private sealed record FinalizerPlan(
        MethodAnalysisContext BaseFinalize,
        List<Instruction> ExitCalls,
        List<Instruction> ExitReturns);

    // Runs after the flat body is emitted but before the fall-off guard: the proven exit
    // calls become leaves out of the try, the returns behind them leave as well, and the
    // handler + shared ret close the body out.
    public static void Apply(MethodAnalysisContext context, MethodDefinition definition,
        Dictionary<Instruction, List<CilInstruction>> instructionMap)
    {
        var plan = CreatePlan(context);
        if (plan == null)
            return;

        var body = definition.CilMethodBody!;
        var instructions = body.Instructions;

        // Validate every planned rewrite up front so a miss cannot leave a half-mutated body.
        var exitSites = plan.ExitCalls.Concat(plan.ExitReturns)
            .Select(i => instructionMap.TryGetValue(i, out var emitted) ? emitted : null)
            .ToList();
        if (exitSites.Any(e => e == null || e.Count == 0))
        {
            context.AddWarning(
                "Finalizer landing pad was proven, but a base.Finalize epilogue was not emitted; try/finally not recovered");
            return;
        }

        var postLabel = new CilInstructionLabel();
        foreach (var emitted in exitSites)
        {
            emitted![0].OpCode = CilOpCodes.Leave;
            emitted[0].Operand = postLabel;
            // By identity: Remove matches opcode and operand, so it could take an
            // earlier identical instruction instead of this exit's own.
            for (var i = 1; i < emitted.Count; i++)
                if (instructions.ToList().FindIndex(x => ReferenceEquals(x, emitted[i])) is >= 0 and var at)
                    instructions.RemoveAt(at);
        }

        var handlerStart = new CilInstruction(CilOpCodes.Ldarg_0);
        instructions.Add(handlerStart);
        instructions.Add(new CilInstruction(CilOpCodes.Call, plan.BaseFinalize.ToMethodDescriptor()));
        instructions.Add(new CilInstruction(CilOpCodes.Endfinally));
        var returnInstruction = new CilInstruction(CilOpCodes.Ret);
        instructions.Add(returnInstruction);
        postLabel.Instruction = returnInstruction;

        body.ExceptionHandlers.Add(new CilExceptionHandler
        {
            HandlerType = CilExceptionHandlerType.Finally,
            TryStart = new CilInstructionLabel(instructions[0]),
            TryEnd = new CilInstructionLabel(handlerStart),
            HandlerStart = new CilInstructionLabel(handlerStart),
            HandlerEnd = new CilInstructionLabel(returnInstruction),
        });
    }

    private static FinalizerPlan? CreatePlan(MethodAnalysisContext context)
    {
        if (context.Name != "Finalize" || context.Parameters.Count != 0 || context.IsStatic
            || !context.IsVoid || !context.IsVirtual)
            return null;

        var cfg = context.ControlFlowGraph!;
        var live = new HashSet<Instruction>(cfg.Blocks.SelectMany(block => block.Instructions));
        if (live.Count == 0)
            return null;

        var baseFinalize = FindBaseFinalize(context, live);
        if (baseFinalize == null)
            return null;

        var exitCalls = new List<Instruction>();
        var misplaced = false;
        foreach (var instruction in live)
        {
            if (!instruction.IsCall || instruction.Operands.Count == 0
                || !CalleeIs(context, instruction, baseFinalize))
                continue;
            if (IsEpilogueCall(cfg, instruction))
                exitCalls.Add(instruction);
            else
                misplaced = true;
        }

        if (exitCalls.Count == 0 && !misplaced)
            return null;

        if (misplaced)
        {
            context.AddWarning(
                "Finalizer calls base.Finalize outside the epilogue; try/finally not recovered");
            return null;
        }

        // The landing pad is lifted but unreachable: nothing managed jumps into it, so a second
        // call to the identical base Finalize there is the duplicated finally body. With no pad
        // there is no region evidence and emitting one would be a guess. When the unwind tables
        // were read, the pad's code sits in the method's landing-pad regions instead of the
        // unreachable tail of the stream.
        bool IsBaseCall(Instruction i) => i.IsCall && i.Operands.Count > 0 && CalleeIs(context, i, baseFinalize);
        var padCallsBase =
            (context.ConvertedIsil != null && context.ConvertedIsil.Any(i => !live.Contains(i) && IsBaseCall(i)))
            || context.LandingPadRegions.Any(region => region.Instructions.Any(IsBaseCall));
        if (!padCallsBase)
        {
            context.AddWarning(
                "Finalizer calls base.Finalize but no unreachable landing pad calls it; try/finally not recovered");
            return null;
        }

        // A finally runs on every normal exit, so every return must sit behind an inlined copy.
        var exitReturns = new List<Instruction>();
        var callBlocks = exitCalls
            .Select(i => cfg.FindBlockByInstruction(i))
            .OfType<Block>()
            .ToHashSet();
        foreach (var instruction in live)
        {
            if (instruction.OpCode != OpCode.Return)
                continue;
            exitReturns.Add(instruction);
            var returnBlock = cfg.FindBlockByInstruction(instruction);
            if (returnBlock != null && ReachableAvoiding(cfg.EntryBlock, returnBlock, callBlocks))
            {
                context.AddWarning(
                    "Finalizer has a return path no inlined base.Finalize precedes; try/finally not recovered");
                return null;
            }
        }

        return new FinalizerPlan(baseFinalize, exitCalls, exitReturns);
    }

    // The overridden Finalize up the declaring type's base chain - vtable first, then the
    // resolved call targets (contexts without metadata never populate the vtable).
    private static MethodAnalysisContext? FindBaseFinalize(MethodAnalysisContext context,
        HashSet<Instruction> live)
    {
        if (context.BaseMethod is { Name: "Finalize" } baseMethod
            && baseMethod.Parameters.Count == 0 && baseMethod.IsVoid
            && IsStrictBase(context.DeclaringType, baseMethod.DeclaringType))
            return baseMethod;

        MethodAnalysisContext? found = null;
        foreach (var instruction in live)
        {
            if (!instruction.IsCall || instruction.Operands.Count == 0)
                continue;
            var callee = ResolveCallee(context, instruction);
            if (callee is not { Name: "Finalize", IsStatic: false } || callee.Parameters.Count != 0
                || !callee.IsVoid || callee == context
                || !IsStrictBase(context.DeclaringType, callee.DeclaringType))
                continue;
            if (found != null && found != callee)
                return null;
            found = callee;
        }
        return found;
    }

    private static bool IsStrictBase(TypeAnalysisContext? type, TypeAnalysisContext? candidateBase)
    {
        for (var current = type?.DefaultBaseType; current != null; current = current.DefaultBaseType)
            if (current == candidateBase)
                return true;
        return false;
    }

    private static MethodAnalysisContext? ResolveCallee(MethodAnalysisContext context, Instruction instruction)
        => instruction.Operands[0] switch
        {
            MethodAnalysisContext callee => callee,
            Immediate immediate => context.AppContext.MethodsByAddress
                .TryGetValue(immediate.UnsignedValue, out var methods) && methods.Count > 0
                    ? methods[0]
                    : null,
            _ => null,
        };

    private static bool CalleeIs(MethodAnalysisContext context, Instruction instruction,
        MethodAnalysisContext target)
        => instruction.Operands[0] switch
        {
            MethodAnalysisContext callee => callee == target
                || (callee.UnderlyingPointer != 0 && callee.UnderlyingPointer == target.UnderlyingPointer),
            Immediate immediate => target.UnderlyingPointer != 0 && immediate.UnsignedValue == target.UnderlyingPointer
                || context.AppContext.MethodsByAddress.TryGetValue(immediate.UnsignedValue, out var methods)
                    && methods.Contains(target),
            _ => false,
        };

    // The epilogue position the finally body is inlined into: nothing with an observable
    // effect follows the call in its block, and successors only unwind through empty
    // blocks to a return or the method exit.
    private static bool IsEpilogueCall(ISILControlFlowGraph cfg, Instruction instruction)
    {
        var block = cfg.FindBlockByInstruction(instruction);
        if (block == null)
            return false;

        var index = block.Instructions.IndexOf(instruction);
        var sawExit = false;
        for (var i = index + 1; i < block.Instructions.Count; i++)
        {
            if (block.Instructions[i].OpCode == OpCode.Return)
                sawExit = true;
            else if (block.Instructions[i].OpCode != OpCode.Nop)
                return false;
        }

        var visited = new HashSet<Block>();
        var pending = new Stack<Block>(block.Successors);
        while (pending.Count > 0)
        {
            var next = pending.Pop();
            if (next == cfg.ExitBlock)
            {
                sawExit = true;
                continue;
            }
            if (!visited.Add(next))
                continue;
            foreach (var nextInstruction in next.Instructions)
            {
                if (nextInstruction.OpCode == OpCode.Return)
                    sawExit = true;
                else if (nextInstruction.OpCode is not (OpCode.Nop or OpCode.Jump))
                    return false;
            }
            foreach (var successor in next.Successors)
                pending.Push(successor);
        }
        return sawExit;
    }

    private static bool ReachableAvoiding(Block entry, Block target, HashSet<Block> stop)
    {
        var visited = new HashSet<Block>();
        var pending = new Stack<Block>();
        pending.Push(entry);
        while (pending.Count > 0)
        {
            var block = pending.Pop();
            // A return sitting in a call block is reached by entering that block, so it is
            // behind the call - check the stop set before testing for the target itself.
            if (stop.Contains(block) || !visited.Add(block))
                continue;
            if (block == target)
                return true;
            foreach (var successor in block.Successors)
                pending.Push(successor);
        }
        return false;
    }
}
