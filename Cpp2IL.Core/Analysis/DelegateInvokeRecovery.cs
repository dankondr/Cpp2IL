using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

//Recovers IndirectCall (call reg) for delegate invoke back to actual calls on Invoke
public static class DelegateInvokeRecovery
{
    public static void Run(MethodAnalysisContext method)
    {
        var instructions = method.ControlFlowGraph!.Blocks.SelectMany(block => block.Instructions).ToList();

        // Il2CppObject is two pointers (klass, monitor), then method_ptr, then invoke_impl.
        var invokeImplOffset = (method.AppContext.Binary.is32Bit ? 4 : 8) * 3;

        foreach (var instruction in instructions)
        {
            if (instruction.OpCode is not (OpCode.IndirectCall or OpCode.IndirectJump))
                continue;

            if (GetDelegate(instruction, instructions, invokeImplOffset) is not { } delegateLocal
                || delegateLocal.Type is not { IsDelegate: true } delegateType)
                continue;

            if (delegateType.Methods.FirstOrDefault(m => m.Name == "Invoke") is not { } invoke)
                continue;

            // Raw tail-call argument recovery is only proven for parameterless delegates.
            if (instruction.OpCode == OpCode.IndirectJump && invoke.Parameters.Count != 0)
                continue;

            var block = method.ControlFlowGraph.Blocks.Single(block => block.Instructions.Contains(instruction));
            RewriteAsInvoke(method, instruction, block, delegateLocal, invoke);
        }
    }

    // The address being called, whether it is still a separate load or has been inlined
    private static LocalVariable? GetDelegate(Instruction call, List<Instruction> instructions, int invokeImplOffset)
    {
        if (call.Operands.Count == 0)
            return null;

        var target = call.Operands[0];
        if (target is LocalVariable targetLocal)
            target = instructions.FirstOrDefault(i => ReferenceEquals(i.Destination, targetLocal)) is
                { OpCode: OpCode.Move, Operands: [_, var loaded] } ? loaded : target;

        return target switch
        {
            MemoryOperand { Addend: var offset, Index: null, Scale: 0, Base: LocalVariable value }
                when offset == invokeImplOffset => value,
            FieldReference { Field.Name: "invoke_impl", Field.DeclaringType.FullName: "System.Delegate", Local: var value }
                when call.OpCode == OpCode.IndirectJump
                => value,
            _ => null
        };
    }

    private static void RewriteAsInvoke(MethodAnalysisContext method, Instruction call, Block block,
        LocalVariable delegateLocal, MethodAnalysisContext invoke)
    {
        var isTailCall = call.OpCode == OpCode.IndirectJump;
        if (isTailCall && (method.IsVoid != invoke.IsVoid
            || !method.IsVoid && method.ReturnType.FullName != invoke.ReturnType.FullName))
            return;

        if (invoke.AppContext.InstructionSet.CallingConventionResolver is not { } callingConventions
            || !callingConventions.HasRawArgumentLayout(call, invoke.AppContext))
            return;

        if (isTailCall)
        {
            var operands = new List<IOperand> { invoke };
            if (!invoke.IsVoid)
                operands.Add(new LocalVariable("delegateTailCallResult", callingConventions.ReturnRegister(invoke), invoke.ReturnType));
            operands.AddRange(call.Operands.Skip(2));
            call.SetOperands(operands);
            call.OpCode = invoke.IsVoid ? OpCode.CallVoid : OpCode.Call;
            callingConventions.RemapRawArguments(call, invoke);

            // The native receiver register holds invoke_impl_this rather than the managed delegate.
            call.SetOperand(invoke.IsVoid ? 1 : 2, delegateLocal);

            block.AddInstruction(new Instruction(-1, OpCode.Return,
                invoke.IsVoid ? [] : [call.Operands[1]]));
            block.CalculateBlockType();
        }
        else
        {
            if (invoke.IsVoid)
                call.RemoveOperandAt(1);
            call.SetOperand(0, invoke);
            call.OpCode = invoke.IsVoid ? OpCode.CallVoid : OpCode.Call;
            call.SetOperand(invoke.IsVoid ? 1 : 2, delegateLocal);
            callingConventions.RemapRawArguments(call, invoke);
        }
    }
}
