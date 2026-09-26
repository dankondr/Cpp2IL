using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Extensions;
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
        var cfg = method.ControlFlowGraph!;

        var (definitions, homeBlock) = InterfaceDispatchRecovery.BuildMaps(cfg);
        if (InterfaceDispatchRecovery.DistributePhiedConstructions(method, cfg, definitions, homeBlock))
            (definitions, homeBlock) = InterfaceDispatchRecovery.BuildMaps(cfg);

        var instructions = cfg.Blocks.SelectMany(block => block.Instructions).ToList();

        // Il2CppObject is two pointers (klass, monitor), then method_ptr, then invoke_impl.
        var invokeImplOffset = (method.AppContext.Binary.is32Bit ? 4 : 8) * 3;

        var changed = false;

        foreach (var instruction in instructions)
        {
            if (instruction.OpCode is not (OpCode.IndirectCall or OpCode.IndirectJump))
                continue;

            var delegateLocal = GetDelegate(instruction, definitions, invokeImplOffset);
            var delegateType = delegateLocal != null ? DelegateTypeOf(delegateLocal, definitions) : null;
            if (delegateLocal == null || delegateType == null)
                continue;

            // Generic instances carry no Methods of their own - resolve Invoke on the generic
            // definition and re-instantiate it against the delegate's arguments.
            var invoke = delegateType switch
            {
                GenericInstanceTypeAnalysisContext genericInstance
                    => genericInstance.GenericType.Methods.FirstOrDefault(m => m.Name == "Invoke") is { } baseInvoke
                        ? new ConcreteGenericMethodAnalysisContext(baseInvoke, genericInstance.GenericArguments, [])
                        : null,
                _ => delegateType.Methods.FirstOrDefault(m => m.Name == "Invoke"),
            };
            if (invoke == null)
                continue;

            if (!VerifyInvokeOperands(instruction, invoke, delegateLocal, definitions, invokeImplOffset))
                continue;

            var block = method.ControlFlowGraph.Blocks.Single(block => block.Instructions.Contains(instruction));
            RewriteAsInvoke(method, instruction, block, delegateLocal, invoke);
            changed = true;
        }

        if (changed)
            DeadCodeEliminator.Run(method);
    }

    // The address being called, whether it is still a separate load or has been inlined
    private static LocalVariable? GetDelegate(Instruction call, Dictionary<LocalVariable, Instruction> definitions, int invokeImplOffset)
    {
        if (call.Operands.Count == 0)
            return null;

        var target = call.Operands[0];
        if (target is LocalVariable targetLocal)
            target = InterfaceDispatchRecovery.ChaseCopies(definitions, targetLocal) is
                { OpCode: OpCode.Move, Operands: [_, var loaded] } ? loaded : target;

        return target switch
        {
            MemoryOperand { Addend: var offset, Index: null, Scale: 0, Base: LocalVariable value }
                when offset == invokeImplOffset => value,
            FieldReference { Field.Name: "invoke_impl", Field.DeclaringType.FullName: "System.Delegate", Local: var value }
                => value,
            _ => null
        };
    }

    // A delegate's invoke frame is (method_code, params..., method): the receiver register
    // carries a delegate-internal field, each declared parameter gets a real argument - an
    // address for byref/pointer params - and the last argument slot is the delegate's
    // MethodInfo. Arguments are located by register so float/HFA params (which consume
    // V-registers) don't shift the integer-register positions. Anything else stays indirect.
    private static bool VerifyInvokeOperands(Instruction call, MethodAnalysisContext invoke,
        LocalVariable delegateLocal, Dictionary<LocalVariable, Instruction> definitions, int invokeImplOffset)
    {
        var parameters = invoke.Parameters;
        if (call.Operands.Count < 4 + parameters.Count
            || invoke.AppContext.InstructionSet.CallingConventionResolver is not { } resolver)
            return false;

        var arguments = resolver.ResolveForManaged(invoke); // receiver, params..., MethodInfo
        if (arguments.Length != 1 + parameters.Count + 1)
            return false;

        var receiverIndex = RawOperandIndex(call, arguments[0]);
        if (receiverIndex < 0
            || !IsDelegateFieldLoad(call.Operands[receiverIndex], delegateLocal, definitions, invokeImplOffset))
            return false;

        for (var i = 0; i < parameters.Count; i++)
        {
            if (parameters[i].ParameterType is not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext))
                continue;

            var argumentIndex = RawOperandIndex(call, arguments[1 + i]);
            if (argumentIndex < 0)
                return false;

            var argument = call.Operands[argumentIndex];
            var address = argument is AddressOf
                          || argument is LocalVariable local
                              && InterfaceDispatchRecovery.ChaseCopies(definitions, local) is
                                  { OpCode: OpCode.Move, Operands: [_, AddressOf] };
            if (!address)
                return false;
        }

        var methodInfoIndex = RawOperandIndex(call, arguments[^1]);
        return methodInfoIndex >= 0
            && IsDelegateFieldLoad(call.Operands[methodInfoIndex], delegateLocal, definitions, invokeImplOffset);
    }

    // The index, within a raw-register operand list, of the register the managed argument
    // was passed in. -1 when it doesn't land in a register (e.g. spilled to the stack).
    private static int RawOperandIndex(Instruction call, IOperand argument)
    {
        var name = argument switch
        {
            Register { Name: var registerName } => registerName,
            LocalVariable { Register.Name: var registerName } => registerName,
            _ => null,
        };
        if (name == null)
            return -1;

        for (var i = 2; i < call.Operands.Count; i++)
            if (RegisterName(call.Operands[i]) == name)
                return i;
        return -1;
    }

    private static string? RegisterName(IOperand operand) => operand switch
    {
        Register register => register.Name,
        LocalVariable { Register.Name: var name } => name,
        _ => null,
    };

    // The local holding the delegate may itself be a copy, or loaded from a field, while the
    // delegate type only shows on its definition. Generic instances report no base type of their
    // own, so the check has to look through to the generic definition.
    private static TypeAnalysisContext? DelegateTypeOf(LocalVariable local,
        Dictionary<LocalVariable, Instruction> definitions)
    {
        var visited = new HashSet<LocalVariable>();
        var current = local;
        while (visited.Add(current))
        {
            if (IsDelegateType(current.Type))
                return current.Type!;
            if (!definitions.TryGetValue(current, out var definition)
                || definition.OpCode != OpCode.Move)
                return null;
            switch (definition.Operands[1])
            {
                case LocalVariable source:
                    current = source;
                    break;
                case FieldReference { Field.FieldType: { } fieldType }:
                    return IsDelegateType(fieldType) ? fieldType : null;
                default:
                    return null;
            }
        }
        return null;
    }

    private static bool IsDelegateType(TypeAnalysisContext? type) =>
        type is { IsDelegate: true } or GenericInstanceTypeAnalysisContext { GenericType.IsDelegate: true };

    private static bool IsDelegateFieldLoad(IOperand operand, LocalVariable delegateLocal,
        Dictionary<LocalVariable, Instruction> definitions, int invokeImplOffset)
    {
        var loaded = operand is LocalVariable local
                     && InterfaceDispatchRecovery.ChaseCopies(definitions, local) is
                         { OpCode: OpCode.Move, Operands: [_, var source] }
            ? source
            : operand;

        return loaded switch
        {
            FieldReference field => ReferenceEquals(field.Local, delegateLocal),
            MemoryOperand { Index: null, Scale: 0, Base: LocalVariable memoryBase, Addend: var addend }
                => ReferenceEquals(memoryBase, delegateLocal) && addend != invokeImplOffset,
            _ => false,
        };
    }

    private static void RewriteAsInvoke(MethodAnalysisContext method, Instruction call, Block block,
        LocalVariable delegateLocal, MethodAnalysisContext invoke)
    {
        var isTailCall = call.OpCode == OpCode.IndirectJump;
        // A void caller may tail-jump an invoke with a return value - CallVoid lowers to
        // call+pop, the discarded result. A non-void caller needs an assignable return.
        if (isTailCall && !method.IsVoid
            && (invoke.IsVoid || !invoke.ReturnType.IsAssignableTo(method.ReturnType)))
            return;

        if (invoke.AppContext.InstructionSet.CallingConventionResolver is not { } callingConventions
            || !callingConventions.HasRawArgumentLayout(call, invoke.AppContext))
            return;

        if (isTailCall)
        {
            var yieldsResult = !method.IsVoid && !invoke.IsVoid;
            var operands = new List<IOperand> { invoke };
            if (yieldsResult)
                operands.Add(new LocalVariable("delegateTailCallResult", callingConventions.ReturnRegister(invoke), invoke.ReturnType));
            operands.AddRange(call.Operands.Skip(2));
            call.SetOperands(operands);
            call.OpCode = yieldsResult ? OpCode.Call : OpCode.CallVoid;
            callingConventions.RemapRawArguments(call, invoke);

            // The native receiver register holds invoke_impl_this rather than the managed delegate.
            call.SetOperand(yieldsResult ? 2 : 1, delegateLocal);

            block.AddInstruction(new Instruction(-1, OpCode.Return,
                yieldsResult ? [call.Operands[1]] : []));
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
