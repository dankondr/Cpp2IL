using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

public abstract class BaseCallingConventionResolver
{
    // One register a value spans besides the first: a float aggregate's further
    // lanes, or a 9-16 byte composite's high half. ByteOffset/AccessSize locate the
    // lane inside the value for field projection.
    public readonly record struct AggregateLane(Register Register, int ByteOffset, int AccessSize);

    public static bool IsFloatingPoint(TypeAnalysisContext type)
        => type == type.AppContext.SystemTypes.SystemSingleType || type == type.AppContext.SystemTypes.SystemDoubleType;

    // The extra registers carrying lanes 1..n-1 when `type` passes in `firstLane`
    // (register naming differs per ISA; the caller knows which register the value's
    // lane 0 sits in). Empty for values that fit one register.
    public virtual IReadOnlyList<AggregateLane> ExtraLanes(TypeAnalysisContext type, Register firstLane)
        => [];

    protected static bool IsFloatingPoint(ParameterAnalysisContext par) => IsFloatingPoint(par.ParameterType);

    public abstract Register ReturnRegister(MethodAnalysisContext ctx);

    public abstract bool ReturnsViaHiddenBuffer(MethodAnalysisContext ctx);

    public abstract Register? HiddenReturnBufferRegister(MethodAnalysisContext ctx);

    public abstract IOperand[] ResolveForManaged(MethodAnalysisContext ctx);

    protected abstract (string[] Integer, string[] Float) RawRegisters(ApplicationAnalysisContext app);

    // MSVC style: argument slot n is integer register n or float register n, not both
    protected virtual bool UsesShadowedArgumentSlots(ApplicationAnalysisContext app) => false;

    // false when the return buffer pointer lives outside the argument registers (e.g. arm64 uses x8)
    protected virtual bool HiddenBufferConsumesArgumentSlot => true;

    public IOperand[] ResolveForUnmanaged(ApplicationAnalysisContext app, ulong target)
    {
        // We don't know the callee's signature, so preserve every argument register.

        var (integerRegisters, floatRegisters) = RawRegisters(app);
        return integerRegisters.Concat(floatRegisters).Select(name => (IOperand)new Register(null, name)).ToArray();
    }

    public bool HasRawArgumentLayout(Instruction call, ApplicationAnalysisContext app)
    {
        var (integerRegisters, floatRegisters) = RawRegisters(app);
        var argBase = ArgBase(call);

        if (call.Operands.Count != argBase + integerRegisters.Length + floatRegisters.Length)
            return false;

        // An operand's position in the list IS its register slot, so folded values without a
        // register identity (AddressOf, MemoryOperand, methodof operands, ...) are accepted.
        // Register-bearing operands still have to sit in their own register's slot.
        bool InSlot(IOperand operand, string register) => operand switch
        {
            Register or LocalVariable => RegisterName(operand) == register,
            _ => true,
        };

        for (var i = 0; i < integerRegisters.Length; i++)
            if (!InSlot(call.Operands[argBase + i], integerRegisters[i]))
                return false;

        for (var i = 0; i < floatRegisters.Length; i++)
            if (!InSlot(call.Operands[argBase + integerRegisters.Length + i], floatRegisters[i]))
                return false;

        return true;
    }

    // TODO Fix handling of params on the stack here
    public void RemapRawArguments(Instruction call, MethodAnalysisContext resolved)
    {
        var app = resolved.AppContext;

        AttachResultLanes(call, resolved);

        if (!HasRawArgumentLayout(call, app))
            return;

        var (integerRegisters, floatRegisters) = RawRegisters(app);
        var argBase = ArgBase(call);

        var slots = new List<(bool IsFloat, bool Emit)>();
        if (ReturnsViaHiddenBuffer(resolved) && HiddenBufferConsumesArgumentSlot)
            slots.Add((false, false));
        if (!resolved.IsStatic)
            slots.Add((false, true));
        foreach (var parameter in resolved.Parameters)
            slots.Add((IsFloatingPoint(parameter), true));
        slots.Add((false, true)); // the MethodInfo argument

        var operands = new List<IOperand>(argBase + slots.Count);
        for (var i = 0; i < argBase; i++)
            operands.Add(call.Operands[i]);

        if (UsesShadowedArgumentSlots(app))
        {
            for (var slot = 0; slot < slots.Count && slot < integerRegisters.Length; slot++)
                if (slots[slot].Emit)
                    operands.Add(call.Operands[argBase + (slots[slot].IsFloat ? integerRegisters.Length + slot : slot)]);
        }
        else
        {
            // independent integer/float counters
            var (integer, floating) = (0, 0);

            foreach (var (isFloat, emit) in slots)
            {
                if (isFloat ? floating >= floatRegisters.Length : integer >= integerRegisters.Length)
                    break;

                var operand = call.Operands[argBase + (isFloat ? integerRegisters.Length + floating++ : integer++)];
                if (emit)
                    operands.Add(operand);
            }
        }

        call.SetOperands(operands);
    }

    // Once the callee is known, the registers a multi-register result occupies are
    // provable. They arrive too late for SSA renaming, so they are attached as
    // unversioned implicit definitions; AggregateResultLanes resolves them with
    // dominator information instead.
    public void AttachResultLanes(Instruction call, MethodAnalysisContext resolved)
    {
        if (call.OpCode != OpCode.Call || resolved.IsVoid || ReturnsViaHiddenBuffer(resolved))
            return;

        var firstLane = ReturnRegister(resolved);
        foreach (var lane in ExtraLanes(resolved.ReturnType, firstLane))
            if (!call.ImplicitDefinitions.Contains(lane.Register))
                call.ImplicitDefinitions.Add(lane.Register);
    }

    // The mirror of AttachResultLanes: a method whose own return type spans
    // several registers reads each lane as a separate operand of the Return, so
    // SSA and local binding treat them like any other use. AggregateResultLanes
    // rebuilds the aggregate from them; a Return whose lanes cannot be proven
    // keeps its extra operands for the default-fill note.
    public void AttachReturnLanes(Instruction instruction, MethodAnalysisContext context)
    {
        if (instruction.OpCode != OpCode.Return || context.IsVoid || ReturnsViaHiddenBuffer(context))
            return;

        var firstLane = ReturnRegister(context);
        foreach (var lane in ExtraLanes(context.ReturnType, firstLane))
            instruction.AddOperands([lane.Register]);
    }

    protected static int ArgBase(Instruction call) => call.OpCode is OpCode.CallVoid ? 1 : 2;

    private static string? RegisterName(IOperand operand) => operand switch
    {
        Register register => register.Name,
        LocalVariable { Register.Name: var name } => name,
        _ => null
    };
}
