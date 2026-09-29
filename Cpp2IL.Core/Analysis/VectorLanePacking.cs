using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// The ARM64 ABI passes a homogeneous-float aggregate one lane per argument
/// register: a UnityEngine.Vector3 argument occupies v0.s0, v1.s0 and v2.s0, and
/// the compiler materializes it with three scalar writes (`fmov s0,s8`,
/// `fmov s1,s9`, `fmov s2,s10`) immediately before the `bl`. The calling
/// convention model nevertheless exposes a single `V0` operand for the whole
/// parameter, so the sibling `Move(V1, …)`/`Move(V2, …)` definitions look dead
/// and are removed, leaving only a scalar to satisfy a vector slot.
///
/// This pass runs while those sibling definitions are still present (before
/// dead-code elimination). For every operand zipped to a float-aggregate slot
/// it recovers each lane's producing definition - in the same block or walking
/// the dominator chain, never across a call that clobbers the lane's volatile
/// register (v0-v7, v16-v31) - and rewrites the operand as a vector built from
/// the proven lanes: a `Vector128Literal` when every lane is a constant, else a
/// synthetic local whose lane fields are stored individually. Lanes that cannot
/// be proven leave the operand untouched so the slot keeps its diagnosed note.
///
/// Separately, any `Move` source that is a register whose reaching definition
/// is `Move(Vn, 0)` or a `Vector128Literal` carries a proven constant vector
/// (every producing form of `Move(Vn, 0)` zeroes the whole register), and is
/// rewritten to the literal directly so aggregate destinations see
/// `new T(0f, …)` instead of a scalar.
/// </summary>
internal static class VectorLanePacking
{
    private static readonly HashSet<OpCode> FloatMathOps =
    [
        OpCode.Add, OpCode.Subtract, OpCode.Multiply, OpCode.Divide,
        OpCode.Negate, OpCode.VectorMin, OpCode.VectorMax,
    ];

    public static void Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph is not { } graph || method.DominatorInfo is null)
            return;

        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in graph.Instructions)
            if (instruction.Destination is LocalVariable destination)
                definitions[destination] = instruction;

        var inserts = new List<(Block Block, Instruction Before, List<Instruction> Stores)>();
        foreach (var block in graph.Blocks)
        {
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                var instruction = block.Instructions[i];
                switch (instruction.OpCode)
                {
                    case OpCode.Call or OpCode.CallVoid:
                        PackCallOperands(method, block, i, definitions, inserts);
                        break;
                    case OpCode.Return:
                        PackReturnOperand(method, block, i, definitions, inserts);
                        break;
                    case OpCode.Move:
                        RewriteZeroVectorSource(block, i, definitions);
                        break;
                }
            }
        }

        foreach (var (block, before, stores) in inserts)
        {
            var index = block.Instructions.IndexOf(before);
            if (index >= 0)
                block.Instructions.InsertRange(index, stores);
        }
    }

    private static void PackCallOperands(MethodAnalysisContext method, Block block, int index,
        Dictionary<LocalVariable, Instruction> definitions,
        List<(Block, Instruction, List<Instruction>)> inserts)
    {
        var call = block.Instructions[index];
        var callee = ResolveCallee(method.AppContext, call.Operands[0]);
        if (callee == null)
            return;

        var argStart = call.OpCode == OpCode.Call ? 2 : 1;
        var parameterBase = argStart + (callee.IsStatic ? 0 : 1);
        for (var j = argStart; j < call.Operands.Count; j++)
        {
            var parameterIndex = j - parameterBase;
            if (parameterIndex < 0 || parameterIndex >= callee.Parameters.Count)
                continue;
            if (call.Operands[j] is not LocalVariable { Register.Name: { } name }
                || !TryRegisterNumber(name, out var register))
                continue;
            var lanes = VectorLanes(callee.Parameters[parameterIndex].ParameterType);
            if (lanes == null || register + lanes.Length > 8)
                continue;
            if (TryBuildPack(method, block, index, register, lanes,
                    callee.Parameters[parameterIndex].ParameterType, definitions,
                    out var packed, out var stores))
            {
                call.SetOperand(j, packed!);
                if (stores.Count > 0)
                    inserts.Add((block, call, stores));
            }
        }
    }

    private static void PackReturnOperand(MethodAnalysisContext method, Block block, int index,
        Dictionary<LocalVariable, Instruction> definitions,
        List<(Block, Instruction, List<Instruction>)> inserts)
    {
        var ret = block.Instructions[index];
        if (ret.Operands is not [LocalVariable { Register.Name: { } name }]
            || !TryRegisterNumber(name, out var register))
            return;

        var lanes = VectorLanes(method.ReturnType);
        if (lanes == null || register + lanes.Length > 8)
            return;

        if (TryBuildPack(method, block, index, register, lanes, method.ReturnType, definitions,
                out var packed, out var stores))
        {
            ret.SetOperand(0, packed!);
            if (stores.Count > 0)
                inserts.Add((block, ret, stores));
        }
    }

    private static void RewriteZeroVectorSource(Block block, int index,
        Dictionary<LocalVariable, Instruction> definitions)
    {
        var move = block.Instructions[index];
        if (move.Operands is not [_, LocalVariable source]
            || !definitions.TryGetValue(source, out var proven)
            || proven.Operands is not [_, var producing])
            return;

        switch (proven.OpCode)
        {
            case OpCode.Move when producing is Immediate { Value: 0 }:
                move.SetOperand(1, new Vector128Literal(0f, 0f, 0f, 0f));
                break;
            case OpCode.Move when producing is Vector128Literal literal:
                move.SetOperand(1, literal);
                break;
        }
    }

    private static bool TryBuildPack(MethodAnalysisContext method, Block block, int index,
        int firstRegister, FieldAnalysisContext[] lanes, TypeAnalysisContext vectorType,
        Dictionary<LocalVariable, Instruction> definitions,
        out IOperand? operand, out List<Instruction> stores)
    {
        operand = null;
        stores = [];

        var laneOperands = new IOperand?[lanes.Length];
        for (var lane = 0; lane < lanes.Length; lane++)
        {
            if (!TryLaneOperand(method, block, index, "V" + (firstRegister + lane), definitions,
                    out var laneOperand))
                return false;
            laneOperands[lane] = laneOperand;
        }

        var constants = new float[4];
        if (laneOperands.All(lane => TryConstantLane(lane, out _)))
        {
            for (var lane = 0; lane < lanes.Length; lane++)
                TryConstantLane(laneOperands[lane], out constants[lane]);
            operand = new Vector128Literal(constants[0], constants[1], constants[2], constants[3]);
            return true;
        }

        var pack = new LocalVariable($"vectorPack{method.Locals.Count}",
            new Register(null, $"VEC_PACK_{method.Locals.Count}"), vectorType);
        method.Locals.Add(pack);

        for (var lane = 0; lane < lanes.Length; lane++)
            stores.Add(new Instruction(-1, OpCode.Move,
                new FieldReference(lanes[lane], pack, lanes[lane].Offset), laneOperands[lane]!));

        operand = pack;
        return true;
    }

    /// <summary>
    /// The operand for lane `i` of a register-spread aggregate is whatever the
    /// lane register `V(first+i)` last evaluated to: the source of a `Move`
    /// into it, or the defined local itself when a real computation wrote it.
    /// Returns false when the lane cannot be proven honest - the operand then
    /// keeps its diagnosed coercion downstream.
    /// </summary>
    private static bool TryLaneOperand(MethodAnalysisContext method, Block block, int index,
        string registerName, Dictionary<LocalVariable, Instruction> definitions,
        out IOperand? operand)
    {
        operand = null;

        var definition = FindLiveDefinition(method, block, index, registerName, out var definedLocal);
        if (definition == null)
        {
            // An entry value still lives in an argument register only when it is
            // the method's own scalar parameter bound there.
            var local = method.Locals.FirstOrDefault(l =>
                l.Register.Name == registerName && l.Register.Version == -1
                && method.ParameterLocals.Contains(l));
            if (local == null || !IsFloatScalar(ParameterTypeForRegister(method, registerName)))
                return false;
            operand = local;
            return true;
        }

        if (definition.OpCode == OpCode.Move && definition.Operands.Count == 2)
        {
            if (!FloatLaneOperand(method, definitions, definition.Operands[1], 0))
                return false;
            operand = definition.Operands[1];
            return true;
        }

        if (definition.OpCode is OpCode.Call or OpCode.IndirectCall)
        {
            if (definedLocal == null
                || ResolveCallee(method.AppContext, definition.Operands[0]) is not { } callee
                || !IsFloatScalar(callee.ReturnType))
                return false;
            operand = definedLocal;
            return true;
        }

        if (FloatMathOps.Contains(definition.OpCode) && definedLocal != null)
        {
            operand = definedLocal;
            return true;
        }

        return false;
    }

    private static bool FloatLaneOperand(MethodAnalysisContext method,
        Dictionary<LocalVariable, Instruction> definitions, IOperand operand, int depth)
    {
        if (depth > 4)
            return false;

        switch (operand)
        {
            case Immediate immediate:
                // A non-zero scalar immediate is a bit pattern, not a value:
                // `movi d1,#bits` writes lane bits `ldc.r4` would misread, and a
                // broadcast `movi v1.8h` writes a different pattern. Only zero
                // is unambiguous - every producer clears the whole register.
                return immediate.Value == 0;
            case FloatLiteral or DoubleLiteral or Vector128Literal:
                return true;
            case FieldReference field:
                return field.Field.FieldType.FullName == "System.Single";
            case MemoryOperand:
                // A scalar load lane (`ldr s0, [x]`) is honest whether or not
                // emission can name the referent - when it cannot, the lane
                // store itself carries the diagnostic.
                return true;
            case LocalVariable local:
            {
                // A `W`/`X` (or other non-V) register source reached the lane
                // through `fmov s?, w?` - a bit reinterpretation, not a float.
                if (local.Register.Name is not { } localName || localName[0] != 'V')
                    return false;
                if (local.Register.Version == -1 && method.ParameterLocals.Contains(local))
                    return IsFloatScalar(local.Type)
                        || IsFloatScalar(ParameterTypeForRegister(method, localName));
                if (!definitions.TryGetValue(local, out var definition))
                    return false;
                if (definition.OpCode == OpCode.Move && definition.Operands.Count == 2)
                    return FloatLaneOperand(method, definitions, definition.Operands[1], depth + 1);
                if (definition.OpCode is OpCode.Call or OpCode.IndirectCall)
                    return ResolveCallee(method.AppContext, definition.Operands[0]) is { } callee
                        && IsFloatScalar(callee.ReturnType);
                // A bare `Vn` destination is a scalar floating-point op
                // (`fadd s0`, `fmul s1`): integer adds write `Xn`/lane-view
                // (`Vn.Sk`) destinations, never a whole-register view.
                return FloatMathOps.Contains(definition.OpCode)
                    && definition.Destination is LocalVariable { Register.Name: { } destName }
                    && TryRegisterNumber(destName, out _);
            }
            default:
                return false;
        }
    }

    private static bool TryConstantLane(IOperand? operand)
        => TryConstantLane(operand, out _);

    private static bool TryConstantLane(IOperand? operand, out float value)
    {
        switch (operand)
        {
            case Immediate { Value: 0 }:
            case FloatLiteral { Value: 0 }:
            case DoubleLiteral { Value: 0 }:
                value = 0;
                return true;
            case FloatLiteral single:
                value = single.Value;
                return true;
            case DoubleLiteral { Value: >= float.MinValue and <= float.MaxValue } doubleLiteral:
                value = (float)doubleLiteral.Value;
                return true;
            case Vector128Literal literal when literal.X == literal.Y
                && literal.Y == literal.Z && literal.Z == literal.W:
                value = literal.X;
                return true;
            default:
                value = 0;
                return false;
        }
    }

    /// <summary>
    /// The definition of `registerName` live at `block.Instructions[index]`:
    /// the last definition in the same block, else the last definition in the
    /// nearest dominator containing one. Any call between that definition and
    /// the use clobbers volatile argument registers (v0-v7, v16-v31), making
    /// the lane unproven; v8-v15 keep their low lanes across calls.
    /// </summary>
    private static Instruction? FindLiveDefinition(MethodAnalysisContext method, Block block,
        int beforeIndex, string registerName, out LocalVariable? definedLocal)
    {
        definedLocal = null;
        var volatileRegister = IsVolatileRegister(registerName);

        for (var i = beforeIndex - 1; i >= 0; i--)
        {
            var candidate = block.Instructions[i];
            if (candidate.Destination is LocalVariable { Register.Name: { } defined }
                && defined == registerName)
            {
                definedLocal = (LocalVariable)candidate.Destination;
                return candidate;
            }
            if (volatileRegister && IsCall(candidate))
                return null;
        }

        var current = block;
        var dominators = method.DominatorInfo!.ImmediateDominators;
        var hops = 0;
        while (dominators.TryGetValue(current, out var dominator) && dominator != null
            && hops++ < 64)
        {
            current = dominator;
            for (var i = current.Instructions.Count - 1; i >= 0; i--)
            {
                var candidate = current.Instructions[i];
                if (candidate.Destination is LocalVariable { Register.Name: { } defined }
                    && defined == registerName)
                {
                    definedLocal = (LocalVariable)candidate.Destination;
                    return candidate;
                }
                if (volatileRegister && IsCall(candidate))
                    return null;
            }
        }

        return null;
    }

    /// <summary>
    /// A type that is a flat vector of `System.Single` instance fields laid out
    /// at consecutive 4-byte offsets - the managed shape the ABI spreads across
    /// one floating-point argument register per lane. Returns the lane fields
    /// ordered by offset, or null.
    /// </summary>
    private static FieldAnalysisContext[]? VectorLanes(TypeAnalysisContext type)
    {
        if (!type.IsValueType)
            return null;

        var lanes = type.Fields
            .Where(field => !field.IsStatic)
            .OrderBy(field => field.Offset)
            .ToArray();
        if (lanes.Length is < 2 or > 4
            || lanes.Any(field => field.FieldType.FullName != "System.Single")
            || lanes.Where((field, i) => field.Offset != 4 * i).Any())
            return null;

        return lanes;
    }

    private static TypeAnalysisContext? ParameterTypeForRegister(MethodAnalysisContext method,
        string registerName)
    {
        var offset = method.IsStatic ? 0 : 1;
        for (var i = offset;
             i < method.ParameterOperands.Count && i - offset < method.Parameters.Count; i++)
            if (method.ParameterOperands[i] is Register { Name: { } name } && name == registerName)
                return method.Parameters[i - offset].ParameterType;
        return null;
    }

    private static MethodAnalysisContext? ResolveCallee(ApplicationAnalysisContext app,
        IOperand target)
    {
        switch (target)
        {
            case MethodAnalysisContext context:
                return context;
            case Immediate immediate:
            {
                if (!app.MethodsByAddress.TryGetValue(immediate.UnsignedValue, out var candidates)
                    || candidates.Count == 0)
                    return null;
                // Folded methods share one address; mirror the lifter's rule and
                // pick the signature with the most arguments.
                var resolved = candidates[0];
                var mostArguments = -1;
                foreach (var method in candidates)
                {
                    var arguments = method.Parameters.Count + (method.IsStatic ? 0 : 1);
                    if (arguments > mostArguments)
                    {
                        mostArguments = arguments;
                        resolved = method;
                    }
                }
                return resolved;
            }
            default:
                return null;
        }
    }

    private static bool IsCall(Instruction instruction)
        => instruction.OpCode is OpCode.Call or OpCode.CallVoid or OpCode.IndirectCall;

    private static bool IsFloatScalar(TypeAnalysisContext? type)
        => type?.FullName is "System.Single" or "System.Double";

    private static bool TryRegisterNumber(string name, out int register)
    {
        register = 0;
        if (name.Length < 2 || name[0] != 'V')
            return false;
        var i = 1;
        while (i < name.Length && char.IsDigit(name[i]))
            i++;
        if (i != name.Length)
            return false;
        return int.TryParse(name[1..], out register) && register < 32;
    }

    private static bool IsVolatileRegister(string registerName)
        => TryRegisterNumber(registerName, out var register)
            && (register < 8 || register >= 16);
}
