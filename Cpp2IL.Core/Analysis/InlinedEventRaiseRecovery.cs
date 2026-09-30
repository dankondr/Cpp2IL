using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Un-inlines the <c>E?.Invoke()</c> raise idiom when the compiler inlined a
/// field-like event's raiser into a foreign body. The inlined shape - a null
/// check on the private backing field guarding a direct
/// <c>callvirt DelegateType::Invoke</c> on that field - leaves a direct field
/// reference in the caller, which forces the emitted field to stay widened and
/// the field/event pair to decompile as duplicate definitions (CS0102).
/// When the call is provably an inlined raise - the only entry to the raise
/// block is a null guard on the same field, and the declaring type has exactly
/// one raiser-shaped method that invokes this field - the call is respelled to
/// that raiser, the guard collapses, and the foreign field reference
/// disappears. Anything not proven keeps its field access untouched.
/// </summary>
internal static class InlinedEventRaiseRecovery
{
    private const int MaxCopyDepth = 8;

    public static int Run(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph;
        if (cfg is null)
            return 0;

        var (definitions, _) = InterfaceDispatchRecovery.BuildMaps(cfg);
        var uses = CountLocalUses(cfg);
        var recovered = 0;

        foreach (var block in cfg.Blocks.ToList())
            foreach (var call in block.Instructions)
            {
                if (call.OpCode is not (OpCode.Call or OpCode.CallVoid)
                    || call.Operands.Count == 0
                    || call.Operands[0] is not MethodAnalysisContext invoke
                    || invoke.Name != "Invoke"
                    || invoke.DeclaringType?.IsDelegate != true)
                    continue;

                var receiverIndex = call.OpCode == OpCode.CallVoid ? 1 : 2;
                if (call.Operands.Count <= receiverIndex
                    || ResolveFieldLoad(call.Operands[receiverIndex], definitions) is not { } receiver
                    || receiver.Local is null
                    || !HasEventTwin(receiver.Field)
                    || WithinPrivateScope(method.DeclaringType, receiver.Field.DeclaringType))
                    continue;

                var sources = TrampolineSources(block);
                if (sources.Count != 1
                    || !TryGetNullGuard(sources[0], receiver.Field, definitions, uses, block, out var guard)
                    || !TryFindUniqueRaiser(method, receiver.Field, invoke, out var raiser))
                    continue;

                // Proven inlined raise: the guard's null check is folded into
                // the raiser's own body, so the block enters the raise
                // unconditionally and the call names the raiser.
                var check = guard.CheckBlock;
                check.Instructions.Remove(guard.Definition);
                var jumpIndex = check.Instructions.IndexOf(guard.Jump);
                check.Instructions[jumpIndex] = new Instruction(guard.Jump.Index, OpCode.Jump, block);
                check.Successors.Remove(guard.Skip);
                guard.Skip.Predecessors.Remove(check);
                if (!check.Successors.Contains(block))
                    check.Successors.Add(block);
                if (!block.Predecessors.Contains(check))
                    block.Predecessors.Add(check);
                check.CalculateBlockType();

                call.SetOperand(0, raiser);
                call.SetOperand(receiverIndex, receiver.Local);
                recovered++;
            }

        if (recovered > 0)
        {
            cfg.RemoveUnreachableBlocks();
            DeadCodeEliminator.Run(method);
        }

        return recovered;
    }

    private readonly record struct Guard(Block CheckBlock, Instruction Jump, Instruction Definition, Block Skip);

    // The raise is `if (x.E != null) x.E.Invoke()` - one ConditionalJump source
    // whose flag is a null-check on this field, single-use, where the matching
    // edge reaches the raise block through trampolines and the other does not.
    private static bool TryGetNullGuard(Block check, FieldAnalysisContext field,
        Dictionary<LocalVariable, Instruction> definitions, Dictionary<LocalVariable, int> uses,
        Block raiseBlock, out Guard guard)
    {
        guard = default;
        if (check.Instructions.Count == 0 || check.Instructions[^1].OpCode != OpCode.ConditionalJump)
            return false;
        var jump = check.Instructions[^1];
        if (jump.Operands.Count < 2
            || jump.Operands[0] is not Block target
            || jump.Operands[1] is not LocalVariable flag
            || uses.GetValueOrDefault(flag) != 1
            || !definitions.TryGetValue(flag, out var definition)
            || definition.OpCode is not (OpCode.CheckEqual or OpCode.CheckNotEqual)
            || !check.Instructions.Contains(definition)
            || definition.Operands.Count < 3)
            return false;

        var (a, b) = (definition.Operands[1], definition.Operands[2]);
        IOperand? fieldSide = ResolveFieldLoad(a, definitions)?.Field == field ? a
            : ResolveFieldLoad(b, definitions)?.Field == field ? b
            : null;
        if (fieldSide is null || ResolveImmediate(a == fieldSide ? b : a, definitions) != 0)
            return false;

        var flagTrueIsNull = definition.OpCode == OpCode.CheckEqual;
        var fallthrough = check.Successors.FirstOrDefault(s => !ReferenceEquals(s, target));
        var raiseSuccessor = flagTrueIsNull ? fallthrough : target;
        var skipSuccessor = flagTrueIsNull ? target : fallthrough;
        if (raiseSuccessor is null || skipSuccessor is null)
            return false;
        if (!ReachesOnlyThroughTrampolines(raiseSuccessor, raiseBlock)
            || ReachesOnlyThroughTrampolines(skipSuccessor, raiseBlock))
            return false;

        guard = new(check, jump, definition, skipSuccessor);
        return true;
    }

    // Exactly one method on the field's declaring type that could have been
    // inlined here: signature-compatible with the delegate invoke, callable
    // from the emitting method, and its own body invokes this field.
    private static bool TryFindUniqueRaiser(MethodAnalysisContext caller, FieldAnalysisContext field,
        MethodAnalysisContext invoke, out MethodAnalysisContext raiser)
    {
        raiser = null!;
        var found = 0;
        foreach (var candidate in field.DeclaringType.Methods)
        {
            if (ReferenceEquals(candidate, caller)
                || candidate.IsStatic != field.IsStatic
                || !SignatureMatches(candidate, invoke)
                || !InaccessibleCalleeRecovery.IsVisibleFrom(candidate, caller)
                || !BodyRaisesField(candidate, field))
                continue;
            if (++found > 1)
                return false;
            raiser = candidate;
        }
        return found == 1;
    }

    private static bool SignatureMatches(MethodAnalysisContext candidate, MethodAnalysisContext invoke)
    {
        if (candidate.Parameters.Count != invoke.Parameters.Count
            || candidate.ReturnType?.FullName != invoke.ReturnType?.FullName)
            return false;
        for (var i = 0; i < candidate.Parameters.Count; i++)
            if (candidate.Parameters[i].ParameterType?.FullName != invoke.Parameters[i].ParameterType?.FullName)
                return false;
        return true;
    }

    // The candidate's body invokes this field: a delegate-dispatch instruction
    // whose delegate resolves to a load of the field. Uses whatever ISIL the
    // context already carries, else a fresh conversion - Analyze() is not
    // called here because method fill runs in parallel.
    private static bool BodyRaisesField(MethodAnalysisContext candidate, FieldAnalysisContext field)
    {
        var isil = candidate.ConvertedIsil ?? TryConvertIsil(candidate);
        if (isil is not { Count: > 0 })
            return false;

        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in isil)
            if (instruction.Destination is LocalVariable destination)
                definitions[destination] = instruction;

        var invokeImplOffset = (candidate.AppContext.Binary.is32Bit ? 4 : 8) * 3;
        foreach (var instruction in isil)
            switch (instruction.OpCode)
            {
                case OpCode.Call or OpCode.CallVoid
                    when instruction.Operands.Count > 0
                        && instruction.Operands[0] is MethodAnalysisContext { Name: "Invoke" } invoked
                        && invoked.DeclaringType?.IsDelegate == true:
                {
                    var receiverIndex = instruction.OpCode == OpCode.CallVoid ? 1 : 2;
                    if (instruction.Operands.Count > receiverIndex
                        && ResolveFieldLoad(instruction.Operands[receiverIndex], definitions)?.Field == field)
                        return true;
                    break;
                }
                case OpCode.IndirectCall or OpCode.IndirectJump:
                    if (DelegateLocal(instruction, definitions, invokeImplOffset) is { } delegateLocal
                        && ResolveFieldLoad(delegateLocal, definitions)?.Field == field)
                        return true;
                    break;
            }
        return false;
    }

    private static List<Instruction>? TryConvertIsil(MethodAnalysisContext candidate)
    {
        try
        {
            return candidate.AppContext.InstructionSet.GetIsilFromMethod(candidate);
        }
        catch
        {
            return null;
        }
    }

    // The delegate a call dispatches on: the call target chases through copies
    // to a load of the delegate's invoke_impl slot.
    private static LocalVariable? DelegateLocal(Instruction call,
        Dictionary<LocalVariable, Instruction> definitions, int invokeImplOffset)
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
            FieldReference { Field.Name: "invoke_impl", Local: { } value } => value,
            _ => null
        };
    }

    private static FieldReference? ResolveFieldLoad(IOperand operand, Dictionary<LocalVariable, Instruction> definitions)
    {
        for (var depth = 0; depth < MaxCopyDepth; depth++)
            switch (operand)
            {
                case FieldReference reference:
                    return reference;
                case LocalVariable local
                    when definitions.TryGetValue(local, out var definition)
                        && definition.OpCode == OpCode.Move
                        && definition.Operands.Count >= 2:
                    operand = definition.Operands[1];
                    continue;
                default:
                    return null;
            }
        return null;
    }

    private static long? ResolveImmediate(IOperand operand, Dictionary<LocalVariable, Instruction> definitions)
    {
        for (var depth = 0; depth < MaxCopyDepth; depth++)
            switch (operand)
            {
                case Immediate immediate:
                    return immediate.Value;
                case LocalVariable local
                    when definitions.TryGetValue(local, out var definition)
                        && definition.OpCode == OpCode.Move
                        && definition.Operands.Count >= 2:
                    operand = definition.Operands[1];
                    continue;
                default:
                    return null;
            }
        return null;
    }

    private static bool HasEventTwin(FieldAnalysisContext field)
    {
        if (field.IsStatic || field.DeclaringType is null || field.DeclaringType.IsValueType
            || (field.Attributes & FieldAttributes.FieldAccessMask) != FieldAttributes.Private)
            return false;
        return field.DeclaringType.Events.Any(e => e.Name == field.Name && e.IsStatic == field.IsStatic);
    }

    private static bool WithinPrivateScope(TypeAnalysisContext? accessing, TypeAnalysisContext declaring)
    {
        for (var type = accessing; type is not null; type = type.DeclaringType)
            if (ReferenceEquals(type, declaring))
                return true;
        return false;
    }

    // A trampoline carries no work - jumps and nops only - so edges through it
    // preserve the guard's shape.
    private static bool IsTrampoline(Block block) =>
        block.Instructions.All(i => i.OpCode is OpCode.Jump or OpCode.Nop);

    // Every non-trampoline predecessor reaching `block`; trampolines are
    // transparent, so the guard behind them still counts as the raise's source.
    private static List<Block> TrampolineSources(Block block)
    {
        var sources = new List<Block>();
        var seen = new HashSet<Block>();
        var pending = new Stack<Block>(block.Predecessors);
        while (pending.Count > 0)
        {
            var current = pending.Pop();
            if (!seen.Add(current))
                continue;
            if (IsTrampoline(current))
                foreach (var predecessor in current.Predecessors)
                    pending.Push(predecessor);
            else
                sources.Add(current);
        }
        return sources;
    }

    private static bool ReachesOnlyThroughTrampolines(Block from, Block into)
    {
        var seen = new HashSet<Block>();
        var pending = new Stack<Block>();
        pending.Push(from);
        while (pending.Count > 0)
        {
            var current = pending.Pop();
            if (ReferenceEquals(current, into))
                return true;
            if (!seen.Add(current) || !IsTrampoline(current))
                continue;
            foreach (var successor in current.Successors)
                pending.Push(successor);
        }
        return false;
    }

    private static Dictionary<LocalVariable, int> CountLocalUses(ISILControlFlowGraph cfg)
    {
        var uses = new Dictionary<LocalVariable, int>();
        foreach (var instruction in cfg.Blocks.SelectMany(b => b.Instructions))
            foreach (var local in instruction.Sources.OfType<LocalVariable>())
                uses[local] = uses.GetValueOrDefault(local) + 1;
        return uses;
    }
}
