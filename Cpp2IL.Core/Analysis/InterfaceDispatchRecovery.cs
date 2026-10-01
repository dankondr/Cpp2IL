using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

// Recovers interface calls from GetInterfaceInvokeData which is usually inlined. that method scans klass->interfaceOffsets
// for the declaring interface, indexes the vtable with (entryOffset + slot), or falls back to a slow path
// helper when the scan fails.
public static class InterfaceDispatchRecovery
{
    public static Action? Run(MethodAnalysisContext method)
    {
        // offsets below are the 64-bit Il2CppClass layout
        if (method.AppContext.Binary.PointerSizeBytes != 8)
            return null;

        var cfg = method.ControlFlowGraph!;

        var (definitions, homeBlock) = BuildMaps(cfg);
        var changed = DistributePhiedConstructions(method, cfg, definitions, homeBlock);
        if (changed)
            (definitions, homeBlock) = BuildMaps(cfg);

        var index = new DefUseIndex(cfg);
        var lookups = new List<Match>();

        MatchAndRewrite(method, cfg, index, definitions, homeBlock, lookups, ref changed);

        if (changed)
        {
            DeadCodeEliminator.Run(method);

            foreach (var lookup in lookups)
                TryExciseLookup(cfg, lookup, definitions, homeBlock);

            DeadCodeEliminator.Run(method);
        }

        // Class-pointer types (Il2CppClass<K>) are seeded after this pass runs, so idioms that
        // match on the interface/type operand may only become recognizable later - retry the
        // matchers in the deferred finish step before giving up on a lookup.
        return () =>
        {
            var (lateDefinitions, lateHomeBlock) = BuildMaps(cfg);
            var lateIndex = new DefUseIndex(cfg);
            var lateChanged = false;
            MatchAndRewrite(method, cfg, lateIndex, lateDefinitions, lateHomeBlock, lookups, ref lateChanged);
            if (lateChanged)
            {
                DeadCodeEliminator.Run(method);
                foreach (var lookup in lookups)
                    TryExciseLookup(cfg, lookup, lateDefinitions, lateHomeBlock);
                DeadCodeEliminator.Run(method);
            }

            TrimResolvedCallArgumentsUsingLookups(cfg, lookups, lateDefinitions);
            DeadCodeEliminator.Run(method);

            foreach (var lookup in lookups)
                TryExciseLookup(cfg, lookup, lateDefinitions, lateHomeBlock);

            DeadCodeEliminator.Run(method);
        };
    }

    private static void MatchAndRewrite(MethodAnalysisContext method, ISILControlFlowGraph cfg,
        DefUseIndex index, Dictionary<LocalVariable, Instruction> definitions,
        Dictionary<Instruction, Block> homeBlock, List<Match> lookups, ref bool changed)
    {
        foreach (var block in cfg.Blocks.ToList())
        {
            foreach (var instruction in block.Instructions.ToList())
            {
                if (instruction.OpCode is not (OpCode.IndirectCall or OpCode.IndirectJump))
                    continue;

                if (MatchDispatch(method, instruction, index, definitions, homeBlock) is { } match)
                {
                    RewriteDispatch(method, instruction, block, match, definitions);
                    lookups.Add(match);
                    changed = true;
                    continue;
                }

                if (MatchVirtualDispatch(method, instruction, definitions, homeBlock) is { } virtualMatch)
                {
                    RewriteVirtualDispatch(method, instruction, block, virtualMatch, definitions);
                    changed = true;
                    continue;
                }

                if (instruction.OpCode == OpCode.IndirectJump
                    && TryRewriteMergedTailDispatch(method, instruction, index, definitions, homeBlock))
                    changed = true;
            }
        }
    }

    private static void TrimResolvedCallArgumentsUsingLookups(ISILControlFlowGraph cfg,
        List<Match> lookups, Dictionary<LocalVariable, Instruction> definitions)
    {
        foreach (var call in cfg.Instructions)
        {
            if (!call.IsCall || call.Operands[0] is not MethodAnalysisContext called)
                continue;

            var expected = 1 + (call.OpCode == OpCode.Call ? 1 : 0)
                + (called.IsStatic ? 0 : 1) + called.Parameters.Count;
            for (var i = call.Operands.Count - 1; i >= expected; i--)
            {
                if (call.Operands[i] is not LocalVariable argument
                    || ChaseCopies(definitions, argument) is not
                        { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: LocalVariable invokeData }] }
                    || !lookups.Any(lookup => lookup.IsMergeOperand(definitions, invokeData)))
                    continue;

                call.RemoveOperandAt(i);
            }
        }
    }

    internal static (Dictionary<LocalVariable, Instruction> Definitions, Dictionary<Instruction, Block> HomeBlock)
        BuildMaps(ISILControlFlowGraph cfg)
    {
        var definitions = new Dictionary<LocalVariable, Instruction>();
        var homeBlock = new Dictionary<Instruction, Block>();

        foreach (var block in cfg.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                homeBlock[instruction] = block;
                if (instruction.Destination is LocalVariable destination)
                    definitions[destination] = instruction;
            }
        }

        return (definitions, homeBlock);
    }

    private const long VTableOffset = 0x138;
    private const long VTableOffset32 = 0xC0;
    private const int InvokeDataShift = 4; // sizeof(VirtualInvokeData) == 16

    // The VirtualInvokeData pointer arriving at the dispatch: an explicit phi (whose source defs
    // are MergeDefs), or an implicit phi - several defs of the same local reaching the use on
    // different edges after SSA removal.
    private record struct Match(
        MethodAnalysisContext Resolved,
        Instruction? InvokeDataPhi,
        Block Merge,
        Instruction SlowCall,
        LocalVariable KlassLocal,
        Instruction? GenericVirtualHelper = null,
        RuntimeMethodInfoAnalysisContext? ConcreteMethodInfo = null,
        int? OutParamBuffer = null,
        HashSet<Instruction>? MergeDefs = null)
    {
        // An operand's def-chain leads to the merged invokeData pointer when it ends at the phi
        // itself or at one of its per-edge sources.
        public bool IsMergeOperand(Dictionary<LocalVariable, Instruction> definitions, IOperand operand)
        {
            if (operand is not LocalVariable local
                || ChaseCopies(definitions, local) is not { } definition)
                return false;
            return ReferenceEquals(definition, InvokeDataPhi)
                || MergeDefs != null && MergeDefs.Contains(definition);
        }
    }

    private record struct GenericVirtualTarget(
        MemoryOperand TargetLoad,
        Instruction Helper,
        RuntimeMethodInfoAnalysisContext MethodInfo);

    private static Match? MatchDispatch(MethodAnalysisContext method, Instruction dispatch,
        DefUseIndex index, Dictionary<LocalVariable, Instruction> definitions,
        Dictionary<Instruction, Block> homeBlock)
    {
        // the call target loads VirtualInvokeData::methodPtr, separately or folded in
        var rawTargetLoad = dispatch.Operands[0] switch
        {
            MemoryOperand folded => folded,
            LocalVariable target when ChaseCopies(definitions, target) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand loaded] } => loaded,
            _ => default(MemoryOperand?)
        };
        var genericTarget = rawTargetLoad is { } concreteTargetLoad
            ? MatchGenericVirtualTarget(method, concreteTargetLoad, definitions)
            : null;
        var targetLoad = genericTarget?.TargetLoad ?? rawTargetLoad;

        if (targetLoad is not { Index: null, Scale: 0, Addend: 0, Base: LocalVariable invokeData })
            return MatchOutParamDispatch(method, dispatch, definitions, homeBlock, index);

        // The invokeData pointer may reach the dispatch through an explicit phi or, after SSA
        // removal, through several defs of the same local on different predecessor edges.
        Instruction? phi = null;
        List<Instruction> mergeDefs;
        if (ChaseCopies(definitions, invokeData) is
            { OpCode: OpCode.Phi, Operands: [_, LocalVariable first, LocalVariable second] } found)
        {
            phi = found;
            mergeDefs = [found];
            if (ChaseCopies(definitions, first) is { } firstDef)
                mergeDefs.Add(firstDef);
            if (ChaseCopies(definitions, second) is { } secondDef)
                mergeDefs.Add(secondDef);
        }
        else if (index.MergeSources(invokeData, dispatch) is { } sources
                 && sources.Select(source => source.Def).ToList() is { Count: >= 2 } defs)
        {
            mergeDefs = defs;
        }
        else
            return MatchOutParamDispatch(method, dispatch, definitions, homeBlock, index);

        return MatchLookupPhi(method, phi, mergeDefs, genericTarget?.MethodInfo,
            genericTarget?.Helper, null, definitions, homeBlock, dispatch, index);
    }

    // Everything after the invokeData merge: one side must be the unresolved slow-path call, the
    // other the vtable entry chain. With genericMethodInfo the resolved method comes from the
    // concrete RuntimeMethod* argument; otherwise the constant slot indexes the interface.
    private static Match? MatchLookupPhi(MethodAnalysisContext method, Instruction? phi,
        List<Instruction> mergeDefs,
        RuntimeMethodInfoAnalysisContext? genericMethodInfo, Instruction? genericHelper,
        int? outParamBuffer,
        Dictionary<LocalVariable, Instruction> definitions, Dictionary<Instruction, Block> homeBlock,
        Instruction dispatch, DefUseIndex index)
    {
        var slowCall = mergeDefs.FirstOrDefault(def => def.OpCode == OpCode.Call);
        var vtableEntry = mergeDefs.FirstOrDefault(def =>
            !ReferenceEquals(def, slowCall) && !ReferenceEquals(def, phi));

        // slow path is GetInterfaceInvokeDataFromVTableSlowPath(obj, interface, slot), never resolved
        if (slowCall is not { Operands: [Immediate, _, _, var interfaceOperand, var slotOperand, ..] })
            return null;

        var declaringInterface = interfaceOperand switch
        {
            RuntimeClassTypeAnalysisContext runtimeClass => runtimeClass.RepresentedType,
            TypeAnalysisContext type => type,
            LocalVariable local when ChaseCopies(definitions, local) is
                { OpCode: OpCode.Move, Operands: [_, RuntimeClassTypeAnalysisContext runtimeClass] }
                => runtimeClass.RepresentedType,
            LocalVariable local when ChaseCopies(definitions, local) is
                { OpCode: OpCode.Move, Operands: [_, TypeAnalysisContext type] } => type,
            LocalVariable { Type: RuntimeClassTypeAnalysisContext runtimeClass } => runtimeClass.RepresentedType,
            LocalVariable { Type: TypeAnalysisContext type } => type,
            _ => null,
        };
        if (declaringInterface == null && genericMethodInfo != null)
            declaringInterface = ResolveRuntimeMethodInfo(interfaceOperand, definitions)?.RepresentedMethod.DeclaringType;
        if (declaringInterface == null
            || !(declaringInterface is GenericInstanceTypeAnalysisContext { GenericType.IsInterface: true } || declaringInterface.IsInterface))
            return null;

        Immediate? slotImmediate = slotOperand switch
        {
            Immediate immediate => immediate,
            LocalVariable local when ChaseCopies(definitions, local) is
                { OpCode: OpCode.Move, Operands: [_, Immediate immediate] } => immediate,
            _ => null,
        };

        MethodAnalysisContext resolved;
        LocalVariable klassLocal;
        if (genericMethodInfo is { } generic)
        {
            var slotProven = slotImmediate is { Value: >= 0 and <= ushort.MaxValue } concreteSlot
                ? ResolveInterfaceSlot(declaringInterface, (int)concreteSlot.Value) is { } openMethod
                    && SameMethodDefinition(openMethod, generic.RepresentedMethod)
                : ResolveRuntimeMethodInfo(slotOperand, definitions) is { } openMethodInfo
                    && SameMethodDefinition(openMethodInfo.RepresentedMethod, generic.RepresentedMethod);
            if (!slotProven
                || !SameDeclaringType(declaringInterface, generic.RepresentedMethod.DeclaringType)
                || MatchVTableEntryChain(definitions, vtableEntry,
                    slotImmediate is { } immediate ? immediate : slotOperand, index) is not { } genericKlass)
                return null;

            resolved = generic.RepresentedMethod;
            klassLocal = genericKlass;
        }
        else
        {
            if (slotImmediate is not { Value: >= 0 and <= ushort.MaxValue } concreteSlot)
                return null;

            var slot = (int)concreteSlot.Value;
            // fast path computes klass + vtableOffset + ((entryOffset + slot) << 4) (the +slot folds away for slot 0)
            if (MatchVTableEntryChain(definitions, vtableEntry, new Immediate(slot), index) is not { } concreteKlass
                || ResolveInterfaceSlot(declaringInterface, slot) is not { } concreteMethod)
                return null;

            resolved = concreteMethod;
            klassLocal = concreteKlass;
        }

        if (!homeBlock.TryGetValue(phi ?? dispatch, out var merge))
            return null;

        return new Match(resolved, phi, merge, slowCall, klassLocal,
            genericHelper, genericMethodInfo, outParamBuffer,
            MergeDefs: mergeDefs.ToHashSet());
    }

    private static GenericVirtualTarget? MatchGenericVirtualTarget(MethodAnalysisContext method,
        MemoryOperand targetLoad, Dictionary<LocalVariable, Instruction> definitions)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        if (targetLoad is not
            {
                Base: LocalVariable inflatedMethodInfo,
                Index: null,
                Scale: 0,
                Addend: var methodPointerOffset
            }
            || methodPointerOffset != pointerSize
            || ChaseCopies(definitions, inflatedMethodInfo) is not { OpCode: OpCode.Call } helper)
            return null;

        var concreteMethods = helper.Operands.Skip(2)
            .Select(operand => AsConcreteMethodInfo(operand, definitions)).OfType<RuntimeMethodInfoAnalysisContext>()
            .GroupBy(info => info.RepresentedMethod.FullNameWithSignature).Select(group => group.First()).ToList();
        if (concreteMethods is not [{ } concreteMethod])
            return null;

        var invokeDataLoads = helper.Operands.Skip(2).Select(operand => LoadedMemoryOperand(operand, definitions))
            .OfType<MemoryOperand>()
            .Where(load => load is { Base: LocalVariable, Index: null, Scale: 0 }
                && load.Addend == pointerSize)
            .ToList();
        if (invokeDataLoads is not [{ Base: LocalVariable invokeData }])
            return null;

        return new GenericVirtualTarget(new MemoryOperand(invokeData, null, 0, 0), helper, concreteMethod);
    }

    // il2cpp_codegen_get_generic_interface_method / get_generic_virtual_method take a
    // VirtualInvokeData* out-param: internal(methodDefinition=[invokeData+ptrSize], method,
    // &callerBuffer) fills it and the dispatch then reads [callerBuffer]. The buffer is a
    // caller stack slot, so the target load is stack[n] (or [bufferPointer] where
    // bufferPointer = &stack[n]) - never the invokeData phi the pointer form needs.
    private static Match? MatchOutParamDispatch(MethodAnalysisContext method, Instruction dispatch,
        Dictionary<LocalVariable, Instruction> definitions, Dictionary<Instruction, Block> homeBlock,
        DefUseIndex index)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        if (dispatch.Operands.Count == 0)
            return null;

        var targetSource = dispatch.Operands[0] switch
        {
            LocalVariable target when ChaseCopies(definitions, target) is
                { OpCode: OpCode.Move, Operands: [_, var loaded] } => loaded,
            var operand => operand,
        };
        var bufferSlot = targetSource switch
        {
            StackOffset slot => slot.Offset,
            MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable bufferBase }
                => BufferSlotOf(bufferBase, definitions),
            _ => (int?)null,
        };
        if (bufferSlot is not { } slotIndex)
            return null;

        // Look for exactly one still-unresolved helper carrying the full proof triple:
        // the buffer address, the [invokeData + ptrSize] method definition, and one concrete
        // method info. Any ambiguity leaves the diagnostic.
        Match? found = null;
        foreach (var candidate in homeBlock.Keys)
        {
            if (candidate.OpCode is not (OpCode.Call or OpCode.CallVoid)
                || candidate.Operands.Count == 0 || candidate.Operands[0] is not Immediate)
                continue;

            var args = candidate.Operands.Skip(candidate.OpCode == OpCode.CallVoid ? 1 : 2).ToList();
            if (args.Count(operand => IsBufferAddress(operand, slotIndex, definitions)) != 1)
                continue;

            var methodDefinitions = args.Select(operand => LoadedMemoryOperand(operand, definitions))
                .OfType<MemoryOperand>()
                .Where(load => load is { Index: null, Scale: 0, Base: LocalVariable } && load.Addend == pointerSize)
                .ToList();
            if (methodDefinitions is not [{ Base: LocalVariable invokeData }])
                continue;

            var methodInfos = args.Select(operand => AsConcreteMethodInfo(operand, definitions))
                .OfType<RuntimeMethodInfoAnalysisContext>()
                .GroupBy(info => info.RepresentedMethod.FullNameWithSignature)
                .Select(group => group.First()).ToList();
            if (methodInfos is not [{ } methodInfo])
                continue;

            if (ChaseCopies(definitions, invokeData) is not
                { OpCode: OpCode.Phi, Operands: [_, LocalVariable first, LocalVariable second] } phi)
                continue;

            var mergeDefs = new List<Instruction> { phi };
            if (ChaseCopies(definitions, first) is { } firstDef)
                mergeDefs.Add(firstDef);
            if (ChaseCopies(definitions, second) is { } secondDef)
                mergeDefs.Add(secondDef);

            var matched = MatchLookupPhi(method, phi, mergeDefs, methodInfo, candidate,
                slotIndex, definitions, homeBlock, dispatch, index);
            if (matched == null)
                continue;

            if (found != null)
                return null;
            found = matched;
        }

        return found;
    }

    // The stack slot a local points at, when it provably holds the address of one. `mov xN, sp`
    // lifts as Move(xN, 0) - a zero out-pointer argument is meaningless to the callee, so it can
    // only be the buffer's address; accept it only for slot 0.
    private static int? BufferSlotOf(LocalVariable local,
        Dictionary<LocalVariable, Instruction> definitions)
        => ChaseCopies(definitions, local) switch
        {
            { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: StackOffset slot }] } => slot.Offset,
            { OpCode: OpCode.Move, Operands: [_, Immediate { Value: 0 }] } => 0,
            _ => null,
        };

    private static bool IsBufferAddress(IOperand operand, int slot,
        Dictionary<LocalVariable, Instruction> definitions)
    {
        var value = operand switch
        {
            LocalVariable local => ChaseCopies(definitions, local) is
                { OpCode: OpCode.Move, Operands: [_, var source] } ? source : null,
            _ => operand,
        };
        return value switch
        {
            AddressOf { Target: StackOffset { Offset: var offset } } => offset == slot,
            Immediate { Value: 0 } => slot == 0,
            _ => false,
        };
    }

    private static RuntimeMethodInfoAnalysisContext? AsConcreteMethodInfo(IOperand operand,
        Dictionary<LocalVariable, Instruction> definitions) => operand switch
    {
        RuntimeMethodInfoAnalysisContext
        {
            RepresentedMethod: ConcreteGenericMethodAnalysisContext concrete
        } info when !concrete.IsPartialInstantiation
            && !concrete.IsStatic
            && concrete.TypeGenericParameters.All(type => type is not GenericParameterTypeAnalysisContext)
            && concrete.MethodGenericParameters.All(type => type is not GenericParameterTypeAnalysisContext)
            => info,
        LocalVariable { Type: RuntimeMethodInfoAnalysisContext info }
            => AsConcreteMethodInfo(info, definitions),
        LocalVariable local when ChaseCopies(definitions, local) is
            { OpCode: OpCode.Move, Operands: [_, RuntimeMethodInfoAnalysisContext info] }
            => AsConcreteMethodInfo(info, definitions),
        _ => null,
    };

    private static MemoryOperand? LoadedMemoryOperand(IOperand operand,
        Dictionary<LocalVariable, Instruction> definitions) => operand switch
    {
        MemoryOperand memory => memory,
        LocalVariable local when ChaseCopies(definitions, local) is
            { OpCode: OpCode.Move, Operands: [_, MemoryOperand memory] } => memory,
        _ => null,
    };

    private static RuntimeMethodInfoAnalysisContext? ResolveRuntimeMethodInfo(IOperand operand,
        Dictionary<LocalVariable, Instruction> definitions)
    {
        var load = operand switch
        {
            MemoryOperand memory => memory,
            LocalVariable local when ChaseCopies(definitions, local) is
                { OpCode: OpCode.Move, Operands: [_, MemoryOperand memory] } => memory,
            _ => default(MemoryOperand?),
        };
        if (load is not { Base: LocalVariable methodInfoLocal })
            return null;

        return ChaseCopies(definitions, methodInfoLocal) switch
        {
            { OpCode: OpCode.Move, Operands: [_, RuntimeMethodInfoAnalysisContext methodInfo] } => methodInfo,
            _ => methodInfoLocal.Type as RuntimeMethodInfoAnalysisContext,
        };
    }

    private static bool SameMethodDefinition(MethodAnalysisContext left, MethodAnalysisContext right)
        => ReferenceEquals(MethodIdentity(left), MethodIdentity(right));

    private static bool SameDeclaringType(TypeAnalysisContext left, TypeAnalysisContext? right)
    {
        left = (left as GenericInstanceTypeAnalysisContext)?.GenericType ?? left;
        right = (right as GenericInstanceTypeAnalysisContext)?.GenericType ?? right;
        return right != null && (ReferenceEquals(left.Definition, right.Definition)
            || left.FullName == right.FullName && left.DeclaringAssembly?.Name == right.DeclaringAssembly?.Name);
    }

    internal static LocalVariable? MatchVTableEntryChain(Dictionary<LocalVariable, Instruction> definitions, Instruction? vtableEntry, int slot)
        => MatchVTableEntryChain(definitions, vtableEntry, new Immediate(slot));

    // The fast path computes &klass->vtable[entryOffset + slot], which codegen associates and
    // folds differently across compilers and slots:
    //   x86 style:   (klass + (SXTW(entryOffset + slot) << 4)) + vtableOffset
    //   ARM64 style: klass + (SXTW(entryOffset) << 4) + (vtableOffset + slot * sizeof(VirtualInvokeData))
    // - a constant slot folds into the vtable base addend, never into the index. Decompose the
    // add tree instead of fixing an association, then require the parts to agree: exactly one
    // klass = [receiver] leaf, exactly one `<< sizeof(VirtualInvokeData)` leaf, and immediates
    // summing to vtableOffset, or to vtableOffset + slot*16 when the slot provably folded there.
    private static LocalVariable? MatchVTableEntryChain(Dictionary<LocalVariable, Instruction> definitions,
        Instruction? vtableEntry, IOperand slotOperand, DefUseIndex? index = null)
    {
        // Def of `local` live at `use`: reaching-def aware so the same register-versioned name can
        // hold the chain on one edge while an unrelated def dominates elsewhere.
        Instruction? ResolveDef(LocalVariable local, Instruction? use)
        {
            if (index == null || use == null)
                return ChaseCopies(definitions, local);

            var visited = new HashSet<LocalVariable>();
            var current = local;
            var at = use;
            while (visited.Add(current))
            {
                if (index.ReachingDef(current, at) is not { } definition)
                    return null;
                if (definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable source] })
                {
                    current = source;
                    at = definition;
                    continue;
                }
                return definition;
            }
            return null;
        }

        // the byte size the slot contributes when it folds into a constant addend
        long? slotBytes = slotOperand switch
        {
            Immediate { Value: >= 0 and <= ushort.MaxValue } slot => slot.Value << InvokeDataShift,
            LocalVariable local when ChaseCopies(definitions, local) is
                { OpCode: OpCode.Move, Operands: [_, Immediate { Value: >= 0 and <= ushort.MaxValue } slot] }
                => slot.Value << InvokeDataShift,
            _ => null,
        };

        var constant = 0L;
        LocalVariable? klassCandidate = null;
        LocalVariable? indexOperand = null;
        Instruction? indexUse = null;
        var leaves = 0;
        var pending = new Stack<(IOperand Operand, Instruction Use)>();

        if (vtableEntry is { OpCode: OpCode.Add, Operands: [_, var first, var second] })
        {
            pending.Push((first, vtableEntry));
            pending.Push((second, vtableEntry));
        }

        while (pending.Count > 0 && leaves < 8)
        {
            var (operand, use) = pending.Pop();
            if (operand is Immediate immediate)
            {
                constant += immediate.Value;
                continue;
            }

            if (operand is not LocalVariable local)
                return null;
            leaves++;

            var definition = ResolveDef(local, use);
            switch (definition)
            {
                case { OpCode: OpCode.Add, Operands: [_, var addLeft, var addRight] }:
                    pending.Push((addLeft, definition));
                    pending.Push((addRight, definition));
                    continue;
                case { OpCode: OpCode.ShiftLeft, Operands: [_, LocalVariable indexLocal, Immediate { Value: InvokeDataShift }] }
                    when indexOperand == null:
                    indexOperand = indexLocal;
                    indexUse = definition;
                    continue;
                case { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable }] }
                    when klassCandidate == null:
                    klassCandidate = local;
                    continue;
                default:
                    return null;
            }
        }

        if (pending.Count != 0 || klassCandidate == null || indexOperand == null)
            return null;

        // a folded slot contributes slot * sizeof(VirtualInvokeData) to the constant addend
        var folded = constant != VTableOffset;
        if (folded && constant != VTableOffset + slotBytes)
            return null;

        var entryOffset = ResolveDef(indexOperand, indexUse);
        if (entryOffset is { OpCode: OpCode.SignExtend32, Operands: [_, LocalVariable unextended] })
            entryOffset = ResolveDef(unextended, entryOffset);

        IOperand? entryOffsetSource = null;
        if (entryOffset is { OpCode: OpCode.Add, Operands: [_, var beforeSlot, var slotAddend] })
        {
            // the slot can only be contributed once - an index-side addend is wrong when the
            // constant already folded it in
            if (folded || !SameSlotOperand(slotAddend, slotOperand, definitions))
                return null;

            entryOffsetSource = beforeSlot;
        }
        else if (folded || slotOperand is Immediate { Value: 0 })
        {
            if (entryOffset is { OpCode: OpCode.Move, Operands: [_, var source] })
                entryOffsetSource = source;
        }
        else
            return null;

        var entryOffsetLoad = entryOffsetSource switch
        {
            MemoryOperand memory => memory,
            LocalVariable local when ResolveDef(local, entryOffset) is
                { OpCode: OpCode.Move, Operands: [_, MemoryOperand memory] } => memory,
            LocalVariable local when ChaseCopies(definitions, local) is
                { OpCode: OpCode.Move, Operands: [_, MemoryOperand memory] } => memory,
            _ => default(MemoryOperand?),
        };
        if (entryOffsetLoad is not { Base: not null })
            return null;

        return klassCandidate;
    }

    private static bool SameSlotOperand(IOperand left, IOperand right,
        Dictionary<LocalVariable, Instruction> definitions)
    {
        static IOperand Unwrap(IOperand operand, Dictionary<LocalVariable, Instruction> definitions) =>
            operand is LocalVariable local && ChaseCopies(definitions, local) is
                { OpCode: OpCode.Move, Operands: [_, var source] } && source is not LocalVariable
                ? source
                : operand;

        return Unwrap(left, definitions).Equals(Unwrap(right, definitions));
    }

    internal static Instruction? Definition(Dictionary<LocalVariable, Instruction> definitions, LocalVariable local)
        => definitions.TryGetValue(local, out var definition) ? definition : null;

    internal static Instruction? ChaseCopies(Dictionary<LocalVariable, Instruction> definitions, LocalVariable local)
    {
        var visited = new HashSet<LocalVariable>();

        while (visited.Add(local))
        {
            if (Definition(definitions, local) is not { } definition)
                return null;

            if (definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable source] })
            {
                local = source;
                continue;
            }

            return definition;
        }

        return null;
    }

    private static MethodAnalysisContext? ResolveInterfaceSlot(TypeAnalysisContext declaringInterface, int slot)
    {
        if (declaringInterface is GenericInstanceTypeAnalysisContext genericInstance)
        {
            var baseMethod = genericInstance.GenericType.Methods.FirstOrDefault(m => m.Definition?.slot == slot);
            return baseMethod == null ? null : new ConcreteGenericMethodAnalysisContext(baseMethod, genericInstance.GenericArguments, []);
        }

        return declaringInterface.Methods.FirstOrDefault(m => m.Definition?.slot == slot);
    }

    private static void RewriteDispatch(MethodAnalysisContext method, Instruction dispatch, Block block, Match match, Dictionary<LocalVariable, Instruction> definitions)
    {
        var resolved = match.Resolved;
        var callingConventions = resolved.AppContext.InstructionSet.CallingConventionResolver;
        var isTailCall = dispatch.OpCode == OpCode.IndirectJump;

        if (match is { GenericVirtualHelper: { } helper, ConcreteMethodInfo: { } methodInfo })
        {
            for (var i = 1; i < dispatch.Operands.Count; i++)
                if (dispatch.Operands[i] is LocalVariable local
                    && ReferenceEquals(ChaseCopies(definitions, local), helper))
                    dispatch.SetOperand(i, methodInfo);
            helper.OpCode = OpCode.Nop;
            helper.SetOperands();
        }

        // an IndirectJump's return register operand is a stale use rather than a return slot, so rebuild from scratch
        if (isTailCall)
        {
            var operands = new List<IOperand> { resolved };

            if (!resolved.IsVoid)
                operands.Add(new LocalVariable("interfaceTailCallResult", callingConventions?.ReturnRegister(resolved) ?? new Register(null, "rax")));

            operands.AddRange(dispatch.Operands.Skip(2));
            dispatch.SetOperands(operands);
        }
        else
        {
            if (resolved.IsVoid)
                dispatch.RemoveOperandAt(1);

            dispatch.SetOperand(0, resolved);
        }

        dispatch.OpCode = resolved.IsVoid ? OpCode.CallVoid : OpCode.Call;
        callingConventions?.RemapRawArguments(dispatch, resolved);

        // name [phi+8] as the hidden MethodInfo param, like ResolveVirtualCalls. A tail call's target
        // register doubles as an argument slot, so a stale [phi] load can turn up as an argument too,
        // and gets a placeholder so the VirtualInvokeData pointer still dies.
        var assembly = resolved.DeclaringType?.DeclaringAssembly ?? method.DeclaringType?.DeclaringAssembly;
        for (var i = 1; i < dispatch.Operands.Count; i++)
        {
            if (dispatch.Operands[i] is not LocalVariable argument
                || ChaseCopies(definitions, argument) is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Base: LocalVariable loadBase } load] }
                || !match.IsMergeOperand(definitions, loadBase))
                continue;

            if (load.Addend == 8 && assembly != null)
                dispatch.SetOperand(i, new RuntimeMethodInfoAnalysisContext(resolved, assembly));
            else if (load.Addend == 0)
                dispatch.SetOperand(i, new Immediate(0));
        }

        // the out-param form instead names the caller stack buffer's fields: [slot+ptrSize] is
        // the hidden MethodInfo, a stale [slot] read is the methodPtr placeholder.
        if (match.OutParamBuffer is { } bufferSlot)
        {
            var pointerSize = method.AppContext.Binary.PointerSizeBytes;
            for (var i = 1; i < dispatch.Operands.Count; i++)
            {
                if (dispatch.Operands[i] is not LocalVariable argument
                    || ChaseCopies(definitions, argument) is not
                        { OpCode: OpCode.Move, Operands: [_, var argumentSource] })
                    continue;

                var field = argumentSource switch
                {
                    StackOffset stack when stack.Offset == bufferSlot => 0L,
                    StackOffset stack when stack.Offset == bufferSlot + pointerSize => (long)pointerSize,
                    MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable bufferBase }
                        when BufferSlotOf(bufferBase, definitions) == bufferSlot => 0L,
                    MemoryOperand { Index: null, Scale: 0, Addend: var addend, Base: LocalVariable bufferBase }
                        when addend == pointerSize && BufferSlotOf(bufferBase, definitions) == bufferSlot => addend,
                    _ => -1L,
                };

                if (field == pointerSize && assembly != null)
                    dispatch.SetOperand(i, new RuntimeMethodInfoAnalysisContext(resolved, assembly));
                else if (field == 0)
                    dispatch.SetOperand(i, new Immediate(0));
            }
        }

        if (isTailCall)
        {
            var returnOperands = !method.IsVoid && !resolved.IsVoid
                ? new List<IOperand> { dispatch.Operands[1] }
                : [];

            block.AddInstruction(new Instruction(-1, OpCode.Return, returnOperands));
            block.CalculateBlockType();
        }
    }

    // ===== class-virtual dispatch =====

    private record struct VirtualMatch(
        MethodAnalysisContext Resolved,
        LocalVariable KlassLocal,
        long TargetAddend);

    // Resolves [klass + vtableOffset + slot * sizeof(VirtualInvokeData)] dispatches where the
    // receiver's possible runtime types are proven by the def-chain (per-edge Newobj types,
    // phis of them, or a declared static type), rather than relying on the local's inferred
    // Type. Every candidate's vtable slot must agree on the same root declaration - the slot
    // the compiler actually indexed - or the dispatch stays indirect.
    private static VirtualMatch? MatchVirtualDispatch(MethodAnalysisContext method, Instruction dispatch,
        Dictionary<LocalVariable, Instruction> definitions, Dictionary<Instruction, Block> homeBlock)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var vtableOffset = pointerSize == 8 ? VTableOffset : VTableOffset32;
        var invokeDataSize = 2L * pointerSize;

        var targetLoad = dispatch.Operands.Count > 0
            ? dispatch.Operands[0] switch
            {
                MemoryOperand folded => folded,
                LocalVariable target when ChaseCopies(definitions, target) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand loaded] } => loaded,
                _ => default(MemoryOperand?)
            }
            : null;

        if (targetLoad is not { Index: null, Scale: 0, Base: LocalVariable klassLocal } load)
            return null;

        var relative = load.Addend - vtableOffset;
        if (relative < 0 || relative % invokeDataSize != 0)
            return null;
        var slot = (int)(relative / invokeDataSize);

        // klass must be a straight [receiver] load
        if (ChaseCopies(definitions, klassLocal) is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable receiver }] })
            return null;

        // the this argument must trace back to the same object the klass was loaded off
        if (dispatch.Operands.Count < 3 || dispatch.Operands[2] is not LocalVariable thisArg)
            return null;
        var receiverRoot = ChaseCopies(definitions, receiver);
        if (receiverRoot == null || !ReferenceEquals(receiverRoot, ChaseCopies(definitions, thisArg)))
            return null;

        var candidates = new HashSet<TypeAnalysisContext>();
        if (!CollectReceiverTypes(method, definitions, receiver, candidates) || candidates.Count == 0)
            return null;

        MethodAnalysisContext? root = null;
        foreach (var candidate in candidates)
        {
            var implementation = ResolveVTableSlot(method.AppContext, candidate, slot);
            var candidateRoot = implementation is { IsStatic: false } ? RootVirtualDeclaration(implementation) : null;
            if (candidateRoot is not { IsVirtual: true })
                return null;
            if (root == null)
                root = candidateRoot;
            else if (!ReferenceEquals(MethodIdentity(root), MethodIdentity(candidateRoot)))
                return null;
        }

        if (root == null
            || InstantiateRoot(method, root, candidates) is not { IsStatic: false } resolved
            || resolved.GenericParameters.Count > 0
            || resolved is ConcreteGenericMethodAnalysisContext concrete
                && concrete.MethodGenericParameters.Any(p => p is GenericParameterTypeAnalysisContext))
            return null;

        if (dispatch.OpCode == OpCode.IndirectJump
            && (method.IsVoid != resolved.IsVoid
                || (!method.IsVoid && method.ReturnType.FullName != resolved.ReturnType.FullName)
                || homeBlock[dispatch].Instructions[^1] != dispatch))
            return null;

        if (!VirtualSignatureProven(dispatch, resolved, klassLocal, load.Addend, pointerSize, definitions))
            return null;

        return new VirtualMatch(resolved, klassLocal, load.Addend);
    }

    // The receiver's concrete runtime types: each Newobj class operand, every phi operand, or
    // the declared static type when nothing better is provable. Any unresolvable source fails.
    private static bool CollectReceiverTypes(MethodAnalysisContext method,
        Dictionary<LocalVariable, Instruction> definitions, LocalVariable local,
        HashSet<TypeAnalysisContext> candidates, int depth = 0)
    {
        if (depth > 16)
            return false;

        if (ChaseCopies(definitions, local) is not { } definition)
            return AddStaticCandidate(local, candidates);

        switch (definition)
        {
            case { OpCode: OpCode.Newobj, Operands: [_, var klassOperand] }:
                return CollectKlassOperand(method, definitions, klassOperand, candidates, depth + 1);
            case { OpCode: OpCode.Phi }:
                for (var i = 1; i < definition.Operands.Count; i++)
                    if (definition.Operands[i] is not LocalVariable phiOperand
                        || !CollectReceiverTypes(method, definitions, phiOperand, candidates, depth + 1))
                        return false;
                return true;
            case { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable inner }] }:
                return CollectReceiverTypes(method, definitions, inner, candidates, depth + 1);
            default:
                return AddStaticCandidate(definition.Destination as LocalVariable ?? local, candidates);
        }
    }

    private static bool CollectKlassOperand(MethodAnalysisContext method,
        Dictionary<LocalVariable, Instruction> definitions, IOperand operand,
        HashSet<TypeAnalysisContext> candidates, int depth)
    {
        switch (operand)
        {
            case RuntimeClassTypeAnalysisContext { RepresentedType: { } represented }:
                candidates.Add(represented);
                return true;
            case TypeAnalysisContext type:
                candidates.Add(type);
                return true;
            case LocalVariable local
                when ChaseCopies(definitions, local) is { OpCode: OpCode.Move, Operands: [_, var source] }
                     && source is not LocalVariable:
                return CollectKlassOperand(method, definitions, source, candidates, depth + 1);
            case Immediate immediate:
                return ResolveTypeGlobal(method, immediate.UnsignedValue) is { } fromImmediate
                    && candidates.Add(fromImmediate);
            case MemoryOperand { Base: null, Index: null, Scale: 0, Addend: var address }:
                return ResolveTypeGlobal(method, (ulong)address) is { } fromGlobal
                    && candidates.Add(fromGlobal);
            default:
                return false;
        }
    }

    private static bool AddStaticCandidate(LocalVariable local, HashSet<TypeAnalysisContext> candidates)
    {
        // A RuntimeClassTypeAnalysisContext-typed local holds class metadata, not an instance.
        if (local.Type is RuntimeClassTypeAnalysisContext { RepresentedType: { } represented })
        {
            candidates.Add(represented);
            return true;
        }
        if (local.Type is { IsValueType: false, IsInterface: false } type && type.FullName != "System.Object")
        {
            candidates.Add(type);
            return true;
        }
        return false;
    }

    private static TypeAnalysisContext? ResolveTypeGlobal(MethodAnalysisContext context, ulong address) =>
        context.AppContext.LibCpp2IlContext.GetTypeGlobalByAddress(address) is { } typeGlobal
            ? context.AppContext.ResolveIl2CppType(typeGlobal)
            : null;

    private static MethodAnalysisContext? ResolveVTableSlot(ApplicationAnalysisContext appContext, TypeAnalysisContext type, int slot)
    {
        var definition = (type as GenericInstanceTypeAnalysisContext)?.GenericType.Definition ?? type.Definition;
        if (definition == null || slot >= definition.VtableCount)
            return null;

        if (appContext.ResolveContextForMethod(definition.VTable[slot]) is { } implementation)
            return type is GenericInstanceTypeAnalysisContext genericInstance
                ? new ConcreteGenericMethodAnalysisContext(implementation, genericInstance.GenericArguments, [])
                : implementation;

        // an abstract method has no implementation, try to resolve it as a declaration
        for (var declarer = type; declarer != null; declarer = declarer.BaseType)
            if (declarer.Methods.FirstOrDefault(m => m.Definition?.slot == slot) is { } declaration)
                return declaration;

        return null;
    }

    // The declaration that owns the vtable slot - what callvirt should name.
    private static MethodAnalysisContext? RootVirtualDeclaration(MethodAnalysisContext implementation)
    {
        var root = (implementation as ConcreteGenericMethodAnalysisContext)?.BaseMethodContext ?? implementation;
        var seen = new HashSet<MethodAnalysisContext>();
        while (root.BaseMethod is { } baseMethod && seen.Add(root))
            root = (baseMethod as ConcreteGenericMethodAnalysisContext)?.BaseMethodContext ?? baseMethod;
        return root;
    }

    private static object MethodIdentity(MethodAnalysisContext method) =>
        (object?)((method as ConcreteGenericMethodAnalysisContext)?.BaseMethodContext ?? method).Definition ?? method;

    // If the root declaration lives on a generic type definition, every candidate receiver must
    // agree on one instantiation; the emitted call then names the instantiated member.
    private static MethodAnalysisContext? InstantiateRoot(MethodAnalysisContext method,
        MethodAnalysisContext root, HashSet<TypeAnalysisContext> candidates)
    {
        var declaringType = root.DeclaringType;
        if (declaringType == null || declaringType.GenericParameters.Count == 0)
            return root;

        List<TypeAnalysisContext>? arguments = null;
        foreach (var candidate in candidates)
        {
            if (FindGenericInstantiation(candidate, declaringType) is not { } instance)
                return null;
            if (arguments == null)
                arguments = instance.GenericArguments;
            else if (!instance.GenericArguments.SequenceEqual(arguments))
                return null;
        }

        return arguments == null ? null : new ConcreteGenericMethodAnalysisContext(root, arguments, []);
    }

    private static GenericInstanceTypeAnalysisContext? FindGenericInstantiation(TypeAnalysisContext type,
        TypeAnalysisContext genericDefinition)
    {
        for (var declarer = type; declarer != null; declarer = declarer.BaseType)
            if (declarer is GenericInstanceTypeAnalysisContext instance
                && (ReferenceEquals(instance.GenericType, genericDefinition) || instance.GenericType == genericDefinition))
                return instance;
        return null;
    }

    // operand[3..3+P) are the declared parameters, operand[3+P] is the hidden MethodInfo field
    // loaded next to methodPtr. A byref/pointer parameter needs a provable address argument.
    private static bool VirtualSignatureProven(Instruction dispatch, MethodAnalysisContext resolved,
        LocalVariable klassLocal, long targetAddend, int pointerSize,
        Dictionary<LocalVariable, Instruction> definitions)
    {
        var parameters = resolved.Parameters;
        if (dispatch.Operands.Count < 4 + parameters.Count)
            return false;

        for (var i = 0; i < parameters.Count; i++)
        {
            if (parameters[i].ParameterType is not (ByRefTypeAnalysisContext or PointerTypeAnalysisContext))
                continue;

            var argument = dispatch.Operands[3 + i];
            var address = argument switch
            {
                AddressOf => true,
                LocalVariable l when ChaseCopies(definitions, l) is { OpCode: OpCode.Move, Operands: [_, AddressOf] } => true,
                _ => false,
            };
            if (!address)
                return false;
        }

        return dispatch.Operands[3 + parameters.Count] switch
        {
            RuntimeMethodInfoAnalysisContext => true,
            MemoryOperand { Index: null, Scale: 0, Base: LocalVariable operandBase, Addend: var addend }
                => ReferenceEquals(operandBase, klassLocal) && addend == targetAddend + pointerSize,
            LocalVariable local when ChaseCopies(definitions, local) is
                { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Base: LocalVariable loadBase, Addend: var addend }] }
                => ReferenceEquals(loadBase, klassLocal) && addend == targetAddend + pointerSize,
            _ => false,
        };
    }

    private static void RewriteVirtualDispatch(MethodAnalysisContext method, Instruction dispatch, Block block,
        VirtualMatch match, Dictionary<LocalVariable, Instruction> definitions)
    {
        var resolved = match.Resolved;
        var callingConventions = resolved.AppContext.InstructionSet.CallingConventionResolver;
        var isTailCall = dispatch.OpCode == OpCode.IndirectJump;

        if (isTailCall)
        {
            var operands = new List<IOperand> { resolved };
            if (!resolved.IsVoid)
                operands.Add(new LocalVariable("virtualTailCallResult",
                    callingConventions?.ReturnRegister(resolved) ?? new Register(null, "rax"), resolved.ReturnType));
            operands.AddRange(dispatch.Operands.Skip(2));
            dispatch.SetOperands(operands);
        }
        else
        {
            if (resolved.IsVoid)
                dispatch.RemoveOperandAt(1);
            dispatch.SetOperand(0, resolved);
        }

        dispatch.OpCode = resolved.IsVoid ? OpCode.CallVoid : OpCode.Call;
        dispatch.IsVirtualDispatch = true;
        callingConventions?.RemapRawArguments(dispatch, resolved);

        // The hidden argument is the MethodInfo loaded at [klass + slot * sizeof(VirtualInvokeData) + pointerSize];
        // a stale copy of the same load is the methodPtr and becomes a placeholder constant.
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var assembly = resolved.DeclaringType?.DeclaringAssembly ?? method.DeclaringType?.DeclaringAssembly;
        for (var i = 1; i < dispatch.Operands.Count; i++)
        {
            if (dispatch.Operands[i] is not LocalVariable argument
                || ChaseCopies(definitions, argument) is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Base: LocalVariable loadBase } load] }
                || !ReferenceEquals(loadBase, match.KlassLocal))
                continue;

            if (load.Addend == match.TargetAddend + pointerSize && assembly != null)
                dispatch.SetOperand(i, new RuntimeMethodInfoAnalysisContext(resolved, assembly));
            else if (load.Addend == match.TargetAddend)
                dispatch.SetOperand(i, new Immediate(0));
        }

        if (isTailCall)
        {
            var returnOperands = !method.IsVoid && !resolved.IsVoid
                ? new List<IOperand> { dispatch.Operands[1] }
                : [];

            block.AddInstruction(new Instruction(-1, OpCode.Return, returnOperands));
            block.CalculateBlockType();
        }
    }

    // ===== merged tail-call dispatch =====

    // `return a.VirtualX(...);` / `return b.VirtualY(...);` emitted as one shared `BR` in a merge
    // block, fed by a phi (or, after SSA removal, several defs of the same local) of different
    // vtable loads - one `[klass_i + vtableOffset + 16*slot_i]` per predecessor edge. Distribute
    // the jump: each edge keeps its own slot's resolved call, cloned into its own block.
    private static bool TryRewriteMergedTailDispatch(MethodAnalysisContext method, Instruction dispatch,
        DefUseIndex index, Dictionary<LocalVariable, Instruction> definitions,
        Dictionary<Instruction, Block> homeBlock)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var vtableOffset = pointerSize == 8 ? VTableOffset : VTableOffset32;
        var invokeDataSize = 2L * pointerSize;

        if (dispatch.Operands.Count < 2 || dispatch.Operands[0] is not LocalVariable target
            || !homeBlock.TryGetValue(dispatch, out var merge)
            || merge.Instructions[^1] != dispatch)
            return false;

        // Every predecessor edge must supply the target as its own [klass_i + vtable + 16*slot]
        // load - a single reaching def means the target isn't a per-edge value at all.
        if (index.MergeSources(target, dispatch) is not { } sources
            || sources.Count < 2 || sources.Count != merge.Predecessors.Count)
            return false;

        var calls = new List<(Block Edge, Instruction TargetDef, MethodAnalysisContext Resolved,
            LocalVariable Receiver, List<IOperand> Args, LocalVariable? ResultLocal)>();
        foreach (var (edge, targetDef) in sources)
        {
            if (targetDef is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand
                    { Index: null, Scale: 0, Base: LocalVariable klassLocal, Addend: var addend }] })
                return false;

            var relative = addend - vtableOffset;
            if (relative < 0 || relative % invokeDataSize != 0)
                return false;
            var slot = (int)(relative / invokeDataSize);

            // klass_i must be a straight [receiver] load on this edge
            if (index.ReachingDefOnEdge(klassLocal, edge) is not
                { OpCode: OpCode.Move, Operands: [_, MemoryOperand
                    { Index: null, Scale: 0, Addend: 0, Base: LocalVariable receiver }] })
                return false;

            var candidates = new HashSet<TypeAnalysisContext>();
            if (!CollectReceiverTypes(method, definitions, receiver, candidates) || candidates.Count == 0)
                return false;

            MethodAnalysisContext? root = null;
            foreach (var candidate in candidates)
            {
                var implementation = ResolveVTableSlot(method.AppContext, candidate, slot);
                var candidateRoot = implementation is { IsStatic: false } ? RootVirtualDeclaration(implementation) : null;
                if (candidateRoot is not { IsVirtual: true })
                    return false;
                if (root == null)
                    root = candidateRoot;
                else if (!ReferenceEquals(MethodIdentity(root), MethodIdentity(candidateRoot)))
                    return false;
            }

            if (root == null
                || InstantiateRoot(method, root, candidates) is not { IsStatic: false } resolved
                || resolved.GenericParameters.Count > 0
                || resolved is ConcreteGenericMethodAnalysisContext concrete
                    && concrete.MethodGenericParameters.Any(p => p is GenericParameterTypeAnalysisContext)
                || method.IsVoid != resolved.IsVoid
                || (!method.IsVoid && method.ReturnType.FullName != resolved.ReturnType.FullName))
                return false;

            // Map the jump's argument registers onto this edge's values: phi'd operands take the
            // edge input, [klass_i + addend + ptrSize] is the hidden MethodInfo, a stale
            // [klass_i + addend] is the methodPtr slot itself.
            var edgeIndex = sources.IndexOf((edge, targetDef));
            var declaringAssembly = resolved.DeclaringType?.DeclaringAssembly ?? method.DeclaringType?.DeclaringAssembly;
            var args = new List<IOperand>();
            var receiverFound = false;
            for (var i = 2; i < dispatch.Operands.Count; i++)
            {
                var edgeValue = EdgeValue(dispatch.Operands[i], edgeIndex, edge);

                if (edgeValue is MemoryOperand
                        { Index: null, Scale: 0, Base: LocalVariable loadBase, Addend: var argAddend }
                    && ReferenceEquals(loadBase, klassLocal))
                {
                    if (argAddend == addend + pointerSize && declaringAssembly != null)
                        args.Add(new RuntimeMethodInfoAnalysisContext(resolved, declaringAssembly));
                    else if (argAddend == addend)
                        args.Add(new Immediate(0));
                    else
                        return false;
                    continue;
                }

                if (edgeValue is LocalVariable candidate)
                {
                    if (SameEdgeValue(index, edge, candidate, receiver))
                    {
                        args.Add(receiver);
                        receiverFound = true;
                    }
                    else
                        args.Add(candidate);
                    continue;
                }

                args.Add(edgeValue ?? dispatch.Operands[i]);
            }

            if (!receiverFound)
                return false;

            LocalVariable? resultLocal = null;
            if (!resolved.IsVoid)
            {
                var callingConventions = resolved.AppContext.InstructionSet.CallingConventionResolver;
                resultLocal = new LocalVariable("mergedTailCallResult",
                    callingConventions?.ReturnRegister(resolved) ?? new Register(null, "rax"),
                    resolved.ReturnType);
            }

            calls.Add((edge, targetDef, resolved, receiver, args, resultLocal));
        }

        // All edges resolve: rewrite each predecessor's `Jump merge` into its own call + return.
        var cfg = method.ControlFlowGraph!;
        for (var i = 0; i < calls.Count; i++)
        {
            var (edge, _, resolved, _, args, resultLocal) = calls[i];

            var operands = new List<IOperand> { resolved };
            if (resultLocal != null)
                operands.Add(resultLocal);
            operands.AddRange(args);

            Instruction call;
            if (edge.Instructions[^1] is { OpCode: OpCode.Jump } jump)
            {
                jump.OpCode = resolved.IsVoid ? OpCode.CallVoid : OpCode.Call;
                jump.SetOperands(operands);
                call = jump;
            }
            else
            {
                call = new Instruction(-1, resolved.IsVoid ? OpCode.CallVoid : OpCode.Call, operands);
                edge.AddInstruction(call);
            }
            call.IsVirtualDispatch = true;
            resolved.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(call, resolved);

            var returnOperands = !method.IsVoid && !resolved.IsVoid && resultLocal != null
                ? new List<IOperand> { resultLocal }
                : [];
            edge.AddInstruction(new Instruction(-1, OpCode.Return, returnOperands));
            edge.CalculateBlockType();
        }

        // The merge's predecessors now return; unlink the merge entirely.
        foreach (var predecessor in merge.Predecessors.ToList())
            predecessor.Successors.Remove(merge);
        foreach (var successor in merge.Successors)
            successor.Predecessors.Remove(merge);
        merge.Predecessors.Clear();
        merge.Successors.Clear();
        cfg.Blocks.Remove(merge);
        return true;

        // The value `operand` carries on `edge`: the phi input when the operand's reaching def is
        // a merge phi, else the operand itself.
        IOperand? EdgeValue(IOperand operand, int edgeIndex, Block edge)
        {
            if (operand is not LocalVariable local)
                return operand;
            if (index.ReachingDef(local, dispatch) is { OpCode: OpCode.Phi } phi)
                return edgeIndex + 1 < phi.Operands.Count ? phi.Operands[edgeIndex + 1] : null;
            if (index.DefinitionsOf(local).Count > 1)
                return index.ReachingDefOnEdge(local, edge) is
                    { OpCode: OpCode.Move, Operands: [_, var source] } ? source : local;
            return local;
        }
    }

    // Two locals carry the same value on an edge when copy-chasing both lands on one def or one
    // undeffed local.
    private static bool SameEdgeValue(DefUseIndex index, Block edge, LocalVariable left,
        LocalVariable right)
    {
        if (ReferenceEquals(left, right))
            return true;
        return TerminalDef(index, edge, left) is { } leftDef
            && ReferenceEquals(leftDef, TerminalDef(index, edge, right));

        static object? TerminalDef(DefUseIndex index, Block edge, LocalVariable local)
        {
            var visited = new HashSet<LocalVariable>();
            var current = local;
            while (visited.Add(current))
            {
                if (index.ReachingDefOnEdge(current, edge) is not { } definition)
                    return current;
                if (definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable source] })
                {
                    current = source;
                    continue;
                }
                return definition;
            }
            return null;
        }
    }

    // ===== phi-carried construction distribution =====

    // A Newobj whose class operand - or whose paired .ctor's arguments, such as the delegate
    // method-pointer - is a Phi has no honest single CIL spelling: each predecessor supplies a
    // different value. When the allocation, its .ctor calls and the phis share one merge block,
    // every predecessor flows solely into the merge, and each edge's operand resolves to a
    // constant (typeof/methodof/immediate) or a dominating local, the Newobj+.ctor are cloned
    // per edge and the results re-merged with a Phi. Ambiguity keeps the diagnostic.
    internal static bool DistributePhiedConstructions(MethodAnalysisContext method, ISILControlFlowGraph cfg,
        Dictionary<LocalVariable, Instruction> definitions, Dictionary<Instruction, Block> homeBlock)
    {
        var dominators = method.DominatorInfo;
        var changed = false;

        var newobjs = cfg.Blocks.SelectMany(b => b.Instructions)
            .Where(i => i.OpCode == OpCode.Newobj && i.Operands is [LocalVariable, ..])
            .ToList();

        foreach (var newobj in newobjs)
        {
            var allocated = (LocalVariable)newobj.Operands[0];

            var ctorCalls = cfg.Blocks.SelectMany(b => b.Instructions)
                .Where(i => i.OpCode == OpCode.CallVoid
                            && i.Operands is [MethodAnalysisContext { Name: ".ctor" }, ..]
                            && i.Operands.Count > 1 && ReferenceEquals(i.Operands[1], allocated))
                .ToList();

            // a non-void .ctor form isn't a shape we can clone safely
            if (cfg.Blocks.SelectMany(b => b.Instructions).Any(i =>
                    i.OpCode == OpCode.Call && i.Operands is [MethodAnalysisContext { Name: ".ctor" }, ..]
                    && i.Operands.Count > 2 && ReferenceEquals(i.Operands[2], allocated)))
                continue;

            var phis = new List<Instruction>();
            void CollectPhiOperand(IOperand operand)
            {
                if (operand is LocalVariable local
                    && ChaseCopies(definitions, local) is { OpCode: OpCode.Phi } phi
                    && !phis.Contains(phi))
                    phis.Add(phi);
            }
            for (var i = 1; i < newobj.Operands.Count; i++)
                CollectPhiOperand(newobj.Operands[i]);
            foreach (var ctor in ctorCalls)
                for (var i = 2; i < ctor.Operands.Count; i++)
                    CollectPhiOperand(ctor.Operands[i]);

            if (phis.Count == 0)
                continue;

            var mergeBlocks = phis.Select(p => BlockOf(homeBlock, p)).Where(b => b != null).Distinct().ToList();
            if (mergeBlocks is not [ { } mergeBlock]
                || phis.Any(p => p.Operands.Count != 1 + mergeBlock.Predecessors.Count)
                || ctorCalls.Any(c => BlockOf(homeBlock, c) != mergeBlock)
                || BlockOf(homeBlock, newobj) is not { } newobjBlock
                || (newobjBlock != mergeBlock && !(dominators?.Dominates(newobjBlock, mergeBlock) ?? false))
                || mergeBlock.Predecessors.Count == 0
                || mergeBlock.Predecessors.Any(p => p.Successors.Count != 1 || p.Successors[0] != mergeBlock))
                continue;

            var predecessors = mergeBlock.Predecessors;
            var ownerList = new List<Instruction> { newobj }.Concat(ctorCalls).ToList();

            // Resolve every owner operand for every edge before mutating anything.
            var edgeOperands = new List<IOperand>?[predecessors.Count][];
            var failed = false;
            for (var edge = 0; edge < predecessors.Count && !failed; edge++)
            {
                var pred = predecessors[edge];
                edgeOperands[edge] = ownerList.Select(owner =>
                {
                    var operands = new List<IOperand>(owner.Operands.Count);
                    for (var j = 0; j < owner.Operands.Count; j++)
                    {
                        if (j == 0 && owner == newobj)
                        {
                            operands.Add(owner.Operands[0]); // placeholder, replaced below
                            continue;
                        }
                        if (owner != newobj && j == 1)
                        {
                            operands.Add(owner.Operands[1]); // receiver, replaced below
                            continue;
                        }
                        var resolved = ResolveEdgeOperand(owner.Operands[j], pred, edge, phis, definitions, homeBlock, dominators);
                        if (resolved == null)
                            failed = true;
                        // The newobj's class operand must be an actual type on this edge: left as a
                        // runtime local the emitted object has the wrong class, which is worse than
                        // keeping the diagnostic.
                        if (owner == newobj && j == 1 && resolved is not (TypeAnalysisContext or RuntimeClassTypeAnalysisContext))
                            failed = true;
                        operands.Add(resolved!);

                    }
                    return operands;
                }).ToArray();
            }
            if (failed || edgeOperands.Any(l => l == null))
                continue;

            // Every use of the allocated local or of a copy of it must live in the merge or a
            // dominated block; copy-definitions are dropped because the new local is only
            // defined once control reaches the merge.
            var aliases = CollectCopiesOf(cfg, allocated);
            var consumed = new HashSet<Instruction> { newobj };
            consumed.UnionWith(ctorCalls);

            var rewrite = new List<Instruction>();
            var aliasDefs = new List<Instruction>();
            var usable = true;
            foreach (var block in cfg.Blocks)
            {
                foreach (var instruction in block.Instructions)
                {
                    if (consumed.Contains(instruction))
                        continue;
                    if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable, LocalVariable source] }
                        && aliases.Contains(source))
                    {
                        aliasDefs.Add(instruction);
                        continue;
                    }
                    if (!UsesAlias(instruction, aliases))
                        continue;
                    if (block != mergeBlock && !(dominators?.Dominates(mergeBlock, block) ?? false))
                    {
                        usable = false;
                        break;
                    }
                    rewrite.Add(instruction);
                }
                if (!usable)
                    break;
            }
            if (!usable)
                continue;

            // The merge local must accept every edge's value through the copies SsaForm.Remove
            // inserts: with a narrower type (e.g. an interface sibling of an edge's Object fallback)
            // that pass decides no legal managed copy exists and drops the edge's write entirely.
            var phiType = allocated.Type is { IsValueType: true }
                ? allocated.Type
                : method.AppContext.SystemTypes.SystemObjectType;
            var phiDest = new LocalVariable($"{allocated.Name}_phi", allocated.Register, phiType);
            var phiOperands = new List<IOperand>(predecessors.Count + 1) { phiDest };
            for (var edge = 0; edge < predecessors.Count; edge++)
            {
                var pred = predecessors[edge];
                var edgeLocal = new LocalVariable($"{allocated.Name}_p{edge}", allocated.Register, allocated.Type);
                phiOperands.Add(edgeLocal);

                var perOwner = edgeOperands[edge]!;
                for (var ownerIndex = 0; ownerIndex < ownerList.Count; ownerIndex++)
                {
                    var operands = new List<IOperand>(perOwner[ownerIndex]!);
                    operands[ownerList[ownerIndex] == newobj ? 0 : 1] = edgeLocal;
                    InsertBeforeTerminator(pred, new Instruction(-1, ownerList[ownerIndex].OpCode, operands));
                }
            }

            var phiInsertAt = mergeBlock.Instructions.TakeWhile(i => i.OpCode == OpCode.Phi).Count();
            mergeBlock.Instructions.Insert(phiInsertAt, new Instruction(-1, OpCode.Phi, phiOperands));

            foreach (var instruction in rewrite)
                RebaseUses(instruction, aliases, phiDest);
            foreach (var instruction in aliasDefs.Concat(consumed))
            {
                instruction.OpCode = OpCode.Nop;
                instruction.SetOperands();
            }

            changed = true;
        }

        return changed;
    }

    // The operand that is valid on `pred`: constant operands are copied verbatim, copies of
    // constants resolve through, phi-carried operands take this edge's operand, and anything
    // else stays only if its definition dominates the predecessor.
    private static IOperand? ResolveEdgeOperand(IOperand operand, Block pred, int edge,
        List<Instruction> phis, Dictionary<LocalVariable, Instruction> definitions,
        Dictionary<Instruction, Block> homeBlock, DominatorInfo? dominators, int depth = 0)
    {
        if (depth > 8 || operand is not LocalVariable local)
            return operand;

        var definition = ChaseCopies(definitions, local);
        if (definition == null)
            return local; // never-defined register local - available everywhere

        if (definition.OpCode == OpCode.Phi && phis.Contains(definition))
            return definition.Operands[1 + edge] is { } edgeOperand
                ? ResolveEdgeOperand(edgeOperand, pred, edge, phis, definitions, homeBlock, dominators, depth + 1)
                : null;

        if (definition is { OpCode: OpCode.Move, Operands: [_, var source] } && source is not LocalVariable)
            return source is Immediate or TypeAnalysisContext or RuntimeMethodInfoAnalysisContext
                or StringLiteral or FloatLiteral or DoubleLiteral or Register or AddressOf
                ? source
                : DominatesDef(definition) ? local : null;

        return DominatesDef(definition) ? local : null;

        bool DominatesDef(Instruction def) =>
            dominators != null
            && homeBlock.TryGetValue(def, out var defBlock)
            && dominators.Dominates(defBlock, pred);
    }

    private static Block? BlockOf(Dictionary<Instruction, Block> homeBlock, Instruction instruction) =>
        homeBlock.TryGetValue(instruction, out var block) ? block : null;

    private static HashSet<LocalVariable> CollectCopiesOf(ISILControlFlowGraph cfg, LocalVariable allocated)
    {
        var aliases = new HashSet<LocalVariable> { allocated };
        var work = true;
        while (work)
        {
            work = false;
            foreach (var block in cfg.Blocks)
            foreach (var instruction in block.Instructions)
                if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable dest, LocalVariable source] }
                    && aliases.Contains(source) && aliases.Add(dest))
                    work = true;
        }
        return aliases;
    }

    private static bool UsesAlias(Instruction instruction, HashSet<LocalVariable> aliases)
    {
        var start = instruction.Destination is { } destination
            && instruction.Operands.Count > 0
            && ReferenceEquals(instruction.Operands[0], destination) ? 1 : 0;
        for (var i = start; i < instruction.Operands.Count; i++)
            if (OperandUsesAlias(instruction.Operands[i], aliases))
                return true;
        return false;
    }

    private static bool OperandUsesAlias(IOperand operand, HashSet<LocalVariable> aliases) =>
        operand switch
        {
            LocalVariable local => aliases.Contains(local),
            MemoryOperand { Base: LocalVariable memoryBase } when aliases.Contains(memoryBase) => true,
            MemoryOperand { Index: LocalVariable index } when aliases.Contains(index) => true,
            FieldReference field => aliases.Contains(field.Local),
            AddressOf { Target: LocalVariable target } => aliases.Contains(target),
            _ => false,
        };

    private static void RebaseUses(Instruction instruction, HashSet<LocalVariable> aliases, LocalVariable replacement)
    {
        var start = instruction.Destination is { } destination
            && instruction.Operands.Count > 0
            && ReferenceEquals(instruction.Operands[0], destination) ? 1 : 0;
        for (var i = start; i < instruction.Operands.Count; i++)
            if (RebaseOperand(instruction.Operands[i], aliases, replacement) is { } mapped)
                instruction.SetOperand(i, mapped);
    }

    private static IOperand? RebaseOperand(IOperand operand, HashSet<LocalVariable> aliases, LocalVariable? replacement) =>
        operand switch
        {
            LocalVariable local when aliases.Contains(local) => replacement!,
            MemoryOperand { Base: LocalVariable memoryBase } memory when aliases.Contains(memoryBase)
                => new MemoryOperand(replacement!, memory.Index, memory.Addend, memory.Scale, memory.AccessSize),
            MemoryOperand { Index: LocalVariable index } memory when aliases.Contains(index)
                => new MemoryOperand(memory.Base, replacement!, memory.Addend, memory.Scale, memory.AccessSize),
            FieldReference field when aliases.Contains(field.Local)
                => new FieldReference(field.Field, replacement!, field.Offset, field.Containers, field.AccessSize),
            AddressOf { Target: LocalVariable target } when aliases.Contains(target)
                => new AddressOf(replacement!),
            _ => null,
        };

    private static void InsertBeforeTerminator(Block block, Instruction instruction)
    {
        var index = block.Instructions.Count;
        if (index > 0 && block.Instructions[^1].OpCode is OpCode.Jump or OpCode.ConditionalJump or OpCode.Return or OpCode.Throw)
            index--;
        block.Instructions.Insert(index, instruction);
    }

    // Bailing here is fine, it just leaves the (already resolved) call with dead lookup around it
    private static void TryExciseLookup(ISILControlFlowGraph cfg, Match match, Dictionary<LocalVariable, Instruction> definitions, Dictionary<Instruction, Block> homeBlock)
    {
        var merge = match.Merge;

        if (!homeBlock.TryGetValue(match.SlowCall, out var slowBlock) || !cfg.Blocks.Contains(slowBlock))
            return;

        if (Definition(definitions, match.KlassLocal) is not { } klassDefinition
            || !homeBlock.TryGetValue(klassDefinition, out var head) || head == merge)
            return;

        if (!TryCollectRegion(cfg, head, merge, out var region) || !region.Contains(slowBlock)
            || !RegionIsSideEffectFree(region, match.SlowCall) || AnyValueEscapes(cfg, region, merge)
            || !MergePhisAreDead(cfg, merge, head, region, out var removable, out var patches))
            return;

        foreach (var (instruction, operandIndex, incoming) in patches)
            instruction.SetOperand(operandIndex, incoming);

        foreach (var instruction in removable)
        {
            instruction.OpCode = OpCode.Nop;
            instruction.SetOperands();
        }

        foreach (var successor in head.Successors)
            successor.Predecessors.Remove(head);
        head.Successors.Clear();
        head.Successors.Add(merge);

        var terminator = head.Instructions[^1];
        if (terminator.OpCode is OpCode.Jump or OpCode.ConditionalJump)
        {
            terminator.OpCode = OpCode.Jump;
            terminator.SetOperands(merge);
        }
        else
            head.AddInstruction(new Instruction(-1, OpCode.Jump, merge));

        head.CalculateBlockType();

        merge.Predecessors.RemoveAll(region.Contains);
        merge.Predecessors.Add(head);

        foreach (var block in region)
        {
            foreach (var successor in block.Successors)
                successor.Predecessors.Remove(block);
            foreach (var predecessor in block.Predecessors)
                predecessor.Successors.Remove(block);

            block.Successors.Clear();
            block.Predecessors.Clear();
            cfg.Blocks.Remove(block);
        }
    }

    // The region has to be closed, so nothing else may enter or leave it
    private static bool TryCollectRegion(ISILControlFlowGraph cfg, Block head, Block merge, out HashSet<Block> region)
    {
        region = [];

        var queue = new Queue<Block>(merge.Predecessors);

        while (queue.Count > 0)
        {
            var block = queue.Dequeue();

            if (block == head)
                continue;

            if (block == merge || block == cfg.EntryBlock || block == cfg.ExitBlock || region.Count > 64)
                return false;

            if (!region.Add(block))
                continue;

            foreach (var predecessor in block.Predecessors)
                queue.Enqueue(predecessor);
        }

        if (region.Count == 0)
            return false;

        var collected = region;
        foreach (var block in collected)
        {
            if (block.Predecessors.Any(p => p != head && !collected.Contains(p)))
                return false;
            if (block.Successors.Any(s => s != merge && !collected.Contains(s)))
                return false;
        }

        // we rewrite the head's terminator, so it can't branch anywhere else
        return head.Successors.All(s => s == merge || collected.Contains(s));
    }

    private static bool RegionIsSideEffectFree(HashSet<Block> region, Instruction slowCall)
    {
        foreach (var block in region)
        {
            foreach (var instruction in block.Instructions)
            {
                if (ReferenceEquals(instruction, slowCall))
                    continue;

                var harmless = instruction.OpCode switch
                {
                    OpCode.Nop or OpCode.Jump or OpCode.ConditionalJump or OpCode.Phi => true,
                    OpCode.Move or OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Modulo
                        or OpCode.ShiftLeft or OpCode.ShiftRight or OpCode.And or OpCode.Or or OpCode.Xor
                        or OpCode.Not or OpCode.Negate or OpCode.SignExtend32 or OpCode.Convert
                        or (>= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual)
                        => instruction.Destination is LocalVariable,
                    _ => false,
                };

                if (!harmless)
                    return false;
            }
        }

        return true;
    }

    // Merge phis are exempt, their deadness gets checked separately
    private static bool AnyValueEscapes(ISILControlFlowGraph cfg, HashSet<Block> region, Block merge)
    {
        var regionDefs = new HashSet<LocalVariable>();
        foreach (var block in region)
            foreach (var instruction in block.Instructions)
                if (instruction.Destination is LocalVariable destination)
                    regionDefs.Add(destination);

        foreach (var block in cfg.Blocks)
        {
            if (region.Contains(block))
                continue;

            foreach (var instruction in block.Instructions)
            {
                if (instruction.OpCode == OpCode.Phi && block == merge)
                    continue;

                if (Uses(instruction, regionDefs))
                    return true;
            }
        }

        return false;
    }

    // They may only feed loads off the VirtualInvokeData pointer. Those loads' results, and any
    // other uses of a merge phi (arguments of later calls, phis in later blocks for loop-only
    // temporaries such as the interface-scan scratch registers), read plain register values: once
    // the lookup is excised the head is the merge's only predecessor, so the register version
    // reaching the head is exactly what downstream code observes. Uses are redirected to it; only a
    // use we cannot redirect keeps the lookup alive.
    private static bool MergePhisAreDead(ISILControlFlowGraph cfg, Block merge, Block head,
        HashSet<Block> region,
        out List<Instruction> removable,
        out List<(Instruction Instruction, int OperandIndex, IOperand Replacement)> patches)
    {
        removable = [];
        patches = [];

        var useSites = new Dictionary<LocalVariable, List<Instruction>>();
        foreach (var block in cfg.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                foreach (var used in UsedLocals(instruction))
                {
                    if (!useSites.TryGetValue(used, out var sites))
                        useSites[used] = sites = [];
                    sites.Add(instruction);
                }
            }
        }

        var reaching = new Dictionary<string, LocalVariable?>();

        foreach (var phi in merge.Instructions)
        {
            if (phi.OpCode != OpCode.Phi)
                continue;

            if (phi.Operands[0] is not LocalVariable phiDest)
            {
                return false;
            }

            foreach (var use in useSites.TryGetValue(phiDest, out var phiUses) ? phiUses : [])
            {
                // Loads off the merged pointer read memory the lookup produced. A dead result is
                // simply removed; a live result becomes a copy of the version reaching the head,
                // which is what the register holds once the lookup is gone.
                if (use is { OpCode: OpCode.Move, Operands: [LocalVariable loaded, MemoryOperand] })
                {
                    if (useSites.TryGetValue(loaded, out var loadUses) && loadUses.Count > 0)
                    {
                        if (Reaching(loaded.Register.Name) is not { } loadedIncoming)
                        {
                            return false;
                        }

                        patches.Add((use, 1, loadedIncoming));
                    }
                    else if (!removable.Contains(use))
                        removable.Add(use);
                    continue;
                }

                if (Reaching(phiDest.Register.Name) is not { } incoming)
                {
                    return false;
                }

                var patched = false;
                for (var i = 0; i < use.Operands.Count; i++)
                    if (OperandPatch(use.Operands[i], phiDest, incoming) is { } replacement)
                    {
                        patches.Add((use, i, replacement));
                        patched = true;
                    }

                if (!patched)
                    return false;
            }

            removable.Add(phi);
        }

        return true;

        LocalVariable? Reaching(string registerName)
        {
            if (!reaching.TryGetValue(registerName, out var value))
                reaching[registerName] = value = ReachingRegisterValue(registerName, head, region, merge);
            return value;
        }
    }

    // The operand replacement if the slot references `from`, else null. Deferred: patching must not
    // mutate operands while the use-site map for this merge is being walked.
    private static IOperand? OperandPatch(IOperand operand, LocalVariable from, IOperand to)
    {
        switch (operand)
        {
            case LocalVariable local when ReferenceEquals(local, from):
                return to;
            case MemoryOperand memory:
                var hit = false;
                if (ReferenceEquals(memory.Base, from))
                {
                    memory.Base = to;
                    hit = true;
                }
                if (ReferenceEquals(memory.Index, from))
                {
                    memory.Index = to;
                    hit = true;
                }
                return hit ? memory : null;
            case AddressOf addressOf when ReferenceEquals(addressOf.Target, from):
                return new AddressOf(to);
            default:
                return null;
        }
    }

    // The register version reaching the end of head: the last definition inside head, or the unique
    // version reaching it along every predecessor path (guaranteed consistent in SSA, otherwise head
    // itself would carry a phi for the register).
    private static LocalVariable? ReachingRegisterValue(string registerName, Block head,
        HashSet<Block> region, Block merge)
    {
        for (var i = head.Instructions.Count - 1; i >= 0; i--)
            if (head.Instructions[i].Destination is LocalVariable headLocal
                && headLocal.Register.Name == registerName)
                return headLocal;

        LocalVariable? found = null;
        var visited = new HashSet<Block>();
        var pending = new Stack<Block>(head.Predecessors);

        while (pending.Count > 0)
        {
            var block = pending.Pop();
            if (!visited.Add(block) || visited.Count > 4096)
                return null;

            if (block == merge || region.Contains(block))
                continue; // these defs cannot contribute to the value entering the region

            LocalVariable? candidate = null;
            for (var i = block.Instructions.Count - 1; i >= 0; i--)
                if (block.Instructions[i].Destination is LocalVariable blockLocal
                    && blockLocal.Register.Name == registerName)
                {
                    candidate = blockLocal;
                    break;
                }

            if (candidate == null)
            {
                if (block.Predecessors.Count == 0)
                    return null; // register is never defined on this path
                foreach (var predecessor in block.Predecessors)
                    pending.Push(predecessor);
                continue;
            }

            if (found == null)
                found = candidate;
            else if (found != candidate)
                return null; // disagreeing paths would have phied at head; treat as unresolvable
        }

        return found;
    }

    private static bool Uses(Instruction instruction, HashSet<LocalVariable> candidates)
        => UsedLocals(instruction).Any(candidates.Contains);

    private static IEnumerable<LocalVariable> UsedLocals(Instruction instruction)
    {
        for (var i = 0; i < instruction.Operands.Count; i++)
        {
            if (ReferenceEquals(instruction.Operands[i], instruction.Destination))
                continue;

            switch (instruction.Operands[i])
            {
                case LocalVariable local:
                    yield return local;
                    break;
                case AddressOf { Target: LocalVariable addressed }:
                    yield return addressed;
                    break;
                case MemoryOperand memory:
                    if (memory.Base is LocalVariable baseLocal)
                        yield return baseLocal;
                    if (memory.Index is LocalVariable indexLocal)
                        yield return indexLocal;
                    break;
            }
        }
    }
}
