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
    public static void Run(MethodAnalysisContext method)
    {
        // offsets below are the 64-bit Il2CppClass layout
        if (method.AppContext.Binary.PointerSizeBytes != 8)
            return;

        var cfg = method.ControlFlowGraph!;

        var (definitions, homeBlock) = BuildMaps(cfg);
        var changed = DistributePhiedConstructions(method, cfg, definitions, homeBlock);
        if (changed)
            (definitions, homeBlock) = BuildMaps(cfg);

        foreach (var block in cfg.Blocks.ToList())
        {
            foreach (var instruction in block.Instructions.ToList())
            {
                if (instruction.OpCode is not (OpCode.IndirectCall or OpCode.IndirectJump))
                    continue;

                if (MatchDispatch(method, instruction, definitions, homeBlock) is { } match)
                {
                    RewriteDispatch(method, instruction, block, match, definitions);
                    TryExciseLookup(cfg, match, definitions, homeBlock);
                    changed = true;
                    continue;
                }

                if (MatchVirtualDispatch(method, instruction, definitions, homeBlock) is { } virtualMatch)
                {
                    RewriteVirtualDispatch(method, instruction, block, virtualMatch, definitions);
                    changed = true;
                }
            }
        }

        if (changed)
            DeadCodeEliminator.Run(method);
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

    private record struct Match(
        MethodAnalysisContext Resolved,
        Instruction InvokeDataPhi,
        Block Merge,
        Instruction SlowCall,
        LocalVariable KlassLocal);

    private static Match? MatchDispatch(MethodAnalysisContext method, Instruction dispatch, Dictionary<LocalVariable, Instruction> definitions, Dictionary<Instruction, Block> homeBlock)
    {
        // the call target loads VirtualInvokeData::methodPtr, separately or folded in
        var targetLoad = dispatch.Operands[0] switch
        {
            MemoryOperand folded => folded,
            LocalVariable target when ChaseCopies(definitions, target) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand loaded] } => loaded,
            _ => default(MemoryOperand?)
        };

        if (targetLoad is not { Index: null, Scale: 0, Addend: 0, Base: LocalVariable invokeData })
            return null;

        if (ChaseCopies(definitions, invokeData) is not { OpCode: OpCode.Phi, Operands: [_, LocalVariable first, LocalVariable second] } phi)
            return null;

        var firstDefinition = ChaseCopies(definitions, first);
        var secondDefinition = ChaseCopies(definitions, second);

        var slowCall = firstDefinition is { OpCode: OpCode.Call } 
            ? firstDefinition
            : secondDefinition is { OpCode: OpCode.Call } ? secondDefinition : null;
        var vtableEntry = ReferenceEquals(slowCall, firstDefinition) ? secondDefinition : firstDefinition;

        // slow path is GetInterfaceInvokeDataFromVTableSlowPath(obj, interface, slot), never resolved
        if (slowCall is not { Operands: [Immediate, _, _, LocalVariable interfaceArg, LocalVariable slotArg, ..] })
            return null;

        if (ChaseCopies(definitions, interfaceArg) is not { OpCode: OpCode.Move, Operands: [_, TypeAnalysisContext declaringInterface] })
            return null;

        if (declaringInterface is RuntimeMethodInfoAnalysisContext
            || !(declaringInterface is GenericInstanceTypeAnalysisContext { GenericType.IsInterface: true } || declaringInterface.IsInterface))
            return null;

        if (ChaseCopies(definitions, slotArg) is not { OpCode: OpCode.Move, Operands: [_, Immediate slotImmediate] }
            || slotImmediate.Value is < 0 or > ushort.MaxValue)
            return null;

        var slot = (int)slotImmediate.Value;

        // fast path computes klass + vtableOffset + ((entryOffset + slot) << 4) (the +slot folds away for slot 0)
        if (MatchVTableEntryChain(definitions, vtableEntry, slot) is not { } klassLocal)
            return null;

        if (ResolveInterfaceSlot(declaringInterface, slot) is not { } resolved)
            return null;

        if (!homeBlock.TryGetValue(phi, out var merge))
            return null;

        return new Match(resolved, phi, merge, slowCall, klassLocal);
    }

    internal static LocalVariable? MatchVTableEntryChain(Dictionary<LocalVariable, Instruction> definitions, Instruction? vtableEntry, int slot)
    {
        // ARM64 emits (klass + (SXTW(entryOffset + slot) << 4)) + vtableOffset.
        // The existing x86 shape associates the same final additions the other way around.
        var trailingOffset = vtableEntry is { OpCode: OpCode.Add, Operands: [_, LocalVariable, Immediate { Value: VTableOffset }] };
        if (trailingOffset)
            vtableEntry = ChaseCopies(definitions, (LocalVariable)vtableEntry!.Operands[1]);

        if (vtableEntry is not { OpCode: OpCode.Add, Operands: [_, LocalVariable addLeft, LocalVariable addRight] })
            return null;

        var (klassCandidate, sum) = ChaseCopies(definitions, addRight) is { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: 0 }] }
            ? (addRight, addLeft)
            : (addLeft, addRight);

        if (ChaseCopies(definitions, klassCandidate) is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable }] })
            return null;

        var shifted = sum;
        if (!trailingOffset)
        {
            if (ChaseCopies(definitions, sum) is not { OpCode: OpCode.Add, Operands: [_, LocalVariable innerShift, Immediate { Value: VTableOffset }] })
                return null;
            shifted = innerShift;
        }

        if (ChaseCopies(definitions, shifted) is not { OpCode: OpCode.ShiftLeft, Operands: [_, LocalVariable index, Immediate { Value: InvokeDataShift }] })
            return null;

        var entryOffset = ChaseCopies(definitions, index);
        if (entryOffset is { OpCode: OpCode.SignExtend32, Operands: [_, LocalVariable unextended] })
            entryOffset = ChaseCopies(definitions, unextended);

        if (entryOffset is { OpCode: OpCode.Add, Operands: [_, LocalVariable beforeSlot, Immediate slotAddend] })
        {
            if (slotAddend.Value != slot)
                return null;

            entryOffset = ChaseCopies(definitions, beforeSlot);
        }
        else if (slot != 0)
            return null;

        if (entryOffset is not { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: not null }] })
            return null;

        return klassCandidate;
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
                || !ReferenceEquals(ChaseCopies(definitions, loadBase), match.InvokeDataPhi))
                continue;

            if (load.Addend == 8 && assembly != null)
                dispatch.SetOperand(i, new RuntimeMethodInfoAnalysisContext(resolved, assembly));
            else if (load.Addend == 0)
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

        if (!homeBlock.TryGetValue(match.SlowCall, out var slowBlock))
            return;

        if (Definition(definitions, match.KlassLocal) is not { } klassDefinition
            || !homeBlock.TryGetValue(klassDefinition, out var head) || head == merge)
            return;

        if (!TryCollectRegion(cfg, head, merge, out var region) || !region.Contains(slowBlock))
            return;

        if (!RegionIsSideEffectFree(region, match.SlowCall) || AnyValueEscapes(cfg, region, merge))
            return;

        if (!MergePhisAreDead(cfg, merge, out var removable))
            return;

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
                        or OpCode.Not or OpCode.Negate or OpCode.SignExtend32
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

    // They may only feed loads off the VirtualInvokeData pointer, which must themselves be dead
    private static bool MergePhisAreDead(ISILControlFlowGraph cfg, Block merge, out List<Instruction> removable)
    {
        removable = [];

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

        foreach (var phi in merge.Instructions)
        {
            if (phi.OpCode != OpCode.Phi)
                continue;

            if (phi.Operands[0] is not LocalVariable phiDest)
                return false;

            foreach (var use in useSites.TryGetValue(phiDest, out var phiUses) ? phiUses : [])
            {
                if (use is not { OpCode: OpCode.Move, Operands: [LocalVariable loaded, MemoryOperand] }
                    || (useSites.TryGetValue(loaded, out var loadUses) && loadUses.Count > 0))
                    return false;

                removable.Add(use);
            }

            removable.Add(phi);
        }

        return true;
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
