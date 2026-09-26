using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

//Recovers terminal IndirectJump (br reg) instructions whose target provably loads a managed
//method's entry point, rewriting them to a managed call followed by Return.
//
//Two proven shapes (all operands are SSA locals by the time this runs):
//  - [mi + 0 | mi + pointerSize]  - MethodInfo::methodPointer / virtualMethodPointer of a
//    methodof(...)-typed pointer - the only source of such a load is a call to that method.
//  - [klass + vtableOffset + slot * sizeof(VirtualInvokeData)] - the vtable entry of a receiver
//    whose klass pointer is typed Il2CppClass<T>; recovered as a virtual dispatch of T's slot.
//
//Anything else (computed addresses, helper-returned pointers, raw function-pointer fields,
//jump tables) keeps its unresolved-indirect diagnostic.
public static class TailCallRecovery
{
    private const long VTableOffset64 = 0x138;
    private const long VTableOffset32 = 0xC0;

    public static void Run(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var (definitions, _) = InterfaceDispatchRecovery.BuildMaps(cfg);

        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var vtableOffset = pointerSize == 8 ? VTableOffset64 : VTableOffset32;
        var invokeDataSize = 2L * pointerSize;

        var changed = false;
        foreach (var block in cfg.Blocks)
        {
            if (block.Instructions is not [.., { OpCode: OpCode.IndirectJump } jump])
                continue;

            if (LoadsOf(jump.Operands[0], definitions) is not { } loads
                || loads.Count == 0
                || loads.Any(l => l.Base == null))
                continue;

            var addend = loads[0].Addend;
            if (loads.Any(l => l.Addend != addend))
                continue;

            MethodAnalysisContext? resolved;
            var isVirtualDispatch = false;
            List<IOperand>? klassOperands = null;

            // MethodInfo* base: every phi source must name the same method.
            var representedMethods = loads
                .Select(l => ResolveMethodInfo(l.Base!, definitions)?.RepresentedMethod)
                .ToList();
            var first = representedMethods.FirstOrDefault(m => m != null);

            if ((addend == 0 || addend == pointerSize)
                && first != null
                && representedMethods.All(m => m != null && SameMethodIdentity(m, first)))
            {
                // [MethodInfo* + methodPointerOffset] - a direct tail call to the represented method.
                // The hidden argument slot carries the same MethodInfo; when it survives typing it
                // corroborates the frame, but methodPointer loads only exist to call the method.
                resolved = first!;
            }
            else
            {
                // Il2CppClass<T> base at a vtable slot: every phi source must refer to the same
                // declared type and the addend must be a valid slot index.
                var receiverTypes = loads
                    .Select(l => RepresentedTypeOf(l.Base!, definitions))
                    .ToList();
                var firstType = receiverTypes.FirstOrDefault(t => t != null);
                var typeMatches = receiverTypes.Count == loads.Count
                    && receiverTypes.All(t => t != null
                        && ReferenceEquals(
                            (t as GenericInstanceTypeAnalysisContext)?.GenericType.Definition ?? t.Definition,
                            (firstType as GenericInstanceTypeAnalysisContext)?.GenericType.Definition ?? firstType!.Definition));

                if (typeMatches
                    && addend >= vtableOffset
                    && (addend - vtableOffset) % invokeDataSize == 0
                    && ResolveVTableSlot(method.AppContext, firstType!, (int)((addend - vtableOffset) / invokeDataSize)) is { IsStatic: false } slotMethod)
                {
                    // [Il2CppClass<T>* + vtableOffset + slot * 16] - virtual dispatch of T's slot.
                    resolved = slotMethod;
                    isVirtualDispatch = true;
                    klassOperands = loads.Select(l => l.Base!).ToList();
                }
                else
                    continue;
            }

            // Return compatibility: a void caller may tail-jump a non-void callee - CallVoid
            // on a non-void target lowers to call+pop, the discarded result. A non-void
            // caller needs a callee return assignable to its own (covariance is legal in CIL).
            if (!method.IsVoid
                && (resolved.IsVoid || !resolved.ReturnType.IsAssignableTo(method.ReturnType)))
                continue;

            if (resolved.AppContext.InstructionSet.CallingConventionResolver is not { } callingConventions
                || !callingConventions.HasRawArgumentLayout(jump, method.AppContext))
                continue;

            RewriteAsCall(method, jump, block, resolved, callingConventions, isVirtualDispatch);

            if (klassOperands != null)
                foreach (var klassOperand in klassOperands)
                    NameMethodInfoArgument(jump, klassOperand, addend, pointerSize, resolved, method, definitions);

            changed = true;
        }

        if (changed)
            DeadCodeEliminator.Run(method);
    }

    // The load(s) producing the call target: still a separate load, folded into the jump, or
    // phi'd across blocks - in which case every phi source must resolve to the same proof
    // (checked by the caller). Returns null for anything not exclusively made of loads.
    private static List<MemoryOperand>? LoadsOf(IOperand operand, Dictionary<LocalVariable, Instruction> definitions)
        => LoadsOf(operand, definitions, []);

    private static List<MemoryOperand>? LoadsOf(IOperand operand, Dictionary<LocalVariable, Instruction> definitions,
        HashSet<LocalVariable> visited)
        => operand switch
        {
            MemoryOperand { Index: null, Scale: 0 } inlined => [inlined],
            LocalVariable local when visited.Add(local) => InterfaceDispatchRecovery.ChaseCopies(definitions, local) switch
            {
                { OpCode: OpCode.Move, Operands: [_, MemoryOperand { Index: null, Scale: 0 } loaded] } => [loaded],
                { OpCode: OpCode.Phi } phi => CombinePhiSources(phi, definitions, visited),
                _ => null,
            },
            _ => null,
        };

    private static List<MemoryOperand>? CombinePhiSources(Instruction phi, Dictionary<LocalVariable, Instruction> definitions,
        HashSet<LocalVariable> visited)
    {
        var loads = new List<MemoryOperand>();
        foreach (var source in phi.Operands.Skip(1))
        {
            if (source is not LocalVariable sourceLocal || LoadsOf(sourceLocal, definitions, visited) is not { } sourceLoads)
                return null;
            loads.AddRange(sourceLoads);
        }
        return loads.Count == 0 ? null : loads;
    }

    // The represented method of a MethodInfo* operand: a methodof constant, or a local defined
    // by one (its synthetic Il2CppMethodInfo type carries the same proof).
    private static RuntimeMethodInfoAnalysisContext? ResolveMethodInfo(IOperand operand,
        Dictionary<LocalVariable, Instruction> definitions)
        => operand switch
        {
            RuntimeMethodInfoAnalysisContext info => info,
            LocalVariable local when InterfaceDispatchRecovery.ChaseCopies(definitions, local) is
                { OpCode: OpCode.Move, Operands: [_, RuntimeMethodInfoAnalysisContext loaded] } => loaded,
            LocalVariable { Type: RuntimeMethodInfoAnalysisContext typed } => typed,
            _ => null,
        };

    // The type a klass pointer refers to: a RuntimeClassTypeAnalysisContext operand, or a local
    // (through plain copies) holding one.
    private static TypeAnalysisContext? RepresentedTypeOf(IOperand operand,
        Dictionary<LocalVariable, Instruction> definitions)
        => operand switch
        {
            RuntimeClassTypeAnalysisContext { RepresentedType: { } represented } => represented,
            LocalVariable local => ChaseLocalCopies(local, definitions).Type switch
            {
                RuntimeClassTypeAnalysisContext { RepresentedType: { } represented } => represented,
                _ => null,
            },
            _ => null,
        };

    private static LocalVariable ChaseLocalCopies(LocalVariable local,
        Dictionary<LocalVariable, Instruction> definitions)
    {
        var visited = new HashSet<LocalVariable>();
        while (visited.Add(local)
               && definitions.TryGetValue(local, out var definition)
               && definition is { OpCode: OpCode.Move, Operands: [_, LocalVariable source] })
            local = source;
        return local;
    }

    private static bool SameMethodIdentity(MethodAnalysisContext left, MethodAnalysisContext right)
        => ReferenceEquals(MethodIdentity(left), MethodIdentity(right));

    private static object MethodIdentity(MethodAnalysisContext method) =>
        (object?)((method as ConcreteGenericMethodAnalysisContext)?.BaseMethodContext ?? method).Definition ?? method;

    private static MethodAnalysisContext? ResolveVTableSlot(ApplicationAnalysisContext appContext,
        TypeAnalysisContext type, int slot)
    {
        var definition = (type as GenericInstanceTypeAnalysisContext)?.GenericType.Definition ?? type.Definition;

        if (definition == null || slot >= definition.VtableCount)
            return null;

        if (appContext.ResolveContextForMethod(definition.VTable[slot]) is { } implementation)
            return implementation;

        // An abstract slot has no implementation in VTable - resolve the declaration itself.
        for (var declarer = type; declarer != null; declarer = declarer.BaseType)
            if (declarer.Methods.FirstOrDefault(m => m.Definition?.slot == slot) is { } declaration)
                return declaration;

        return null;
    }

    private static void RewriteAsCall(MethodAnalysisContext method, Instruction jump, Block block,
        MethodAnalysisContext resolved, BaseCallingConventionResolver callingConventions, bool isVirtualDispatch)
    {
        // A void caller discards a non-void callee's result (CallVoid lowers to call+pop),
        // so the call only yields a result operand when both sides are non-void.
        var yieldsResult = !method.IsVoid && !resolved.IsVoid;
        var operands = new List<IOperand> { resolved };
        if (yieldsResult)
            operands.Add(new LocalVariable("tailCallResult", callingConventions.ReturnRegister(resolved), resolved.ReturnType));
        operands.AddRange(jump.Operands.Skip(2));
        jump.SetOperands(operands);
        jump.OpCode = yieldsResult ? OpCode.Call : OpCode.CallVoid;
        jump.IsVirtualDispatch = isVirtualDispatch;
        callingConventions.RemapRawArguments(jump, resolved);

        block.AddInstruction(new Instruction(-1, OpCode.Return,
            yieldsResult ? [jump.Operands[1]] : []));
        block.CalculateBlockType();
    }

    // The hidden argument is the MethodInfo loaded at [klass + slotOffset + pointerSize];
    // rewrite it to the resolved methodof for cleanliness.
    private static void NameMethodInfoArgument(Instruction jump, IOperand klassOperand, long targetAddend,
        int pointerSize, MethodAnalysisContext resolved, MethodAnalysisContext method,
        Dictionary<LocalVariable, Instruction> definitions)
    {
        var assembly = resolved.DeclaringType?.DeclaringAssembly ?? method.DeclaringType?.DeclaringAssembly;
        if (assembly == null)
            return;

        for (var i = 1; i < jump.Operands.Count; i++)
        {
            if (LoadsOf(jump.Operands[i], definitions) is { } methodInfoLoads
                && methodInfoLoads.Any(methodInfoLoad =>
                    methodInfoLoad.Base is { } loadBase
                    && ReferenceEquals(loadBase, klassOperand)
                    && methodInfoLoad.Addend == targetAddend + pointerSize))
                jump.SetOperand(i, new RuntimeMethodInfoAnalysisContext(resolved, assembly));
        }
    }
}
