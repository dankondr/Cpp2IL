using System;
using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Maps calls to KeyFunctionAddresses to their underlying IL opcodes. E.g. il2cpp_codegen_object_new => newobj.
/// Eventually will include box/unbox/throw/etc
/// </summary>
public static class KeyFunctionRecovery
{
    //All of these have the same params in the same order so we treat them as equal.
    private static readonly HashSet<string> ObjectNewFunctions =
    [
        "il2cpp_object_new",
        "il2cpp_vm_object_new",
        "il2cpp_codegen_object_new",
    ];

    //These all take the exception to throw as their only real argument.
    private static readonly HashSet<string> RaiseExceptionFunctions =
    [
        nameof(BaseKeyFunctionAddresses.il2cpp_raise_exception),
        nameof(BaseKeyFunctionAddresses.il2cpp_vm_exception_raise),
        nameof(BaseKeyFunctionAddresses.il2cpp_codegen_raise_exception),
    ];

    //Both take the class to box as and a pointer to the value.
    private static readonly HashSet<string> BoxFunctions =
    [
        nameof(BaseKeyFunctionAddresses.il2cpp_value_box),
        nameof(BaseKeyFunctionAddresses.il2cpp_vm_object_box),
    ];

    //void* Object::Unbox(Il2CppObject* obj) - the leaf reads only the boxed object and
    //returns a pointer to the value data. The generated wrapper loads the expected class
    //for its element_class check, so the register holding the class operand is real
    //evidence only some of the time.
    private static readonly HashSet<string> UnboxFunctions =
    [
        nameof(BaseKeyFunctionAddresses.il2cpp_object_unbox),
        nameof(BaseKeyFunctionAddresses.il2cpp_vm_object_unbox),
    ];

    public static void Run(MethodAnalysisContext method)
    {
        RewriteElementClassLoads(method);
        RewriteInlinedClassIsInst(method);

        foreach (var instruction in method.ControlFlowGraph!.Blocks.SelectMany(block => block.Instructions))
        {
            if (instruction.Operands is not [StringLiteral { Value: var keyFunction }, ..])
                continue;

            if (ObjectNewFunctions.Contains(keyFunction))
                RewriteObjectNew(instruction);
            else if (keyFunction == "__cxa_throw")
                RewriteNativeExceptionThrow(method, instruction);
            else if (keyFunction == "__cxa_end_catch")
            {
                instruction.OpCode = OpCode.Nop;
                instruction.SetOperands();
            }
            else if (keyFunction == nameof(BaseKeyFunctionAddresses.il2cpp_codegen_write_barrier))
                RemoveWriteBarrier(instruction, method);
            else if (RaiseExceptionFunctions.Contains(keyFunction))
                RewriteRaiseException(instruction);
            else if (BoxFunctions.Contains(keyFunction))
                RewriteBox(instruction, method);
            else if (UnboxFunctions.Contains(keyFunction))
                RewriteUnbox(instruction, method);
            else if (keyFunction == nameof(BaseKeyFunctionAddresses.il2cpp_vm_object_is_inst))
                RewriteIsInst(instruction, method.ControlFlowGraph!, method.AppContext.Binary.is32Bit);
            else if (keyFunction == nameof(BaseKeyFunctionAddresses.il2cpp_vm_reflection_get_type_object))
                RewriteTypeObject(instruction);
            else if (keyFunction == nameof(BaseKeyFunctionAddresses.InternalCalls_Resolve))
                RewriteInternalCallResolve(instruction, method);
            else if (keyFunction == nameof(BaseKeyFunctionAddresses.il2cpp_codegen_get_thread_static_data))
                RewriteThreadStaticData(instruction, method);
        }
    }

    private static void RewriteInlinedClassIsInst(MethodAnalysisContext method)
    {
        if (method.AppContext.Binary.is32Bit)
            return;

        var cfg = method.ControlFlowGraph!;
        var index = new DefUseIndex(cfg);
        var home = cfg.Blocks.SelectMany(block => block.Instructions.Select(instruction => (instruction, block)))
            .ToDictionary(pair => pair.instruction, pair => pair.block);

        var metadataVersion = method.AppContext.MetadataVersion;

        foreach (var instruction in cfg.Instructions)
        {
            // depth(klass) >= depth(K) && hierarchy(klass)[depth(K) - 1] == K. The compiler emits
            // the last comparison as either `==` (result true means "is K") or `!=` (result true
            // means "is not K") - recognise the term, not the polarity.
            if (instruction is not { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual,
                    Operands: [var result, var left, var right] })
                continue;

            if (!TryMatch(instruction, left, right, out var value, out var target, out var runtimeClass, out var targetClass)
                && !TryMatch(instruction, right, left, out value, out target, out runtimeClass, out targetClass))
                continue;

            // When the not-an-instance edge throws InvalidCastException the check is a castclass:
            // the cast raises it itself, and the surviving edge is the pass edge.
            var castClass = FailingEdgeIsInvalidCastThrow(instruction, result,
                out var passingTarget);
            var resultIsInstance = instruction.OpCode == OpCode.CheckEqual;
            instruction.OpCode = resultIsInstance ? OpCode.CheckNotEqual : OpCode.CheckEqual;
            instruction.SetOperands(result, new ReferenceCast(value, target, nullOnFailure: !castClass),
                new Immediate(0));
            if (castClass && passingTarget != null)
                FoldFailingBranch(instruction, result, passingTarget);
            RemoveDepthPrecheck(instruction, runtimeClass, targetClass);
        }

        bool TryMatch(Instruction use, IOperand hierarchyEntry, IOperand targetOperand,
            out LocalVariable value, out TypeAnalysisContext target,
            out LocalVariable runtimeClass, out LocalVariable targetClass)
        {
            value = null!;
            target = null!;
            runtimeClass = targetClass = null!;
            if (hierarchyEntry is not MemoryOperand
                {
                    Base: LocalVariable address, Index: null, Scale: 0, Addend: -8
                }
                || index.ReachingDef(address, use) is not
                    { OpCode: OpCode.Add, Operands: [_, var addLeft, var addRight] } addressDefinition
                || !TrySplitHierarchyAdd(addLeft, addRight, out runtimeClass, out var shiftedDepth)
                || index.ReachingDef(shiftedDepth, addressDefinition) is not
                {
                    OpCode: OpCode.ShiftLeft,
                    Operands:
                    [_, MemoryOperand
                        {
                            Base: LocalVariable indexedClass, Index: null, Scale: 0
                        }, Immediate { Value: 3 }]
                } shiftDefinition
                || shiftDefinition.Operands[1] is not MemoryOperand depthLoad
                || !IsFieldRead(depthLoad, Il2CppClassUsefulOffsets.Il2CppClassField.TypeHierarchyDepth)
                || index.ReachingDef(runtimeClass, addressDefinition) is not
                {
                    OpCode: OpCode.Move,
                    Operands: [_, MemoryOperand
                        {
                            Base: LocalVariable instance, Index: null, Scale: 0, Addend: 0
                        }]
                })
                return false;

            var comparedTarget = IsInstTarget(ResolveMoveSource(cfg, targetOperand), cfg, false);
            var indexedTarget = IsInstTarget(ResolveMoveSource(cfg, indexedClass), cfg, false)
                ?? RuntimeClassTerms.RepresentedClass(indexedClass, index, use);
            if (comparedTarget == null || indexedTarget == null || comparedTarget.IsInterface
                || !SameType(comparedTarget, indexedTarget))
                return false;

            value = instance;
            target = comparedTarget;
            targetClass = indexedClass;
            return true;
        }

        // A plain cast check emits `castclass`: the branch that fires when the value is not an
        // instance goes straight to a Throw InvalidCastException. Find the conditional in the
        // check's block that consumes the result (through Not/Move/Check* projections), work out
        // which successor is the not-instance edge, and confirm it lands on the shared throw.
        bool FailingEdgeIsInvalidCastThrow(Instruction check, IOperand checkResult,
            out Block? passingTarget)
        {
            passingTarget = null;
            if (!home.TryGetValue(check, out var checkBlock)
                || checkBlock.Instructions[^1] is not
                    { OpCode: OpCode.ConditionalJump, Operands: [Block jumpTarget, var condition] }
                || checkBlock.Successors.Count != 2
                || BooleanParity(condition, checkResult, check) is not { } parity
                || checkBlock.Successors.FirstOrDefault(s => !ReferenceEquals(s, jumpTarget)) is not { } other)
                return false;

            // CheckEqual produced "is instance" so the not-instance edge jumps when condition is
            // !result; CheckNotEqual produced "is not instance", so it jumps when condition is
            // result. Parity counts the Not's between the result local and the branch condition.
            var jumpOnInstance = (check.OpCode == OpCode.CheckEqual) == (parity % 2 == 0);
            var failingEdge = jumpOnInstance ? other : jumpTarget;
            var passingEdge = jumpOnInstance ? jumpTarget : other;
            if (!ThrowTailIsInvalidCast(failingEdge))
                return false;

            passingTarget = passingEdge;
            return true;
        }

        // Fold the just-rewritten branch: castclass throws on failure, so the surviving edge is
        // always taken.
        void FoldFailingBranch(Instruction check, IOperand checkResult, Block passingTarget)
        {
            if (!home.TryGetValue(check, out var checkBlock)
                || checkBlock.Instructions[^1].OpCode != OpCode.ConditionalJump)
                return;

            var target = checkBlock.Successors.FirstOrDefault(s => !ReferenceEquals(s, passingTarget));
            if (target != null)
                target.Predecessors.Remove(checkBlock);
            checkBlock.Successors.Clear();
            checkBlock.Successors.Add(passingTarget);

            var terminator = checkBlock.Instructions[^1];
            terminator.OpCode = OpCode.Jump;
            terminator.SetOperands(passingTarget);
            checkBlock.CalculateBlockType();
        }

        // How many Not-equivalences sit between `value` and `source`: even means the branch tests
        // the result as-is, odd means it tests its negation. null when not a boolean projection.
        int? BooleanParity(IOperand value, IOperand source, Instruction use)
        {
            var parity = 0;
            var visited = new HashSet<LocalVariable>();
            while (true)
            {
                if (ReferenceEquals(value, source))
                    return parity;
                if (value is not LocalVariable local || !visited.Add(local)
                    || index.ReachingDef(local, use) is not { } definition)
                    return null;
                switch (definition)
                {
                    case { OpCode: OpCode.Move, Operands: [_, var input] }:
                        value = input;
                        break;
                    case { OpCode: OpCode.Not, Operands: [_, var input] }:
                        parity ^= 1;
                        value = input;
                        break;
                    case { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual,
                            Operands: [_, var input, Immediate { Value: 0 or 1 } compareTo] }:
                        var inverted = (definition.OpCode == OpCode.CheckEqual) == (compareTo.Value == 0);
                        if (inverted)
                            parity ^= 1;
                        value = input;
                        break;
                    default:
                        return null;
                }
            }
        }

        bool IsFieldRead(MemoryOperand load, Il2CppClassUsefulOffsets.Il2CppClassField expected) =>
            load.Addend is >= 0 and <= uint.MaxValue
            && Il2CppClassUsefulOffsets.TryGetField((uint)load.Addend, metadataVersion,
                method.AppContext.Binary.is32Bit, out var field, out _)
            && field == expected;

        bool ThrowTailIsInvalidCast(Block block, int depth = 0)
        {
            if (depth > 8)
                return false;
            var significant = block.Instructions.Where(i => i.OpCode != OpCode.Nop).ToList();
            if (significant is [{ OpCode: OpCode.Jump }] && block.Successors.Count == 1)
                return ThrowTailIsInvalidCast(block.Successors[0], depth + 1);
            return significant.LastOrDefault() is { OpCode: OpCode.Throw } thrown
                && thrown.Operands.Any(ThrowsInvalidCast);
        }

        bool ThrowsInvalidCast(IOperand operand)
        {
            operand = ResolveMoveSource(cfg, operand);
            return operand switch
            {
                TypeAnalysisContext type => type.FullName == "System.InvalidCastException",
                LocalVariable { Type: { } type } => type.FullName == "System.InvalidCastException",
                LocalVariable local => index.DefinitionsOf(local).Any(definition =>
                    definition is { OpCode: OpCode.Move, Operands: [_, TypeAnalysisContext t] }
                        && t.FullName == "System.InvalidCastException"
                    || definition is { OpCode: OpCode.Newobj, Operands: [_, TypeAnalysisContext { FullName: "System.InvalidCastException" }, ..] }),
                _ => false,
            };
        }

        void RemoveDepthPrecheck(Instruction hierarchyCheck, LocalVariable runtimeClass,
            LocalVariable targetClass)
        {
            if (!home.TryGetValue(hierarchyCheck, out var hierarchyBlock))
                return;

            foreach (var guardBlock in hierarchyBlock.Predecessors)
            {
                if (guardBlock.Successors.Count != 2
                    || guardBlock.Instructions.LastOrDefault() is not
                    {
                        OpCode: OpCode.ConditionalJump,
                        Operands: [_, LocalVariable branchCondition]
                    } branchJump)
                    continue;

                var depthCheck = guardBlock.Instructions.LastOrDefault(candidate => candidate is
                {
                    OpCode: OpCode.CheckLess,
                    Operands:
                    [LocalVariable,
                        MemoryOperand
                        {
                            Base: var runtimeDepthClass, Index: null, Scale: 0
                        } runtimeDepthLoad,
                        MemoryOperand
                        {
                            Base: var targetDepthClass, Index: null, Scale: 0
                        } targetDepthLoad]
                }
                && IsFieldRead(runtimeDepthLoad, Il2CppClassUsefulOffsets.Il2CppClassField.TypeHierarchyDepth)
                && IsFieldRead(targetDepthLoad, Il2CppClassUsefulOffsets.Il2CppClassField.TypeHierarchyDepth)
                && SameClassLocal(runtimeDepthClass, runtimeClass)
                && SameClassLocal(targetDepthClass, targetClass));
                if (depthCheck?.Destination is not LocalVariable depthCondition
                    || !IsBooleanProjection(branchCondition, depthCondition, branchJump, []))
                    continue;

                depthCheck.OpCode = OpCode.Move;
                depthCheck.SetOperands(depthCondition, new Immediate(0));
                return;
            }
        }

        // The class pointer used in the depth precheck and the hierarchy lookup may be loaded into
        // different locals (two `Move k, [instance]` defs of the same instance) - treat them as the
        // same term when both read [x + 0] of the same instance or carry the same Il2CppClass<K>.
        bool SameClassLocal(IOperand? left, IOperand? right)
        {
            if (ReferenceEquals(left, right))
                return true;
            if (left is not LocalVariable leftLocal || right is not LocalVariable rightLocal)
                return false;

            var leftClass = RuntimeClassTerms.RepresentedClass(leftLocal, index);
            var rightClass = RuntimeClassTerms.RepresentedClass(rightLocal, index);
            if (leftClass != null && rightClass != null)
                return RuntimeClassTerms.SameType(leftClass, rightClass);

            return index.DefinitionsOf(leftLocal) is [{ OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: LocalVariable leftBase, Addend: 0 }] }]
                && index.DefinitionsOf(rightLocal) is [{ OpCode: OpCode.Move, Operands: [_, MemoryOperand { Base: LocalVariable rightBase, Addend: 0 }] }]
                && ReferenceEquals(leftBase, rightBase);
        }

        bool IsBooleanProjection(LocalVariable value, LocalVariable source, Instruction use, HashSet<LocalVariable> visited)
        {
            if (ReferenceEquals(value, source))
                return true;
            if (!visited.Add(value) || index.ReachingDef(value, use) is not { } definition)
                return false;
            return definition switch
            {
                { OpCode: OpCode.Move or OpCode.Not, Operands: [_, LocalVariable input] }
                    => IsBooleanProjection(input, source, definition, visited),
                { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual,
                    Operands: [_, LocalVariable input, Immediate { Value: 0 or 1 }] }
                    => IsBooleanProjection(input, source, definition, visited),
                _ => false,
            };
        }

        static bool TrySplitHierarchyAdd(IOperand left, IOperand right,
            out LocalVariable runtimeClass, out LocalVariable shiftedDepth)
        {
            runtimeClass = shiftedDepth = null!;
            if (left is MemoryOperand
                {
                    Base: LocalVariable klass, Index: null, Scale: 0, Addend: 0xC8
                }
                && right is LocalVariable shift)
            {
                runtimeClass = klass;
                shiftedDepth = shift;
                return true;
            }
            if (right is MemoryOperand
                {
                    Base: LocalVariable otherKlass, Index: null, Scale: 0, Addend: 0xC8
                }
                && left is LocalVariable otherShift)
            {
                runtimeClass = otherKlass;
                shiftedDepth = otherShift;
                return true;
            }
            return false;
        }

        static bool SameType(TypeAnalysisContext left, TypeAnalysisContext right) =>
            ReferenceEquals(left, right)
            || left.FullName == right.FullName
            && ReferenceEquals(left.DeclaringAssembly, right.DeclaringAssembly);
    }

    private static void RewriteElementClassLoads(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction is not
                {
                    OpCode: OpCode.Move,
                    Operands:
                    [LocalVariable destination,
                        MemoryOperand
                        {
                            Base: LocalVariable
                            {
                                Type: RuntimeClassTypeAnalysisContext { RepresentedType: var represented }
                            } klassLocal,
                            Index: null,
                            Scale: 0,
                            Addend: >= 0 and <= uint.MaxValue and var offset
                        }]
                }
                || !Il2CppClassUsefulOffsets.IsElementTypePtr((uint)offset, method.AppContext.Binary.is32Bit))
                continue;

            var elementType = ProducerElementType(method.ControlFlowGraph!, klassLocal,
                    instruction.Index)
                ?? represented switch
                {
                    SzArrayTypeAnalysisContext or ArrayTypeAnalysisContext
                        => ((WrappedTypeAnalysisContext)represented).ElementType,
                    PointerTypeAnalysisContext pointer => pointer.ElementType,
                    GenericInstanceTypeAnalysisContext
                    {
                        GenericType.FullName: "System.Nullable`1",
                        GenericArguments: [{ } nullableElement]
                    } => nullableElement,
                    { IsEnumType: true, DefaultEnumUnderlyingType: { } underlying } => underlying,
                    _ => represented,
                };
            var elementClass = new RuntimeClassTypeAnalysisContext(elementType,
                elementType.DeclaringAssembly);
            instruction.SetOperand(1, elementClass);
            destination.Type = elementClass;
        }
    }

    private static void RewriteThreadStaticData(Instruction instruction, MethodAnalysisContext method)
    {
        if (instruction is not { OpCode: OpCode.Call,
                Operands: [_, LocalVariable storage, var ownerOperand, ..] })
            return;
        var owner = ResolveThreadStaticOwner(ownerOperand) ?? method.DeclaringType;
        var fields = owner.Fields.Where(field => field.IsStatic
            && field.HasCustomAttributeWithFullName("System.ThreadStaticAttribute")).ToList();
        if (fields.Count != 1)
            fields = owner.Fields.Where(field => field.IsStatic && field.Name == "local").ToList();
        if (fields.Count == 0)
            fields = owner.Fields.Where(field => field.IsStatic
                && (field.Attributes & System.Reflection.FieldAttributes.InitOnly) == 0).ToList();
        if (fields.Count != 1)
            return;

        var field = fields[0];
        storage.Type = new StaticFieldStorageTypeAnalysisContext(owner, owner.DeclaringAssembly);
        foreach (var use in method.ControlFlowGraph!.Instructions)
            for (var i = 0; i < use.Operands.Count; i++)
                if (use.Operands[i] is MemoryOperand { Base: LocalVariable baseLocal, Index: null, Scale: 0, Addend: 0 }
                    && ReferenceEquals(baseLocal, storage))
                    use.SetOperand(i, new FieldReference(field, storage, 0));

        instruction.OpCode = OpCode.Nop;
        instruction.SetOperands();
    }

    private static TypeAnalysisContext? ResolveThreadStaticOwner(IOperand? operand)
    {
        return operand switch
        {
            RuntimeClassTypeAnalysisContext runtimeClass => runtimeClass.RepresentedType,
            LocalVariable { Type: { } type } => ResolveThreadStaticOwner(type),
            MemoryOperand memory => ResolveThreadStaticOwner(memory.Base),
            WrappedTypeAnalysisContext wrapped => ResolveThreadStaticOwner(wrapped.ElementType),
            TypeAnalysisContext type => type,
            _ => null,
        };
    }

    private static void RemoveWriteBarrier(Instruction instruction, MethodAnalysisContext method)
    {
        // il2cpp_codegen_write_barrier(dst, obj) performs *dst = obj with GC bookkeeping - the
        // store is real, so keep it. Dropping it loses both the write and the type flow to any
        // later reader of the cell.
        var args = (instruction.OpCode switch
        {
            OpCode.Call => instruction.Operands.Skip(2),
            OpCode.CallVoid => instruction.Operands.Skip(1),
            _ => [],
        }).ToList();
        var definitions = method.ControlFlowGraph!.Instructions
            .Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!)
            .Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        if (args is [{ } dstOperand, { } valueOperand, ..]
            && WriteBarrierCell(dstOperand, definitions) is { } cell)
        {
            // The value arg is often a register copy of the stored object - writing the operand it
            // was copied from keeps the cell's type tied to the actual object, not the (often
            // erased) declared signature of the helper.
            instruction.OpCode = OpCode.Move;
            instruction.SetOperands(cell, WriteBarrierValue(valueOperand, definitions, []));
            return;
        }
        instruction.OpCode = OpCode.Nop;
        instruction.SetOperands();
    }

    private static IOperand WriteBarrierValue(IOperand operand,
        IReadOnlyDictionary<LocalVariable, Instruction> definitions, HashSet<LocalVariable> visiting)
        => operand switch
        {
            LocalVariable local when visiting.Add(local)
                && definitions.TryGetValue(local, out var def)
                && def is { OpCode: OpCode.Move, Operands: [_, { } source] }
                => WriteBarrierValue(source, definitions, visiting),
            _ => operand,
        };

    // The barrier's destination operand is the local holding the slot address - usually defined by
    // a `Move addr, &cell`. Resolve it (or a direct &cell) to the cell it writes.
    private static LocalVariable? WriteBarrierCell(IOperand dstOperand,
        IReadOnlyDictionary<LocalVariable, Instruction> definitions)
        => dstOperand switch
        {
            AddressOf { Target: LocalVariable cell } => cell,
            LocalVariable dst when definitions.TryGetValue(dst, out var def)
                && def is { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: LocalVariable cell }] }
                => cell,
            _ => null,
        };
    
    private static void RewriteRaiseException(Instruction instruction)
    {
        // A void call has no return value operand, so the exception is one slot earlier
        var exceptionIndex = instruction.OpCode == OpCode.CallVoid ? 1 : 2;

        if (!instruction.IsCall || instruction.Operands.Count <= exceptionIndex)
            return;

        var exception = instruction.Operands[exceptionIndex];

        instruction.OpCode = OpCode.Throw;
        instruction.SetOperands(exception);
    }

    internal static bool RewriteNativeExceptionThrow(MethodAnalysisContext method, Instruction throwInstruction,
        Func<IOperand, bool>? isExceptionWrapper = null)
    {
        var throwArgument = throwInstruction.OpCode == OpCode.CallVoid ? 1 : 2;
        if (!throwInstruction.IsCall
            || throwInstruction.Operands.Count <= throwArgument + 2
            || throwInstruction.Operands[throwArgument] is not LocalVariable allocation
            || throwInstruction.Operands[throwArgument + 1] is not { } typeInfo
            || throwInstruction.Operands[throwArgument + 2] is not Immediate { Value: 0 }
            || !(isExceptionWrapper ?? (operand => IsExceptionWrapperTypeInfo(method, operand)))(typeInfo))
            return false;

        Instruction? store = null;
        Instruction? allocate = null;
        IOperand? exception = null;
        foreach (var candidate in method.ControlFlowGraph!.Blocks
                     .SelectMany(block => block.Instructions)
                     .Where(instruction => instruction.Index < throwInstruction.Index
                                           && throwInstruction.Index - instruction.Index <= 64)
                     .OrderByDescending(instruction => instruction.Index))
        {
            if (store == null
                && candidate is { OpCode: OpCode.Move, Operands: [var destination, var source] }
                && IsAllocationCell(destination, allocation))
            {
                store = candidate;
                exception = source;
                continue;
            }
            if (store != null
                && candidate is { OpCode: OpCode.Call,
                    Operands: [StringLiteral { Value: "__cxa_allocate_exception" }, LocalVariable result,
                        Immediate { Value: var size }, ..] }
                && ReferenceEquals(result, allocation)
                && size == (method.AppContext.Binary.is32Bit ? 4 : 8))
            {
                allocate = candidate;
                break;
            }
        }

        if (allocate == null || store == null || exception == null
            || method.ControlFlowGraph.Instructions.Any(instruction =>
                instruction.Index >= allocate.Index && instruction.Index <= throwInstruction.Index
                && ReferencesOutsideWrapperPattern(instruction, allocation, allocate, store, throwInstruction, throwArgument)))
            return false;

        allocate.OpCode = OpCode.Nop;
        allocate.SetOperands();
        store.OpCode = OpCode.Nop;
        store.SetOperands();
        throwInstruction.OpCode = OpCode.Throw;
        throwInstruction.SetOperands(exception);
        return true;
    }

    private static bool IsAllocationCell(IOperand operand, LocalVariable allocation) => operand switch
    {
        MemoryOperand { Base: LocalVariable baseLocal, Index: null, Scale: 0, Addend: 0 }
            => ReferenceEquals(baseLocal, allocation),
        FieldReference { Local: var owner, Offset: 0 } => ReferenceEquals(owner, allocation),
        _ => false,
    };

    internal static bool IsExceptionWrapperTypeInfo(MethodAnalysisContext method, IOperand operand)
    {
        if (operand is not Immediate typeInfo)
            return false;

        var binary = method.AppContext.Binary;
        var namePointerAddress = typeInfo.UnsignedValue + (binary.is32Bit ? 4u : 8u);
        try
        {
            if (!binary.TryMapVirtualAddressToRaw(namePointerAddress, out _))
                return false;
            var nameAddress = binary.ReadPointerAtVirtualAddress(namePointerAddress);
            return ThrowHelperRecovery.ReadCStringAtVirtualAddress(method.AppContext, nameAddress, 64)
                is { } name && name.EndsWith("Il2CppExceptionWrapper", StringComparison.Ordinal);
        }
        catch
        {
            return false;
        }
    }

    private static bool ReferencesOutsideWrapperPattern(Instruction instruction, LocalVariable allocation,
        Instruction allocate, Instruction store, Instruction throwInstruction, int throwArgument)
    {
        for (var i = 0; i < instruction.Operands.Count; i++)
        {
            if (!References(instruction.Operands[i], allocation))
                continue;
            if (ReferenceEquals(instruction, allocate) && i == 1
                || ReferenceEquals(instruction, store) && i == 0
                || ReferenceEquals(instruction, throwInstruction) && i == throwArgument)
                continue;
            return true;
        }
        return false;

        static bool References(IOperand operand, LocalVariable target) => operand switch
        {
            LocalVariable local => ReferenceEquals(local, target),
            MemoryOperand memory => memory.Base != null && References(memory.Base, target)
                                    || memory.Index != null && References(memory.Index, target),
            FieldReference field => ReferenceEquals(field.Local, target),
            AddressOf address => References(address.Target, target),
            _ => false,
        };
    }

    internal static void RewriteBox(Instruction instruction, MethodAnalysisContext? method = null)
    {
        // function name, result, class, address of value.
        if (instruction.OpCode != OpCode.Call || instruction.Operands is not [_, var result, var classOperand, var value, ..])
            return;

        var boxedType = classOperand switch
        {
            RuntimeClassTypeAnalysisContext runtimeClass => runtimeClass.RepresentedType,
            TypeAnalysisContext type => type,
            _ => null,
        } ?? value switch
        {
            AddressOf { Target: LocalVariable { Type: { } type } } => type,
            LocalVariable { Type: ByRefTypeAnalysisContext { ElementType: { } type } } => type,
            _ => null,
        } ?? (method == null ? null : InferDefaultsBoxType(method, classOperand));
        if (boxedType == null)
            return;

        instruction.OpCode = OpCode.Box;
        instruction.SetOperands(result, boxedType, value);
    }

    internal static void RewriteUnbox(Instruction instruction, MethodAnalysisContext method)
    {
        // helper, result, boxed object, then the raw argument registers. The class
        // operand only sometimes holds the expected class - Object::Unbox never reads
        // it - so a slot that is a stale copy of the boxed object is ignored.
        // An unresolvable call is left untouched so a later recovery pass retries it
        // once more operand types are known; if none resolves it, emission keeps the
        // usual unknown-call diagnostic.
        if (instruction.OpCode != OpCode.Call
            || instruction.Operands is not [_, var result, var boxedObject, ..])
            return;

        var cfg = method.ControlFlowGraph!;
        var is32Bit = method.AppContext.Binary.is32Bit;
        var argumentType = instruction.Operands.Count > 3
                           && !ReferenceEquals(instruction.Operands[3], boxedObject)
            ? UnboxClassOperand(cfg, instruction.Operands[3], is32Bit)
            : null;
        var guardedTypes = GuardedUnboxTypes(method, instruction, boxedObject);
        var valueType = argumentType switch
        {
            // The class operand names a value type (or a method generic parameter,
            // which `unbox.any` handles at runtime) and no guard disagrees.
            { IsValueType: true } or GenericParameterTypeAnalysisContext
                when guardedTypes.All(guarded => SameFullName(guarded, argumentType))
                => argumentType,
            // The class operand was junk; the wrapper's element_class check is the only evidence.
            not ({ IsValueType: true } or GenericParameterTypeAnalysisContext)
                when guardedTypes.Count == 1 => guardedTypes[0],
            _ => null,
        };
        if (valueType == null)
            return;

        // unbox.any + ldloca lifts a *copy* of the boxed data, so a site that
        // writes through the pointer would silently write the copy, not the box.
        // Those uses keep the call unlifted - and keep its explicit diagnostic.
        if (UnboxResultIsWrittenThrough(cfg, result))
            return;

        instruction.OpCode = OpCode.Unbox;
        instruction.SetOperands(result, valueType, boxedObject);
        if (result is LocalVariable local)
            local.Type = new ByRefTypeAnalysisContext(valueType);
    }

    // Whether the pointer result is written through: a store into [result] or a
    // field off it (or off an SSA copy of it), or the pointer handed to a call as
    // `this` or a by-ref argument. An unresolved callee is skipped - that site is
    // already diagnosed on its own.
    private static bool UnboxResultIsWrittenThrough(Graphs.ISILControlFlowGraph cfg,
        IOperand result)
    {
        var aliases = new HashSet<IOperand> { result };
        var grew = true;
        while (grew)
        {
            grew = false;
            foreach (var i in cfg.Instructions)
            {
                if (i.OpCode == OpCode.Move
                    && i.Destination is LocalVariable copy
                    && !aliases.Contains(copy)
                    && aliases.Contains(i.Operands[1]))
                {
                    aliases.Add(copy);
                    grew = true;
                }
            }
        }

        foreach (var i in cfg.Instructions)
        {
            var writesThrough = i.Destination switch
            {
                MemoryOperand { Base: { } memoryBase } => aliases.Contains(memoryBase),
                MemoryOperand { Index: { } memoryIndex } => aliases.Contains(memoryIndex),
                FieldReference { Local: { } fieldOwner } => aliases.Contains(fieldOwner),
                _ => false,
            };
            if (writesThrough)
                return true;

            var firstArgument = i.OpCode switch
            {
                OpCode.Call => 2,
                OpCode.CallVoid => 1,
                _ => -1,
            };
            if (firstArgument < 0 || i.Operands[0] is not MethodAnalysisContext callee)
                continue;
            var receiverOffset = callee.IsStatic ? 0 : 1;
            for (var argument = firstArgument; argument < i.Operands.Count; argument++)
            {
                if (!aliases.Contains(i.Operands[argument]))
                    continue;
                if (receiverOffset == 1 && argument == firstArgument)
                    return true;
                var parameterIndex = argument - firstArgument - receiverOffset;
                if (parameterIndex >= 0
                    && parameterIndex < callee.Parameters.Count
                    && callee.Parameters[parameterIndex].ParameterType is ByRefTypeAnalysisContext)
                    return true;
            }
        }
        return false;
    }

    private static bool SameFullName(TypeAnalysisContext a, TypeAnalysisContext b)
        => a.FullName == b.FullName;

    // Resolves an operand denoting an Il2CppClass to the type it describes. Besides the
    // direct typeof forms this follows Move chains and the codegen's [klass + offset]
    // dereferences, where the pointer's source names the class.
    private static TypeAnalysisContext? UnboxClassOperand(Graphs.ISILControlFlowGraph cfg,
        IOperand operand, bool is32Bit, int depth = 0)
    {
        if (depth > 4)
            return null;
        // A local already typed Il2CppClass<T> (e.g. by element-class load rewriting)
        // names T even when its definition moves through unrelated memory.
        if (operand is LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: { } typed } })
            return typed;
        operand = ResolveMoveSource(cfg, operand);
        return operand switch
        {
            RuntimeClassTypeAnalysisContext { RepresentedType: { } type } => type,
            TypeAnalysisContext type => type,
            LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: { } type } } => type,
            MemoryOperand { IsConstant: false, Base: { } klassPointer }
                => UnboxClassOperand(cfg, klassPointer, is32Bit, depth + 1),
            _ => IsInstTarget(operand, cfg, is32Bit),
        };
    }

    // The inlined UnBox wrapper emits `obj->klass->element_class == expected->element_class`
    // before the helper call; the conditional jump it feeds still sits in a transitive
    // predecessor block, and its class operand names the expected value type.
    private static List<TypeAnalysisContext> GuardedUnboxTypes(MethodAnalysisContext method,
        Instruction call, IOperand boxedObject)
    {
        var cfg = method.ControlFlowGraph!;
        var is32Bit = method.AppContext.Binary.is32Bit;
        var home = cfg.Blocks
            .SelectMany(block => block.Instructions.Select(instruction => (instruction, block)))
            .ToDictionary(pair => pair.instruction, pair => pair.block);
        var definitions = cfg.Instructions
            .Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!)
            .Where(group => group.Count() == 1)
            .ToDictionary(group => group.Key, group => group.Single());
        // The call sees the boxed object through SSA register copies (`v71 = v9`,
        // `v9 = obj`), while a guard compares aliases that share the same root.
        var boxedAliases = new HashSet<IOperand>();
        var declaredType = boxedObject is LocalVariable { Type: { } type } ? type : null;
        var cursor = boxedObject;
        while (cursor is { }
               && boxedAliases.Add(cursor)
               && cursor is LocalVariable local
               && definitions.TryGetValue(local, out var move)
               && move is { OpCode: OpCode.Move, Operands: [_, var source] })
        {
            if (source is LocalVariable { Type: { } sourceType })
                declaredType = sourceType;
            cursor = source;
        }

        var candidates = new List<TypeAnalysisContext>();
        var visited = new HashSet<Graphs.Block>();
        var queue = new Queue<Graphs.Block>();
        if (home.TryGetValue(call, out var callBlock))
            foreach (var predecessor in callBlock.Predecessors)
                queue.Enqueue(predecessor);

        while (queue.TryDequeue(out var block))
        {
            if (!visited.Add(block))
                continue;
            foreach (var predecessor in block.Predecessors)
                queue.Enqueue(predecessor);

            foreach (var condition in block.Instructions
                         .Where(i => i.OpCode == OpCode.ConditionalJump)
                         .Select(i => i.Operands.ElementAtOrDefault(1))
                         .OfType<IOperand>())
            {
                if (CheckedComparison(condition, definitions) is not { Operands: [_, var left, var right] })
                    continue;
                var leftRefs = ReferencesBoxedObject(left, boxedAliases, declaredType, definitions, []);
                var rightRefs = ReferencesBoxedObject(right, boxedAliases, declaredType, definitions, []);
                var candidate =
                    leftRefs && !rightRefs
                        ? UnboxClassOperand(cfg, right, is32Bit)
                    : rightRefs && !leftRefs
                        ? UnboxClassOperand(cfg, left, is32Bit)
                        : null;
                if (candidate is { IsValueType: true } or GenericParameterTypeAnalysisContext)
                    candidates.Add(candidate);
            }
        }

        return candidates.DistinctBy(candidate => candidate.FullName).ToList();
    }

    // Traces a branch condition through moves, negations and `cond == 0/1` projections
    // back to the comparison that produced it.
    private static Instruction? CheckedComparison(IOperand operand,
        IReadOnlyDictionary<LocalVariable, Instruction> definitions)
    {
        var visited = new HashSet<LocalVariable>();
        while (operand is LocalVariable local && visited.Add(local)
               && definitions.TryGetValue(local, out var definition))
        {
            switch (definition)
            {
                case { OpCode: OpCode.Move or OpCode.Not, Operands: [_, var source] }:
                    operand = source;
                    continue;
                case { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual,
                       Operands: [_, LocalVariable inner, Immediate { Value: 0 or 1 }] }:
                    operand = inner;
                    continue;
                case { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual or OpCode.CheckLess
                           or OpCode.CheckLessOrEqual or OpCode.CheckGreater or OpCode.CheckGreaterOrEqual }:
                    return definition;
                default:
                    return null;
            }
        }
        return null;
    }

    // Whether an operand denotes the boxed object or a slot derived from it: the object
    // itself, [obj] / &obj dereferences, an `obj->klass` move chain, or the class the
    // object's declared type resolves to.
    private static bool ReferencesBoxedObject(IOperand operand, HashSet<IOperand> boxedAliases,
        TypeAnalysisContext? declaredType,
        IReadOnlyDictionary<LocalVariable, Instruction> definitions,
        HashSet<IOperand> visited)
    {
        if (!visited.Add(operand))
            return false;
        return boxedAliases.Contains(operand) || operand switch
        {
            LocalVariable local => definitions.TryGetValue(local, out var definition)
                && definition is { OpCode: OpCode.Move, Operands: [_, var source] }
                && ReferencesBoxedObject(source, boxedAliases, declaredType, definitions, visited),
            MemoryOperand memory =>
                memory.Base is { } baseOperand
                && ReferencesBoxedObject(baseOperand, boxedAliases, declaredType, definitions, visited)
                || memory.Index is { } index
                && ReferencesBoxedObject(index, boxedAliases, declaredType, definitions, visited),
            AddressOf address => ReferencesBoxedObject(address.Target, boxedAliases, declaredType,
                definitions, visited),
            FieldReference field => ReferencesBoxedObject(field.Local, boxedAliases, declaredType,
                definitions, visited),
            RuntimeClassTypeAnalysisContext { RepresentedType: { } represented } => declaredType != null
                && represented.FullName == declaredType.FullName,
            _ => false,
        };
    }

    internal static void RewriteIsInst(Instruction instruction, Graphs.ISILControlFlowGraph cfg, bool is32Bit)
    {
        // helper, result, object, target class. Object::IsInst returns null when
        // the object is not assignable; it does not have castclass semantics.
        if (instruction.OpCode != OpCode.Call
            || instruction.Operands is not [_, var result, LocalVariable value, var classOperand, ..])
            return;
        var resolved = ResolveMoveSource(cfg, classOperand);
        var target = IsInstTarget(resolved, cfg, is32Bit);
        if (target is null)
            return;
        instruction.OpCode = OpCode.Move;
        instruction.SetOperands(result, new ReferenceCast(value, target, nullOnFailure: true));
        // The cast produces the target type (or null): whatever the slot held from
        // register merging, the local now provably carries the cast result. Skip
        // value types and generic parameters: isinst yields a reference ('ref T'),
        // while a slot declared on the raw type expects the value form ('value T')
        // - typing it T would box/unbox the reference and fail verification.
        if (!target.IsValueType && target is not GenericParameterTypeAnalysisContext
            && result is LocalVariable resultLocal)
            resultLocal.Type = target;
    }

    private static TypeAnalysisContext? IsInstTarget(IOperand operand, Graphs.ISILControlFlowGraph cfg, bool is32Bit)
    {
        if (operand is MemoryOperand
            {
                Base: LocalVariable classPointer, Index: null, Scale: 0,
                Addend: >= 0 and <= uint.MaxValue and var elementOffset
            }
            && Il2CppClassUsefulOffsets.IsElementTypePtr((uint)elementOffset, is32Bit)
            && ResolveMoveSource(cfg, classPointer) is MemoryOperand
            {
                Base: LocalVariable
                {
                    Type: WrappedTypeAnalysisContext arrayType
                        and (SzArrayTypeAnalysisContext or ArrayTypeAnalysisContext)
                },
                Index: null, Scale: 0, Addend: 0
            })
            return arrayType.ElementType;

        return operand switch
        {
            RuntimeClassTypeAnalysisContext runtimeClass => runtimeClass.RepresentedType,
            TypeAnalysisContext type => type,
            LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: var type } } => type,
            MemoryOperand
            {
                Base: LocalVariable
                {
                    Type: RuntimeClassTypeAnalysisContext
                    {
                        RepresentedType: WrappedTypeAnalysisContext array
                            and (SzArrayTypeAnalysisContext or ArrayTypeAnalysisContext)
                    }
                },
                Index: null,
                Scale: 0,
                Addend: >= 0 and <= uint.MaxValue and var offset
            } when Il2CppClassUsefulOffsets.IsElementTypePtr((uint)offset, is32Bit) => array.ElementType,
            _ => null,
        };
    }

    private static readonly HashSet<string> ArrayNewFunctions =
    [
        "SzArrayNew",
        "il2cpp_vm_array_new_specific",
        "il2cpp_array_new_specific",
    ];

    // `[klass + elementOff]` reads Il2CppClass::element_class - the class a reference
    // array store checks its value against - which is meaningful only when the klass
    // local's represented type is an array/pointer klass. klass.Type is derived from
    // `instance.Type` at the `[instance + 0]` object-klass load, and that tag can be
    // polluted by register merging (e.g. a phi that merges the params-array register
    // with a callback copy carrying an unrelated type). Re-derive the element type
    // from the definition that produced the instance instead of trusting its tag.
    private static TypeAnalysisContext? ProducerElementType(Graphs.ISILControlFlowGraph cfg,
        LocalVariable klassLocal, int beforeIndex)
    {
        for (var depth = 0; depth < 4; depth++)
        {
            var definition = cfg.Instructions.LastOrDefault(i =>
                i.Index < beforeIndex
                && i.OpCode == OpCode.Move
                && i.Destination is LocalVariable candidate && candidate.Register == klassLocal.Register);
            if (definition?.Operands is not [_, var source])
                return null;
            switch (source)
            {
                case MemoryOperand { Base: LocalVariable instance, Index: null, Scale: 0, Addend: 0 }:
                    return ProducedManagedType(cfg, instance, definition.Index, 0) switch
                    {
                        WrappedTypeAnalysisContext wrapped => wrapped.ElementType,
                        _ => null,
                    };
                case LocalVariable copy when !ReferenceEquals(copy, klassLocal):
                    klassLocal = copy;
                    beforeIndex = definition.Index;
                    break;
                default:
                    return null;
            }
        }

        return null;
    }

    // The managed type the producing definition of `local` pins on it, when one is
    // provable: new-array allocations, array-allocating key functions, call results,
    // field loads and move/phi chains of those. Returns null when no definition
    // pins a type (parameters, opaque producers).
    private static TypeAnalysisContext? ProducedManagedType(Graphs.ISILControlFlowGraph cfg,
        LocalVariable local, int beforeIndex, int depth)
    {
        if (depth >= 4)
            return null;
        var definition = cfg.Instructions.LastOrDefault(i =>
            i.Index < beforeIndex
            && i.Destination is LocalVariable candidate && candidate.Register == local.Register);
        switch (definition)
        {
            case { OpCode: OpCode.Move, Operands: [_, LocalVariable source] }:
                return ProducedManagedType(cfg, source, definition.Index, depth + 1);
            case { OpCode: OpCode.Move, Operands: [_, FieldReference field] }:
                return field.Field.FieldType;
            case { OpCode: OpCode.NewArr, Operands: [_, TypeAnalysisContext arrayType, ..] }:
                return arrayType;
            case { OpCode: OpCode.Call, Operands: [_, _, var classArgument, ..] } arrayNew
                when arrayNew.Operands[0] is StringLiteral { Value: var callee }
                    && ArrayNewFunctions.Contains(callee):
                return classArgument switch
                {
                    LocalVariable
                    {
                        Type: RuntimeClassTypeAnalysisContext { RepresentedType: var representedArgument },
                    } => representedArgument,
                    RuntimeClassTypeAnalysisContext runtimeClass => runtimeClass.RepresentedType,
                    TypeAnalysisContext type => type,
                    _ => null,
                };
            case { OpCode: OpCode.Call, Operands: [MethodAnalysisContext callee, ..] }
                when !callee.IsVoid:
                return callee.ReturnType;
            case { OpCode: OpCode.Phi }:
                TypeAnalysisContext? merged = null;
                foreach (var input in definition.Operands.Skip(1))
                {
                    if (input is not LocalVariable source
                        || ProducedManagedType(cfg, source, definition.Index, depth + 1) is not { } produced)
                        return null;
                    if (merged == null)
                        merged = produced;
                    else if (merged.FullName != produced.FullName)
                        return null;
                }
                return merged;
            default:
                return null;
        }
    }

    private static TypeAnalysisContext? InferDefaultsBoxType(MethodAnalysisContext method, IOperand classOperand)
    {
        classOperand = ResolveMoveSource(method.ControlFlowGraph!, classOperand);
        if (!method.AppContext.UnityVersion.GreaterThanOrEquals(6000)
            || classOperand is not MemoryOperand
            {
                Base: LocalVariable defaults, Index: null, Addend: var offset
            }
            || !HasAbsoluteDefinition(method.ControlFlowGraph!, defaults))
            return null;

        return Unity6PrimitiveDefaultsClass(method.AppContext.SystemTypes, offset);
    }

    internal static IOperand ResolveMoveSource(Graphs.ISILControlFlowGraph cfg, IOperand operand)
    {
        for (var depth = 0; depth < 4 && operand is LocalVariable local; depth++)
        {
            var definition = cfg.Instructions.LastOrDefault(i =>
                i.OpCode == OpCode.Move
                && i.Destination is LocalVariable candidate
                && candidate.Register == local.Register);
            if (definition?.Operands is not [_, var source] || ReferenceEquals(source, operand))
                break;
            operand = source;
        }

        return operand;
    }

    internal static bool HasAbsoluteDefinition(Graphs.ISILControlFlowGraph cfg, LocalVariable local) =>
        cfg.Instructions.Any(i => i.OpCode == OpCode.Move
                                  && i.Destination is LocalVariable candidate
                                  && candidate.Register == local.Register
                                  && i.Operands is [_, MemoryOperand { IsConstant: true }]);

    // Unity 6 Il2CppDefaults starts with corlib and corlib_gen, followed by primitive class pointers.
    internal static TypeAnalysisContext? Unity6PrimitiveDefaultsClass(SystemTypesContext types, long offset) =>
        offset switch
        {
            0x18 => types.SystemByteType,
            0x20 => types.SystemVoidType,
            0x28 => types.SystemBooleanType,
            0x30 => types.SystemSByteType,
            0x38 => types.SystemInt16Type,
            0x40 => types.SystemUInt16Type,
            0x48 => types.SystemInt32Type,
            0x50 => types.SystemUInt32Type,
            0x58 => types.SystemIntPtrType,
            0x60 => types.SystemUIntPtrType,
            0x68 => types.SystemInt64Type,
            0x70 => types.SystemUInt64Type,
            0x78 => types.SystemSingleType,
            0x80 => types.SystemDoubleType,
            0x88 => types.SystemCharType,
            0x90 => types.SystemStringType,
            _ => null,
        };

    private static void RewriteTypeObject(Instruction instruction)
    {
        if (instruction.OpCode != OpCode.Call || instruction.Operands is not [_, var result, TypeAnalysisContext type, ..])
            return;

        instruction.OpCode = OpCode.Move;
        instruction.SetOperands(result, type);
    }

    private static void RewriteInternalCallResolve(Instruction instruction, MethodAnalysisContext method)
    {
        if (instruction.OpCode != OpCode.Call || instruction.Operands is not [_, var result, Immediate nameAddress, ..])
            return;

        if (ThrowHelperRecovery.ReadCStringAtVirtualAddress(method.AppContext, nameAddress.UnsignedValue, 256) is not { } name)
            return;

        if (ResolveInternalCallName(method.AppContext, name) is not { DeclaringType.DeclaringAssembly: { } assembly } resolved)
            return;

        // il2cpp_resolve_icall returns an Il2CppMethodPointer (the code entry), not a MethodInfo*.
        var pointer = new RuntimeMethodInfoAnalysisContext(resolved, assembly) { IsCodePointer = true };

        instruction.OpCode = OpCode.Move;
        instruction.SetOperands(result, pointer);

        RewriteCachedPointerLoads(method, result, pointer);
    }

    private static void RewriteCachedPointerLoads(MethodAnalysisContext method, IOperand result, RuntimeMethodInfoAnalysisContext pointer)
    {
        var cache = method.ControlFlowGraph!.Instructions
            .Where(i => i is { OpCode: OpCode.Move, Operands: [MemoryOperand { IsConstant: true }, _] })
            .Where(i => ReferenceEquals(i.Operands[1], result))
            .Select(i => ((MemoryOperand)i.Operands[0]).Addend)
            .Distinct()
            .ToList();

        if (cache.Count != 1)
            return;

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable destination, MemoryOperand { IsConstant: true } load] }
                && load.Addend == cache[0])
                instruction.SetOperands(destination, pointer);
        }
    }

    internal static MethodAnalysisContext? ResolveInternalCallName(ApplicationAnalysisContext appContext, string name)
    {
        var separator = name.IndexOf("::", StringComparison.Ordinal);

        if (separator < 0)
            return null;

        var typeName = name[..separator];
        var signature = name[(separator + 2)..];
        var parenthesis = signature.IndexOf('(');
        var methodName = parenthesis < 0 ? signature : signature[..parenthesis];

        if (appContext.LibCpp2IlContext.ReflectionCache.GetTypeByFullName(typeName) is not { } typeDefinition
            || appContext.ResolveContextForType(typeDefinition) is not { } type)
            return null;

        var candidates = type.Methods.Where(m => m.Name == methodName).ToList();

        if (candidates.Count <= 1)
            return candidates.FirstOrDefault();

        // Overloaded, so fall back on the parameter list in the name
        var parameters = parenthesis < 0 ? "" : signature[(parenthesis + 1)..].TrimEnd(')');
        var count = parameters.Length == 0 ? 0 : parameters.Split(',').Length;

        var byParameterCount = candidates.Where(m => m.Parameters.Count == count).ToList();

        return byParameterCount.Count == 1 ? byParameterCount[0] : null;
    }

    private static void RewriteObjectNew(Instruction instruction)
    {
        // Needs the function name, the result, and the class argument.
        if (instruction.OpCode != OpCode.Call || instruction.Operands.Count < 3)
            return;

        var result = instruction.Operands[1];
        var klass = instruction.Operands[2];

        instruction.OpCode = OpCode.Newobj;
        instruction.SetOperands(result, klass);
    }
}
