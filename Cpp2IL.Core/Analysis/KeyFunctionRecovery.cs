using System;
using System.Collections.Generic;
using System.Linq;
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

    public static void Run(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Blocks.SelectMany(block => block.Instructions))
        {
            if (instruction.Operands is not [StringLiteral { Value: var keyFunction }, ..])
                continue;

            if (ObjectNewFunctions.Contains(keyFunction))
                RewriteObjectNew(instruction);
            else if (keyFunction == nameof(BaseKeyFunctionAddresses.il2cpp_codegen_write_barrier))
                RemoveWriteBarrier(instruction, method);
            else if (RaiseExceptionFunctions.Contains(keyFunction))
                RewriteRaiseException(instruction);
            else if (BoxFunctions.Contains(keyFunction))
                RewriteBox(instruction, method);
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

    internal static void RewriteBox(Instruction instruction, MethodAnalysisContext? method = null)
    {
        // function name, result, class, address of value.
        if (instruction.OpCode != OpCode.Call || instruction.Operands is not [_, var result, var classOperand, var value, ..])
            return;

        var boxedType = classOperand as TypeAnalysisContext ?? value switch
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

    internal static void RewriteIsInst(Instruction instruction, Graphs.ISILControlFlowGraph cfg, bool is32Bit)
    {
        // helper, result, object, target class. The surrounding native code
        // already performs the null test and throws where castclass semantics
        // are required, so a managed reference cast preserves the observable path.
        if (instruction.OpCode != OpCode.Call
            || instruction.Operands is not [_, var result, LocalVariable value, var classOperand, ..]
            || IsInstTarget(ResolveMoveSource(cfg, classOperand), cfg, is32Bit) is not { } target)
            return;
        instruction.OpCode = OpCode.Move;
        instruction.SetOperands(result, new ReferenceCast(value, target));
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

        var pointer = new RuntimeMethodInfoAnalysisContext(resolved, assembly);

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
