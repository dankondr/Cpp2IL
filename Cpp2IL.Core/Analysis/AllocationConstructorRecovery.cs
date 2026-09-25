using System.Buffers.Binary;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

internal static class AllocationConstructorRecovery
{
    internal static bool RewriteInlinedFieldInitializer(MethodAnalysisContext caller, Instruction allocation,
        Instruction constructorCall)
    {
        if (allocation.Operands is not [LocalVariable destination, TypeAnalysisContext allocated]
            || allocated.IsAbstract || allocated.IsValueType || allocated.IsGenericInstance
            || constructorCall is not { OpCode: OpCode.CallVoid,
                Operands: [MethodAnalysisContext { IsStatic: false, Name: ".ctor", Parameters.Count: 0 } baseConstructor, ..] }
            || constructorCall.Operands.Count < 2
            || !ReferenceEquals(constructorCall.Operands[1], destination)
            || ReferenceEquals(baseConstructor.DeclaringType, allocated))
            return false;

        var instructions = caller.ControlFlowGraph!.Instructions;
        var callIndex = instructions.IndexOf(constructorCall);
        if (callIndex < 0)
            return false;

        var stores = new List<(Instruction Instruction, FieldAnalysisContext Field, IOperand Value)>();
        for (var i = callIndex + 1; i < instructions.Count; i++)
        {
            var instruction = instructions[i];
            if (instruction.OpCode == OpCode.Nop)
                continue;
            if (instruction is { OpCode: OpCode.Move,
                    Operands: [FieldReference { Local: var receiver, Containers.Count: 0 } field, var value] }
                && ReferenceEquals(receiver, destination)
                && ReferenceEquals(field.Field.DeclaringType, allocated)
                && !field.Field.IsStatic
                && (field.Field.Attributes & FieldAttributes.InitOnly) != 0)
            {
                stores.Add((instruction, field.Field, value));
                continue;
            }
            break;
        }

        var readonlyFields = allocated.Fields
            .Where(field => !field.IsStatic && (field.Attributes & FieldAttributes.InitOnly) != 0)
            .ToArray();
        if (stores.Count == 0 || stores.Count != readonlyFields.Length
            || stores.Select(store => store.Field).ToHashSet().Count != readonlyFields.Length)
            return false;

        var constructors = allocated.Methods
            .Where(method => method is { IsStatic: false, Name: ".ctor" }
                && method.Parameters.Count == stores.Count
                && method.Parameters.Select(parameter => parameter.ParameterType)
                    .SequenceEqual(stores.Select(store => store.Field.FieldType)))
            .ToArray();
        if (constructors is not [{ } constructor])
            return false;

        constructorCall.SetOperands([constructor, destination, .. stores.Select(store => store.Value)]);
        foreach (var (instruction, _, _) in stores)
        {
            instruction.OpCode = OpCode.Nop;
            instruction.SetOperands();
        }
        return true;
    }

    internal static MethodAnalysisContext? Resolve(Instruction allocation, MethodAnalysisContext calledConstructor)
    {
        // Native allocation and initialization are separate. A call to Object::.ctor
        // does not mean the allocation's concrete type was System.Object.
        // Reuse the concrete ctor only when its entire A64 body proves that it does
        // exactly that same base initialization; never guess an arbitrary .ctor.
        if (allocation.OpCode != OpCode.Newobj
            || allocation.Operands is not [LocalVariable, TypeAnalysisContext allocated]
            || allocated.AppContext.InstructionSet is not NewArmV8InstructionSet
            || allocated.IsAbstract || allocated.IsValueType || allocated.IsGenericInstance || allocated.GenericParameters.Count != 0
            || calledConstructor is not { IsStatic: false, Name: ".ctor", Parameters.Count: 0 }
            || !ReferenceEquals(calledConstructor.DeclaringType, allocated.AppContext.SystemTypes.SystemObjectType)
            || !ReferenceEquals(allocated.BaseType, calledConstructor.DeclaringType)
            || calledConstructor.UnderlyingPointer == 0)
            return null;

        var constructors = allocated.Methods.Where(m => m is { IsStatic: false, Name: ".ctor", Parameters.Count: 0 }).ToArray();
        if (constructors is not [{ } constructor] || constructor.UnderlyingPointer == 0 || constructor.RawBytes.Length != 8)
            return null;

        var bytes = constructor.RawBytes.AsSpan();
        // mov x1, xzr (hidden MethodInfo), followed by an unconditional B.
        if (BinaryPrimitives.ReadUInt32LittleEndian(bytes) != 0xaa1f03e1)
            return null;
        var branch = BinaryPrimitives.ReadUInt32LittleEndian(bytes[4..]);
        if ((branch & 0xfc000000) != 0x14000000)
            return null;
        var displacement = (long)((int)(branch << 6) >> 4);
        var target = unchecked((ulong)((long)constructor.UnderlyingPointer + 4 + displacement));
        return target == calledConstructor.UnderlyingPointer ? constructor : null;
    }
}
