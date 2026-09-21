using System.Buffers.Binary;
using System.Linq;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

internal static class AllocationConstructorRecovery
{
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
