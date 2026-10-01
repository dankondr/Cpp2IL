using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils;

// integer args in X0-X7, fp args in V0-V7 (independent counters), rest on the stack.
// Oversized struct returns go via a pointer in X8, which is not an argument register.
public class Arm64CallingConventionResolver : BaseCallingConventionResolver
{
    private const int PtrSize = 8;

    private static readonly string[] IntegerRegisters = ["X0", "X1", "X2", "X3", "X4", "X5", "X6", "X7"];
    private static readonly string[] FloatRegisters = ["V0", "V1", "V2", "V3", "V4", "V5", "V6", "V7"];

    public override Register ReturnRegister(MethodAnalysisContext ctx)
        => new(null, FloatingRegisterCount(ctx.ReturnType) > 0 ? "V0" : "X0");

    public override Register? HiddenReturnBufferRegister(MethodAnalysisContext ctx)
        => ReturnsViaHiddenBuffer(ctx) ? new Register(null, "X8") : null;

    public override bool ReturnsViaHiddenBuffer(MethodAnalysisContext ctx)
    {
        if (ctx.IsVoid)
            return false;

        var returnType = ctx.ReturnType;
        if (!returnType.IsValueType || IsFloatingPoint(returnType))
            return false;

        var size = StructSize(returnType);
        if (size == 0)
            return false; // unknown size (e.g. generic), assume a register return

        return size > 16;
    }

    private static long StructSize(TypeAnalysisContext type)
    {
        var size = TypeSizes.UnboxedSize(type, PtrSize);
        if (size == 0)
            size = TypeSizes.MinimumUnboxedSize(type, PtrSize);
        return size;
    }

    // integer args in X0-X7, fp args in V0-V7 (independent counters). A homogeneous
    // float aggregate of n floats takes one V register per lane; any other value
    // type of 9-16 bytes takes an integer register pair; wider composites go on the
    // stack.
    public override IReadOnlyList<AggregateLane> ExtraLanes(TypeAnalysisContext type, Register firstLane)
    {
        var firstIndex = FirstRegisterIndex(firstLane, FloatRegisters);
        if (firstIndex >= 0
            && TryGetHomogeneousFloatAggregate(type, [], out var elementType, out var count)
            && count > 1
            && firstIndex + count <= FloatRegisters.Length)
        {
            var lanes = new List<AggregateLane>(count - 1);
            var width = (int)StructSize(elementType!);
            for (var i = 1; i < count; i++)
                lanes.Add(new AggregateLane(new Register(null, FloatRegisters[firstIndex + i]), i * width, width));
            return lanes;
        }

        firstIndex = FirstRegisterIndex(firstLane, IntegerRegisters);
        if (firstIndex >= 0
            && firstIndex < IntegerRegisters.Length - 1
            && !IsFloatingPoint(type)
            && type.IsValueType
            && StructSize(type) is > 8 and <= 16)
            return [new AggregateLane(new Register(null, IntegerRegisters[firstIndex + 1]), 8,
                (int)StructSize(type) - 8)];

        return [];
    }

    private static int FirstRegisterIndex(Register register, string[] registers)
    {
        for (var i = 0; i < registers.Length; i++)
            if (registers[i] == register.Name)
                return i;
        return -1;
    }

    protected override (string[] Integer, string[] Float) RawRegisters(ApplicationAnalysisContext app)
        => (IntegerRegisters, FloatRegisters);

    protected override bool HiddenBufferConsumesArgumentSlot => false;

    protected override IReadOnlyList<IOperand> ManagedArgumentRegisters(MethodAnalysisContext resolved)
        => ResolveForManaged(resolved);

    public override IOperand[] ResolveForManaged(MethodAnalysisContext ctx)
    {
        var args = new List<IOperand>();

        var integer = 0;
        var floating = 0;
        var stack = 0;

        void AddParameter(ParameterAnalysisContext? par)
        {
            var floatingRegisterCount = par == null ? 0 : FloatingRegisterCount(par.ParameterType);
            if (floatingRegisterCount > 0)
            {
                if (floating + floatingRegisterCount <= FloatRegisters.Length)
                {
                    args.Add(new Register(null, FloatRegisters[floating]));
                    floating += floatingRegisterCount;
                    return;
                }

                floating = FloatRegisters.Length;
            }
            else
            {
                var integerRegisterCount = par == null ? 1 : IntegerRegisterCount(par.ParameterType);
                if (integerRegisterCount > 0 && integer + integerRegisterCount <= IntegerRegisters.Length)
                {
                    args.Add(new Register(null, IntegerRegisters[integer]));
                    integer += integerRegisterCount;
                    return;
                }

                // A composite that does not fit the remaining registers spills whole to
                // the stack and the register file is done (AAPCS C.3); a >16 byte one
                // is passed on the stack without consuming registers at all.
                if (integerRegisterCount > 0)
                    integer = IntegerRegisters.Length;
            }

            args.Add(new StackOffset(stack));
            stack += par != null && par.ParameterType.IsValueType
                ? (int)((System.Math.Max(StructSize(par.ParameterType), 1) + 7) & ~7L)
                : PtrSize;
        }

        if (!ctx.IsStatic)
            AddParameter(null);

        foreach (var par in ctx.Parameters)
            AddParameter(par);

        AddParameter(null); // The MethodInfo argument

        return args.ToArray();
    }

    private static int FloatingRegisterCount(TypeAnalysisContext type)
        => TryGetHomogeneousFloatAggregate(type, [], out _, out var count) ? count : 0;

    // 0 = too wide for registers at all (stack), 1 = one register, 2 = a pair.
    private static int IntegerRegisterCount(TypeAnalysisContext type)
    {
        if (!type.IsValueType || IsFloatingPoint(type))
            return 1;

        return StructSize(type) switch
        {
            > 8 and <= 16 => 2,
            > 16 => 0,
            _ => 1,
        };
    }

    private static bool TryGetHomogeneousFloatAggregate(TypeAnalysisContext type,
        HashSet<TypeAnalysisContext> active, out TypeAnalysisContext? elementType, out int count)
    {
        if (IsFloatingPoint(type))
        {
            elementType = type;
            count = 1;
            return true;
        }

        elementType = null;
        count = 0;
        if (!type.IsValueType || !active.Add(type))
            return false;

        var fields = type.Fields.Where(field => !field.IsStatic).ToArray();
        if (fields.Length is < 1 or > 4)
        {
            active.Remove(type);
            return false;
        }

        foreach (var field in fields)
        {
            if (!TryGetHomogeneousFloatAggregate(field.FieldType, active, out var fieldElementType, out var fieldCount)
                || count + fieldCount > 4)
            {
                active.Remove(type);
                return false;
            }
            if (elementType != null && fieldElementType != elementType)
            {
                active.Remove(type);
                return false;
            }

            elementType = fieldElementType;
            count += fieldCount;
        }

        active.Remove(type);
        return true;
    }
}
