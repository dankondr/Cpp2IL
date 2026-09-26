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

        var size = TypeSizes.UnboxedSize(returnType, PtrSize);
        if (size == 0)
            size = TypeSizes.MinimumUnboxedSize(returnType, PtrSize);
        if (size == 0)
            return false; // unknown size (e.g. generic), assume a register return

        return size > 16;
    }

    protected override (string[] Integer, string[] Float) RawRegisters(ApplicationAnalysisContext app)
        => (IntegerRegisters, FloatRegisters);

    protected override bool HiddenBufferConsumesArgumentSlot => false;

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
            else if (integer < IntegerRegisters.Length)
            {
                args.Add(new Register(null, IntegerRegisters[integer++]));
                return;
            }

            args.Add(new StackOffset(stack));
            stack += PtrSize;
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
