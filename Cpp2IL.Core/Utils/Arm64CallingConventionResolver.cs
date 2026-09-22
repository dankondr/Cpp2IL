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
        => new(null, IsFloatingPoint(ctx.ReturnType) || GetHfa(ctx.ReturnType) != null ? "V0" : "X0");

    public override IOperand ReturnOperand(MethodAnalysisContext ctx)
    {
        var hfa = GetHfa(ctx.ReturnType);
        return hfa is { } info
            ? new AggregateOperand(ctx.ReturnType, Enumerable.Range(0, info.Count)
                .Select(i => (IOperand)new Register(null, FloatRegisters[i])).ToArray())
            : ReturnRegister(ctx);
    }

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
            if (par != null && GetHfa(par.ParameterType) is { } hfa)
            {
                if (floating + hfa.Count <= FloatRegisters.Length)
                {
                    args.Add(new AggregateOperand(par.ParameterType, Enumerable.Range(floating, hfa.Count)
                        .Select(i => (IOperand)new Register(null, FloatRegisters[i])).ToArray()));
                    floating += hfa.Count;
                    return;
                }

                args.Add(StackAggregate(par.ParameterType, hfa, stack));
                floating = FloatRegisters.Length;
                stack += Align(hfa.Count * hfa.ElementWidth);
                return;
            }
            else if (par != null && IsFloatingPoint(par))
            {
                if (floating < FloatRegisters.Length)
                {
                    args.Add(new Register(null, FloatRegisters[floating++]));
                    return;
                }
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

    public override void RemapRawArguments(Instruction call, MethodAnalysisContext resolved)
    {
        if (!HasRawArgumentLayout(call, resolved.AppContext)) return;
        var baseIndex = ArgBase(call);
        var result = Enumerable.Range(0, baseIndex).Select(i => call.Operands[i]).ToList();
        var integer = 0; var floating = 0; var stack = 0;
        void Add(ParameterAnalysisContext? parameter)
        {
            if (parameter != null && GetHfa(parameter.ParameterType) is { } hfa)
            {
                if (floating + hfa.Count <= FloatRegisters.Length)
                {
                    result.Add(new AggregateOperand(parameter.ParameterType, Enumerable.Range(floating, hfa.Count)
                        .Select(i => call.Operands[baseIndex + IntegerRegisters.Length + i]).ToArray()));
                    floating += hfa.Count;
                }
                else
                {
                    result.Add(StackAggregate(parameter.ParameterType, hfa, stack));
                    floating = FloatRegisters.Length;
                    stack += Align(hfa.Count * hfa.ElementWidth);
                }
                return;
            }
            if (parameter != null && IsFloatingPoint(parameter) && floating < FloatRegisters.Length)
            { result.Add(call.Operands[baseIndex + IntegerRegisters.Length + floating++]); return; }
            if ((parameter == null || !IsFloatingPoint(parameter)) && integer < IntegerRegisters.Length)
            { result.Add(call.Operands[baseIndex + integer++]); return; }
            result.Add(new StackOffset(stack)); stack += PtrSize;
        }
        if (!resolved.IsStatic) Add(null);
        foreach (var parameter in resolved.Parameters) Add(parameter);
        Add(null);
        call.SetOperands(result);
    }

    private static AggregateOperand StackAggregate(TypeAnalysisContext type, HfaInfo hfa, int offset)
        => new(type, Enumerable.Range(0, hfa.Count).Select(i => (IOperand)new StackOffset(offset + i * hfa.ElementWidth)).ToArray());

    private static int Align(int size) => (size + PtrSize - 1) / PtrSize * PtrSize;

    private static HfaInfo? GetHfa(TypeAnalysisContext type)
    {
        if (!type.IsValueType) return null;
        var fields = type.Fields.Where(field => !field.IsStatic).ToArray();
        if (fields is not { Length: >= 2 and <= 4 }) return null;
        var element = fields[0].FieldType;
        if (element != type.AppContext.SystemTypes.SystemSingleType || fields.Any(field => field.FieldType != element)) return null;
        const int width = 4;
        return TypeSizes.UnboxedSize(type, PtrSize) == width * fields.Length ? new HfaInfo(width, fields.Length) : null;
    }

    private readonly record struct HfaInfo(int ElementWidth, int Count);
}
