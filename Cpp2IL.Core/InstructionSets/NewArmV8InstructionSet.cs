using System;
using System.Collections.Generic;
using System.Linq;
using Disarm;
using Cpp2IL.Core.Api;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Disarm.InternalDisassembly;
using LibCpp2IL.Elf;

namespace Cpp2IL.Core.InstructionSets;

public class NewArmV8InstructionSet : Cpp2IlInstructionSet
{
    [ThreadStatic]
    private static Dictionary<string, ulong>? adrpOffsets;

    [ThreadStatic]
    private static Dictionary<string, (bool Greater, IOperand Value, IOperand Bound)>? vectorComparisons;

    private static readonly Arm64CallingConventionResolver CallingConventions = new();

    // Scalar libm imports with an exact managed spelling. fmod/fmodf are truncated
    // remainders (sign of the dividend), which is precisely CIL `rem` —
    // Math.IEEERemainder rounds the quotient instead, so Method=null maps them to
    // OpCode.Modulo rather than a call.
    internal static readonly IReadOnlyDictionary<string, (string? Method, bool IsDouble, int ArgumentCount)> ScalarMathImports
        = new Dictionary<string, (string?, bool, int)>
        {
            ["sinf"] = ("Sin", false, 1),     ["sin"] = ("Sin", true, 1),
            ["cosf"] = ("Cos", false, 1),     ["cos"] = ("Cos", true, 1),
            ["tanf"] = ("Tan", false, 1),     ["tan"] = ("Tan", true, 1),
            ["asinf"] = ("Asin", false, 1),   ["asin"] = ("Asin", true, 1),
            ["acosf"] = ("Acos", false, 1),   ["acos"] = ("Acos", true, 1),
            ["atanf"] = ("Atan", false, 1),   ["atan"] = ("Atan", true, 1),
            ["expf"] = ("Exp", false, 1),     ["exp"] = ("Exp", true, 1),
            ["logf"] = ("Log", false, 1),     ["log"] = ("Log", true, 1),
            ["atan2f"] = ("Atan2", false, 2), ["atan2"] = ("Atan2", true, 2),
            ["powf"] = ("Pow", false, 2),     ["pow"] = ("Pow", true, 2),
            ["fmodf"] = (null, false, 2),    ["fmod"] = (null, true, 2),
        };

    public override BaseCallingConventionResolver CallingConventionResolver => CallingConventions;

    private static Immediate Imm(long value) => new(value);
    private static Immediate Imm(ulong value) => new(unchecked((long)value));

    private static string NormalizeRegister(Arm64Register reg) => reg switch
    {
        >= Arm64Register.W0 and <= Arm64Register.W31 => "X" + (reg - Arm64Register.W0),
        >= Arm64Register.X0 and <= Arm64Register.X31 => "X" + (reg - Arm64Register.X0),
        >= Arm64Register.V0 and <= Arm64Register.V31 => "V" + (reg - Arm64Register.V0),
        >= Arm64Register.D0 and <= Arm64Register.D31 => "V" + (reg - Arm64Register.D0),
        >= Arm64Register.S0 and <= Arm64Register.S31 => "V" + (reg - Arm64Register.S0),
        >= Arm64Register.H0 and <= Arm64Register.H31 => "V" + (reg - Arm64Register.H0),
        >= Arm64Register.B0 and <= Arm64Register.B31 => "V" + (reg - Arm64Register.B0),
        _ => reg.ToString()
    };

    private static Register Reg(Arm64Register reg) => new(null, NormalizeRegister(reg));

    private static bool IsScalarFloatRegister(Arm64Register reg) =>
        reg is >= Arm64Register.S0 and <= Arm64Register.S31
            or >= Arm64Register.D0 and <= Arm64Register.D31;

    private static bool IsWordRegister(Arm64Register reg) => reg is >= Arm64Register.W0 and <= Arm64Register.W31;

    private static int RegisterWidthBytes(Arm64Register reg) => reg switch
    {
        >= Arm64Register.B0 and <= Arm64Register.B31 => 1,
        >= Arm64Register.H0 and <= Arm64Register.H31 => 2,
        >= Arm64Register.W0 and <= Arm64Register.W31 or >= Arm64Register.S0 and <= Arm64Register.S31 => 4,
        >= Arm64Register.X0 and <= Arm64Register.X31 or >= Arm64Register.D0 and <= Arm64Register.D31 => 8,
        >= Arm64Register.V0 and <= Arm64Register.V31 => 16,
        _ => 0
    };

    // integer register 31 is SP or ZR depending on context, callers must decide which
    private static bool IsReg31(Arm64Register reg) => reg is Arm64Register.X31 or Arm64Register.W31;

    public override BinarySlice GetRawBytesForMethod(MethodAnalysisContext context, bool isAttributeGenerator)
    {
        var binary = context.AppContext.Binary;

        if (context is not ConcreteGenericMethodAnalysisContext)
        {
            //Managed method or attr gen => grab raw byte range between a and b
            var startOfNextFunction = context.AppContext.GetAddressOfNextFunctionStart(context.UnderlyingPointer);
            var count = (int)(startOfNextFunction - context.UnderlyingPointer);

            if (startOfNextFunction > 0)
            {
                var startRaw = (int)binary.MapVirtualAddressToRaw(context.UnderlyingPointer);
                if (startRaw > 0 && startRaw + count <= binary.RawLength)
                    return new BinarySlice(binary, startRaw, count);
            }
        }

        var result = NewArm64Utils.GetArm64MethodBodyAtVirtualAddress(context.AppContext, context.UnderlyingPointer);
        var lastInsn = result.LastValid();

        var start = (int)binary.MapVirtualAddressToRaw(context.UnderlyingPointer);
        // Map the last instruction (always within segment) and add 4 (ARM64 instruction size).
        // This avoids mapping endVa which may land exactly at a segment boundary gap.
        var end = (int)binary.MapVirtualAddressToRaw(lastInsn.Address) + 4;

        //Sanity check
        if (start < 0 || end < 0 || start >= binary.RawLength || end >= binary.RawLength)
            throw new Exception($"Failed to map virtual address 0x{context.UnderlyingPointer:X} to raw address for method {context!.DeclaringType?.FullName}/{context.Name} - start: 0x{start:X}, end: 0x{end:X} are out of bounds for length {binary.RawLength}.");

        return new BinarySlice(binary, start, end - start);
    }

    public override List<IOperand> GetParameterOperandsFromMethod(MethodAnalysisContext context)
    {
        return CallingConventions.ResolveForManaged(context).ToList();
    }

    public override (IReadOnlyList<ulong> DataReferences, IReadOnlyList<ulong> CallTargets) InspectPotentialThrowHelper(ApplicationAnalysisContext context, ulong address)
    {
        //Deliberately not calling NewArm64Utils here, it's too slow
        const int maxInstructions = 48;

        var binary = context.Binary;
        var rawStart = (int)binary.MapVirtualAddressToRaw(address);
        if (rawStart <= 0)
            return ([], []);

        var content = binary.GetRawBinaryContent();
        var window = System.Math.Min(maxInstructions * 4, content.Length - rawStart);
        if (window < 4)
            return ([], []);

        List<Arm64Instruction> body;
        try
        {
            body = Disassembler.Disassemble(content.Slice(rawStart, window), address, new Disassembler.Options(true, true, false)).ToList();
        }
        catch
        {
            return ([], []);
        }

        var dataReferences = new List<ulong>();
        var callTargets = new List<ulong>();
        var pages = new Dictionary<Arm64Register, ulong>();

        foreach (var insn in body)
        {
            switch (insn.Mnemonic)
            {
                case Arm64Mnemonic.ADRP:
                    pages[insn.Op0Reg] = (ulong)((long)(insn.Address & ~0xFFFUL) + insn.Op1Imm);
                    break;
                case Arm64Mnemonic.ADD when insn.Op2Kind == Arm64OperandKind.Immediate && pages.TryGetValue(insn.Op1Reg, out var page):
                    dataReferences.Add(page + (ulong)insn.Op2Imm);
                    break;
                case Arm64Mnemonic.ADR:
                    dataReferences.Add((ulong)((long)insn.Address + insn.Op1Imm));
                    break;
                case Arm64Mnemonic.BL:
                    callTargets.Add(insn.BranchTarget);
                    break;
            }

            if (insn.Mnemonic != Arm64Mnemonic.ADRP && insn.Op0Kind == Arm64OperandKind.Register)
                pages.Remove(insn.Op0Reg);
            
            if (insn.Mnemonic is Arm64Mnemonic.RET or Arm64Mnemonic.RETAA or Arm64Mnemonic.RETAB or Arm64Mnemonic.BR or Arm64Mnemonic.INVALID
                || (insn.Mnemonic == Arm64Mnemonic.B && insn.MnemonicConditionCode is Arm64ConditionCode.NONE or Arm64ConditionCode.AL))
                break;
        }

        return (dataReferences, callTargets);
    }

    public override List<Instruction> GetIsilFromMethod(MethodAnalysisContext context)
        => ConvertInstructions(NewArm64Utils.GetArm64MethodBodyAtVirtualAddress(context.AppContext, context.UnderlyingPointer), context);

    internal List<Instruction> ConvertInstructions(IEnumerable<Arm64Instruction> insns, MethodAnalysisContext context,
        Func<ulong, string?>? importNameResolver = null)
    {
        if (adrpOffsets == null) // initializers for ThreadStatic fields only run on the first thread
            adrpOffsets = new();
        else
            adrpOffsets.Clear();
        vectorComparisons ??= new();
        vectorComparisons.Clear();

        var instructions = new List<Instruction>();
        var addresses = new List<ulong>();

        var instructionList = insns as IReadOnlyList<Arm64Instruction> ?? insns.ToList();
        var scalarizer = new Arm64VectorScalarizer();
        scalarizer.Begin(instructionList);

        foreach (var instruction in instructionList)
            ConvertInstructionStatement(instruction, instructions, addresses, context, scalarizer, importNameResolver);

        // Add return if the function doesn't end with one already
        if (instructions.Count > 0 && instructions[^1].OpCode != OpCode.Return)
        {
            var index = instructions[^1].Index + 1;

            if (context.IsVoid)
                instructions.Add(new Instruction(index, OpCode.Return));
            else
                instructions.Add(new Instruction(index, OpCode.Return, CallingConventions.ReturnRegister(context)));
        }

        // fix branches
        for (var i = 0; i < instructions.Count; i++)
        {
            var instruction = instructions[i];

            if (instruction.OpCode != OpCode.Jump && instruction.OpCode != OpCode.ConditionalJump)
                continue;

            var targetAddress = ((Immediate)instruction.Operands[0]).UnsignedValue;
            var targetIndex = addresses.FindIndex(addr => addr == targetAddress);

            if (targetIndex == -1)
            {
                instruction.OpCode = OpCode.Invalid;
                instruction.SetOperands(new StringLiteral($"Jump target not found in method: 0x{targetAddress:X4}"));
                continue;
            }

            var targetInstruction = instructions[targetIndex];

            instruction.SetOperand(0, targetInstruction);
        }

        adrpOffsets.Clear();
        return instructions;
    }

    private void ConvertInstructionStatement(Arm64Instruction instruction, List<Instruction> instructions, List<ulong> addresses, MethodAnalysisContext context, Arm64VectorScalarizer scalarizer, Func<ulong, string?>? importNameResolver)
    {
        var address = instruction.Address;

        Instruction Add(ulong address, OpCode opCode, params List<IOperand> operands)
        {
            addresses.Add(address);
            var newInstruction = new Instruction(instructions.Count, opCode, operands);
            instructions.Add(newInstruction);
            return newInstruction;
        }

        Instruction AddInteger(ulong address, OpCode opCode, params List<IOperand> operands)
        {
            var generated = Add(address, opCode, operands);
            if (instruction.Op0Kind == Arm64OperandKind.Register && IsWordRegister(instruction.Op0Reg))
                generated.NativeIntegerWidthBits = 32;
            return generated;
        }

        void AddCallAt(ulong target)
        {
            if (IsThreadStaticDataHelper(context.AppContext, target))
            {
                var threadStatic = Add(address, OpCode.Call,
                    new StringLiteral(nameof(BaseKeyFunctionAddresses.il2cpp_codegen_get_thread_static_data)),
                    new Register(null, "X0"));
                threadStatic.AddOperands([new Register(null, "X0")]);
                return;
            }

            if (context.AppContext.MethodsByAddress.TryGetValue(target, out var possibleMethods) && possibleMethods.Count > 0)
            {
                MethodAnalysisContext ctx;
                if (possibleMethods.Count == 1)
                {
                    ctx = possibleMethods[0];
                }
                else
                {
                    // multiple methods folded onto one address, pick the one with the most arguments so nothing gets truncated
                    ctx = possibleMethods[0];
                    var mostArguments = -1;
                    foreach (var method in possibleMethods)
                    {
                        var arguments = method.Parameters.Count + (method.IsStatic ? 0 : 1);
                        if (arguments > mostArguments)
                        {
                            mostArguments = arguments;
                            ctx = method;
                        }
                    }
                }

                var call = ctx.IsVoid
                    ? Add(address, OpCode.CallVoid, Imm(target))
                    : Add(address, OpCode.Call, Imm(target),
                        CallingConventions.ReturnsViaHiddenBuffer(ctx)
                            ? new MemoryOperand(CallingConventions.HiddenReturnBufferRegister(ctx))
                            : CallingConventions.ReturnRegister(ctx));

                call.AddOperands(CallingConventions.ResolveForManaged(ctx));
            }
            else if (!TryEmitScalarMathImport(target))
            {
                // Not a managed method, so we don't know its signature, preserve all argument registers
                var call = Add(address, OpCode.Call, Imm(target), new Register(null, "X0"));
                call.AddOperands(CallingConventions.ResolveForUnmanaged(context.AppContext, target));
            }
        }

        void AddReturn()
        {
            if (context.IsVoid)
                Add(address, OpCode.Return);
            else
                Add(address, OpCode.Return, CallingConventions.ReturnRegister(context));
        }

        // for pre/post indexed accesses, apply the base register update on the correct side of the access
        void EmitWriteback(bool beforeAccess)
        {
            var isPre = instruction.MemIndexMode == Arm64MemoryIndexMode.PreIndex;
            var isPost = instruction.MemIndexMode == Arm64MemoryIndexMode.PostIndex;

            if (!(beforeAccess ? isPre : isPost))
                return;

            if (IsReg31(instruction.MemBase))
                Add(address, OpCode.ShiftStack, Imm(instruction.MemOffset));
            else
                Add(address, OpCode.Add, Reg(instruction.MemBase), Reg(instruction.MemBase), Imm(instruction.MemOffset));
        }

        // the memory operand for the current instruction's access, offset by extraOffset (for the second reg of a pair)
        IOperand MemOperand(long extraOffset = 0, int accessSize = 0)
        {
            var baseReg = instruction.MemBase;
            // writeback modes apply the offset to the base register itself, the access is at [base]
            var offset = (instruction.MemIndexMode == Arm64MemoryIndexMode.Offset ? instruction.MemOffset : 0) + extraOffset;

            if (baseReg == Arm64Register.INVALID)
                return new MemoryOperand(addend: offset, accessSize: accessSize);

            if (IsReg31(baseReg))
                return new StackOffset((int)offset);

            if (instruction.MemAddendReg != Arm64Register.INVALID)
                return new MemoryOperand(Reg(baseReg), Reg(instruction.MemAddendReg), offset, 1 << instruction.MemExtendOrShiftAmount, accessSize);

            // a load through a register holding an ADRP page address is really an absolute load
            if (adrpOffsets!.TryGetValue(NormalizeRegister(baseReg), out var page))
                return new MemoryOperand(addend: (long)page + offset, accessSize: accessSize);

            return new MemoryOperand(Reg(baseReg), addend: offset, accessSize: accessSize);
        }

        var flagN = new Register(null, "N");
        var flagZ = new Register(null, "Z");
        var flagC = new Register(null, "C");
        var flagV = new Register(null, "V");

        // models op0 - op1, which CMP and friends are defined in terms of
        void EmitCompareFlags(IOperand op0, IOperand op1)
        {
            var temp1 = new Register(null, "TEMP1");
            var temp2 = new Register(null, "TEMP2");
            var temp3 = new Register(null, "TEMP3");
            var temp4 = new Register(null, "TEMP4");

            Add(address, OpCode.CheckLess, flagC, op0, op1); // arm's C is the inverse of a borrow
            Add(address, OpCode.Not, flagC, flagC);
            AddInteger(address, OpCode.Subtract, temp1, op0, op1);
            Add(address, OpCode.CheckLess, flagN, temp1, Imm(0));
            Add(address, OpCode.CheckEqual, flagZ, temp1, Imm(0));
            AddInteger(address, OpCode.Xor, temp2, op0, op1);
            AddInteger(address, OpCode.Xor, temp3, op0, temp1);
            AddInteger(address, OpCode.And, temp4, temp2, temp3);
            Add(address, OpCode.CheckLess, flagV, temp4, Imm(0));
        }

        void EmitResultFlags(IOperand result)
        {
            Add(address, OpCode.CheckLess, flagN, result, Imm(0));
            Add(address, OpCode.CheckEqual, flagZ, result, Imm(0));
            Add(address, OpCode.Move, flagC, Imm(0));
            Add(address, OpCode.Move, flagV, Imm(0));
        }

        // Evaluates the "Rm {<shift> #imm}" operand of a logical shifted-register
        // encoding into ISIL. The produced operand carries the register width: a
        // word form is a real 32-bit value (zero-extended/truncated), an x form
        // keeps the full 64 bits. Returns null when the encoding carries a shift
        // combination that cannot be represented honestly.
        IOperand? EmitLogicalShiftedOperand()
        {
            var source = ConvertOperand(instruction, 2);

            // Logical immediate encodings carry no shift triple, and a zero
            // amount passes the operand through untouched - no temporary is
            // created for either case.
            if (instruction.Op2Kind != Arm64OperandKind.Register || instruction.Op3Imm == 0)
                return source;

            var shift = instruction.Op3ShiftType;
            var amount = (int)instruction.Op3Imm;
            var is32 = IsWordRegister(instruction.Op0Reg);
            var width = is32 ? 32 : 64;

            // Disarm rejects out-of-range shift encodings during decode; refuse
            // to guess if one ever slips through.
            if (amount < 0 || amount >= width || shift == Arm64ShiftType.NONE)
                return null;

            // OpCode.ShiftRight is an arithmetic shift, so a logical right shift
            // is the shift followed by a mask clearing the sign-filled bits.
            IOperand EmitLogicalShiftRight(IOperand input)
            {
                var raw = new Register(null, "TEMP_LOGICAL_SHIFT_RAW");
                Add(address, OpCode.ShiftRight, raw, input, Imm(amount));
                var masked = new Register(null, "TEMP_LOGICAL_SHIFT");
                AddInteger(address, OpCode.And, masked, raw, Imm((1L << (width - amount)) - 1));
                return masked;
            }

            switch (shift)
            {
                case Arm64ShiftType.LSL:
                {
                    var shifted = new Register(null, "TEMP_LOGICAL_SHIFT");
                    AddInteger(address, OpCode.ShiftLeft, shifted, source, Imm(amount));
                    return shifted;
                }
                case Arm64ShiftType.LSR:
                    return EmitLogicalShiftRight(source);
                case Arm64ShiftType.ASR:
                {
                    // a word arithmetic shift takes its sign from bit 31, not bit 63
                    var input = source;
                    if (is32)
                    {
                        input = new Register(null, "TEMP_LOGICAL_SHIFT_SRC");
                        Add(address, OpCode.SignExtend32, input, source);
                    }

                    var shifted = new Register(null, "TEMP_LOGICAL_SHIFT");
                    AddInteger(address, OpCode.ShiftRight, shifted, input, Imm(amount));
                    return shifted;
                }
                case Arm64ShiftType.ROR:
                {
                    // ror(x, n) = lsr(x, n) | lsl(x, width - n)
                    var rightPart = EmitLogicalShiftRight(source);

                    var leftPart = new Register(null, "TEMP_LOGICAL_SHIFT_LEFT");
                    AddInteger(address, OpCode.ShiftLeft, leftPart, source, Imm(width - amount));

                    var rotated = new Register(null, "TEMP_LOGICAL_SHIFT_ROT");
                    AddInteger(address, OpCode.Or, rotated, rightPart, leftPart);
                    return rotated;
                }
                default:
                    return null;
            }
        }

        // emits any instructions needed to evaluate the condition, returning an operand that is nonzero when it holds
        IOperand EmitCondition(Arm64ConditionCode condition)
        {
            var temp = new Register(null, "TEMPCOND");
            var temp2 = new Register(null, "TEMPCOND2");

            switch (condition)
            {
                case Arm64ConditionCode.EQ:
                    return flagZ;
                case Arm64ConditionCode.NE:
                    Add(address, OpCode.Not, temp, flagZ);
                    return temp;
                case Arm64ConditionCode.GE:
                    Add(address, OpCode.CheckEqual, temp, flagN, flagV);
                    return temp;
                case Arm64ConditionCode.LT:
                    Add(address, OpCode.CheckEqual, temp, flagN, flagV);
                    Add(address, OpCode.Not, temp, temp);
                    return temp;
                case Arm64ConditionCode.GT:
                    Add(address, OpCode.CheckEqual, temp, flagN, flagV);
                    Add(address, OpCode.Not, temp2, flagZ);
                    Add(address, OpCode.And, temp, temp, temp2);
                    return temp;
                case Arm64ConditionCode.LE:
                    Add(address, OpCode.CheckEqual, temp, flagN, flagV);
                    Add(address, OpCode.Not, temp, temp);
                    Add(address, OpCode.Or, temp, temp, flagZ);
                    return temp;
                case Arm64ConditionCode.CS: // unsigned >=
                    return flagC;
                case Arm64ConditionCode.CC: // unsigned <
                    Add(address, OpCode.Not, temp, flagC);
                    return temp;
                case Arm64ConditionCode.HI: // unsigned >
                    Add(address, OpCode.Not, temp, flagZ);
                    Add(address, OpCode.And, temp, flagC, temp);
                    return temp;
                case Arm64ConditionCode.LS: // unsigned <=
                    Add(address, OpCode.Not, temp, flagC);
                    Add(address, OpCode.Or, temp, temp, flagZ);
                    return temp;
                case Arm64ConditionCode.MI:
                    return flagN;
                case Arm64ConditionCode.PL:
                    Add(address, OpCode.Not, temp, flagN);
                    return temp;
                case Arm64ConditionCode.VS:
                    return flagV;
                case Arm64ConditionCode.VC:
                    Add(address, OpCode.Not, temp, flagV);
                    return temp;
                default: // AL/NV are both unconditional
                    return Imm(1);
            }
        }

        // dest = cond ? <emitTrueValue into dest> : <emitFalseValue into dest>
        void EmitConditionalAssign(Arm64ConditionCode condition, Action emitTrueValue, Action<ulong> emitFalseValue)
        {
            var inverse = new Register(null, "TEMPCSEL");
            Add(address, OpCode.Not, inverse, EmitCondition(condition));
            Add(address, OpCode.ConditionalJump, Imm(address + 1), inverse);
            emitTrueValue();
            Add(address, OpCode.Jump, Imm(address + 2));
            emitFalseValue(address + 1);
            Add(address + 2, OpCode.Nop);
        }

        MethodAnalysisContext? ResolveMathMethod(string name, bool isDouble, int argumentCount)
        {
            var assembly = context.AppContext.SystemTypes.SystemDoubleType.DeclaringAssembly;
            var single = context.AppContext.SystemTypes.SystemSingleType;
            var @double = context.AppContext.SystemTypes.SystemDoubleType;
            var types = isDouble
                ? new[] { assembly.GetTypeByFullName("System.Math") }
                : new[]
                {
                    argumentCount == 2
                        ? context.AppContext.AssembliesByName.GetValueOrDefault("UnityEngine.CoreModule")
                            ?.GetTypeByFullName("UnityEngine.Mathf")
                        : null,
                    assembly.GetTypeByFullName("System.MathF"),
                    assembly.GetTypeByFullName("System.Math")
                };

            foreach (var mathType in types.OfType<TypeAnalysisContext>())
                foreach (var numberType in isDouble ? new[] { @double } : new[] { single, @double })
                    if (mathType.Methods.FirstOrDefault(method =>
                            method.IsStatic && method.Name == name && method.Parameters.Count == argumentCount
                            && method.Parameters.All(parameter => parameter.ParameterType == numberType)) is { } method)
                        return method;

            return null;
        }

        void EmitMathUnary(string name, IOperand destination, IOperand source, bool isDouble)
        {
            if (ResolveMathMethod(name, isDouble, 1) is { } method)
            {
                var needsSingleBridge = !isDouble && method.Parameters[0].ParameterType == context.AppContext.SystemTypes.SystemDoubleType;
                var argument = source;
                if (needsSingleBridge)
                {
                    argument = new Register(null, "TEMP_MATH_ARG");
                    Add(address, OpCode.Move, argument, source).NativeFloatWidthBits = 32;
                }
                var call = Add(address, OpCode.Call, method, destination);
                call.AddOperands([argument]);
                if (needsSingleBridge)
                    call.NativeFloatWidthBits = 32;
            }
            else
            {
                Add(address, OpCode.NotImplemented, new StringLiteral($"ARM64 {name} intrinsic is unavailable for this target framework."));
            }
        }

        void EmitMathBinary(string name, IOperand destination, IOperand left, IOperand right, bool isDouble)
        {
            if (ResolveMathMethod(name, isDouble, 2) is not { } method)
            {
                Add(address, OpCode.NotImplemented, new StringLiteral($"ARM64 {name} intrinsic is unavailable for this target framework."));
                return;
            }

            var arguments = new[] { left, right };
            if (!isDouble && method.Parameters[0].ParameterType == context.AppContext.SystemTypes.SystemDoubleType)
            {
                arguments = arguments.Select((operand, index) =>
                {
                    var argument = new Register(null, $"TEMP_MATH_ARG{index}");
                    Add(address, OpCode.Move, argument, operand).NativeFloatWidthBits = 32;
                    return (IOperand)argument;
                }).ToArray();
            }
            var call = Add(address, OpCode.Call, method, destination);
            call.AddOperands(arguments);
            if (!isDouble)
                call.NativeFloatWidthBits = 32;
        }

        // A call target that is an adrp+ldr(+add)+br GOT trampoline names its
        // import through the dynamic relocation on the pointer slot. Pure scalar
        // libm calls lower to their managed equivalents; AAPCS64 passes the
        // first float/double arguments in s0/d0..s1/d1 (normalized V0/V1) and
        // leaves the scalar result in s0/d0. Anything unrecognized keeps the
        // unresolved call target — imports are never masked as key functions.
        bool TryEmitScalarMathImport(ulong callTarget)
        {
            var importName = importNameResolver != null
                ? importNameResolver(callTarget)
                : NewArm64KeyFunctionAddresses.TryResolveGotVeneerImportName(context.AppContext.Binary, callTarget, out var resolved)
                    ? resolved
                    : null;

            if (importName == null || !ScalarMathImports.TryGetValue(importName, out var import))
                return false;

            var result = new Register(null, "V0");
            if (import.Method is not { } managedName)
            {
                Add(address, OpCode.Modulo, result, new Register(null, "V0"), new Register(null, "V1"))
                    .NativeFloatWidthBits = import.IsDouble ? 64 : 32;
                return true;
            }
            if (import.ArgumentCount == 2)
                EmitMathBinary(managedName, result, new Register(null, "V0"), new Register(null, "V1"), import.IsDouble);
            else
                EmitMathUnary(managedName, result, new Register(null, "V0"), import.IsDouble);
            return true;
        }

        TypeAnalysisContext? UnityVector4() => context.AppContext.AssembliesByName
            .GetValueOrDefault("UnityEngine.CoreModule")?.Types
            .FirstOrDefault(type => type.DefaultFullName == "UnityEngine.Vector4");

        bool EmitVector4Call(string name, IOperand destination, params IOperand[] operands)
        {
            var method = UnityVector4()?.Methods.FirstOrDefault(candidate => candidate.IsStatic
                && candidate.Name == name && candidate.Parameters.Count == operands.Length);
            if (method == null)
                return false;
            var call = Add(address, OpCode.Call, method, destination);
            call.AddOperands(operands);
            return true;
        }

        // Scalar FCM* write a boolean mask into an FP register: all-ones when
        // the ordered comparison holds, zero otherwise. Check* yields 0/1 —
        // negating it produces the mask. FCMGE/FCMLE are composite
        // (a>b)|(a==b) / (a<b)|(a==b) so unordered input masks to zero, which
        // the emitted ordered compares already guarantee on NaN.
        void EmitScalarCompareMask()
        {
            var compareDest = ConvertOperand(instruction, 0);
            var left = ConvertOperand(instruction, 1);
            IOperand right;
            if (instruction.Op2Kind == Arm64OperandKind.FloatingPointImmediate)
                right = instruction.Op0Reg is >= Arm64Register.D0 and <= Arm64Register.D31
                    ? new DoubleLiteral(0)
                    : new FloatLiteral(0f);
            else if (instruction.Op2Kind == Arm64OperandKind.Register)
                right = ConvertOperand(instruction, 2);
            else
            {
                Add(address, OpCode.NotImplemented,
                    new StringLiteral($"Instruction {instruction.Mnemonic} form is not supported."));
                return;
            }

            var mask = new Register(null, "TEMP_CMP");
            Add(address, instruction.Mnemonic is Arm64Mnemonic.FCMLT or Arm64Mnemonic.FCMLE
                ? OpCode.CheckLess
                : instruction.Mnemonic == Arm64Mnemonic.FCMEQ ? OpCode.CheckEqual : OpCode.CheckGreater,
                mask, left, right);
            if (instruction.Mnemonic is Arm64Mnemonic.FCMGE or Arm64Mnemonic.FCMLE)
            {
                var equal = new Register(null, "TEMP_CMP2");
                Add(address, OpCode.CheckEqual, equal, left, right);
                Add(address, OpCode.Or, mask, mask, equal);
            }
            // Pin the mask Int32: the Check* seed types its 0/1 result
            // Boolean, and a Boolean-typed mask would evaluate `and` as
            // 1 & n where the hardware mask is all-ones.
            Add(address, OpCode.Negate, compareDest, mask).NativeIntegerWidthBits = 32;
        }

        var preserveAdrpOffset = false;
        scalarizer.BeginInstruction(address);
        // lane-wise SIMD chains (DUP broadcast + following integer lanes) are
        // scalarized by the helper when lane provenance is fully proven; it
        // returns false for anything it cannot prove, leaving the normal path
        if (!scalarizer.TryConvert(instruction, Add, ConvertOperand))
            switch (instruction.Mnemonic)
        {
            case Arm64Mnemonic.FRINTM:
            case Arm64Mnemonic.FRINTP:
            case Arm64Mnemonic.FSQRT:
            case Arm64Mnemonic.FABS:
                {
                    var destination = ConvertOperand(instruction, 0);
                    var source = ConvertOperand(instruction, 1);
                    if (!IsScalarFloatRegister(instruction.Op0Reg))
                    {
                        Add(address, OpCode.NotImplemented, new StringLiteral($"Instruction {instruction.Mnemonic} vector form is not supported."));
                        break;
                    }

                    var name = instruction.Mnemonic switch
                    {
                        Arm64Mnemonic.FRINTM => "Floor",
                        Arm64Mnemonic.FRINTP => "Ceiling",
                        Arm64Mnemonic.FSQRT => "Sqrt",
                        _ => "Abs"
                    };
                    EmitMathUnary(name, destination, source, instruction.Op0Reg is >= Arm64Register.D0 and <= Arm64Register.D31);
                    break;
                }
            case Arm64Mnemonic.FABD:
                {
                    var destination = ConvertOperand(instruction, 0);
                    if (!IsScalarFloatRegister(instruction.Op0Reg))
                    {
                        Add(address, OpCode.NotImplemented, new StringLiteral("Instruction FABD vector form is not supported."));
                        break;
                    }

                    var difference = new Register(null, "TEMP_FABD");
                    Add(address, OpCode.Subtract, difference, ConvertOperand(instruction, 1), ConvertOperand(instruction, 2));
                    EmitMathUnary("Abs", destination, difference, instruction.Op0Reg is >= Arm64Register.D0 and <= Arm64Register.D31);
                    break;
                }
            case Arm64Mnemonic.FMAXNM:
            case Arm64Mnemonic.FMINNM:
                {
                    if (!IsScalarFloatRegister(instruction.Op0Reg))
                    {
                        Add(address, OpCode.NotImplemented,
                            new StringLiteral($"Instruction {instruction.Mnemonic} vector form is not supported."));
                        break;
                    }

                    EmitMathBinary(instruction.Mnemonic == Arm64Mnemonic.FMAXNM ? "Max" : "Min",
                        ConvertOperand(instruction, 0), ConvertOperand(instruction, 1), ConvertOperand(instruction, 2),
                        instruction.Op0Reg is >= Arm64Register.D0 and <= Arm64Register.D31);
                    break;
                }
            case Arm64Mnemonic.DUP:
                if (instruction.Op0Arrangement == Arm64ArrangementSpecifier.FourS
                    && UnityVector4()?.Methods.FirstOrDefault(candidate => candidate is
                        { Name: "get_one", IsStatic: true, Parameters.Count: 0 }) is { } getOne)
                {
                    var one = new Register(null, "TEMP_VECTOR_ONE");
                    Add(address, OpCode.Call, getOne, one);
                    if (!EmitVector4Call("op_Multiply", ConvertOperand(instruction, 0), one, ConvertOperand(instruction, 1)))
                        Add(address, OpCode.NotImplemented, new StringLiteral("UnityEngine.Vector4.op_Multiply is unavailable."));
                }
                else if (!scalarizer.TryBroadcastDup(instruction, Add, ConvertOperand))
                    Add(address, OpCode.NotImplemented, new StringLiteral("Instruction DUP vector broadcast is not supported."));
                break;
            case Arm64Mnemonic.FADDP:
                // the vector pairwise form is lane-wise and handled by the
                // scalarizer's TryConvert above; here is the scalar reduction
                // FADDP Sd/Dd, Vn.2S/2D, which only folds when both lanes are
                // honest float carriers (element locals or constants) — an
                // LDR D may carry a managed Vector2/aggregate and cannot be
                // sliced into lanes by shifting the register local.
                if (!scalarizer.TryScalarFaddp(instruction, Add, ConvertOperand))
                    Add(address, OpCode.NotImplemented, new StringLiteral("Instruction FADDP not yet implemented."));
                break;
            case Arm64Mnemonic.FCMGT:
            case Arm64Mnemonic.FCMLT:
            case Arm64Mnemonic.FCMGE:
            case Arm64Mnemonic.FCMLE:
            case Arm64Mnemonic.FCMEQ:
                if (IsScalarFloatRegister(instruction.Op0Reg))
                {
                    EmitScalarCompareMask();
                    break;
                }
                var recordsVector4Compare = instruction.Op0Arrangement == Arm64ArrangementSpecifier.FourS
                    && instruction.Mnemonic is Arm64Mnemonic.FCMGT or Arm64Mnemonic.FCMLT;
                if (recordsVector4Compare)
                    vectorComparisons![NormalizeRegister(instruction.Op0Reg)] =
                        (instruction.Mnemonic == Arm64Mnemonic.FCMGT,
                            ConvertOperand(instruction, 1), ConvertOperand(instruction, 2));
                if (scalarizer.TryCompareMask(instruction, Add, ConvertOperand))
                    break;
                // a recorded 4S comparison may still feed a Vector4 min/max
                // select; the rest reports an honest diagnostic
                Add(address, recordsVector4Compare ? OpCode.Nop : OpCode.NotImplemented,
                    recordsVector4Compare
                        ? []
                        : [new StringLiteral($"Instruction {instruction.Mnemonic} not yet implemented.")]);
                break;
            case Arm64Mnemonic.MOV:
            case Arm64Mnemonic.MOVZ:
            case Arm64Mnemonic.FMOV:
            case Arm64Mnemonic.SXTB:
            case Arm64Mnemonic.SXTH:
            case Arm64Mnemonic.SXTW:
            case Arm64Mnemonic.UXTB:
            case Arm64Mnemonic.UXTH:
            // conversions are moves for analysis purposes, same as the x86 handling of cvt*
            case Arm64Mnemonic.FCVT:
            case Arm64Mnemonic.FCVTZS:
            case Arm64Mnemonic.FCVTZU:
            case Arm64Mnemonic.FCVTMS:
            case Arm64Mnemonic.FCVTMU:
            case Arm64Mnemonic.FCVTNS:
            case Arm64Mnemonic.FCVTNU:
            case Arm64Mnemonic.FCVTPS:
            case Arm64Mnemonic.FCVTPU:
            case Arm64Mnemonic.FCVTAS:
            case Arm64Mnemonic.FCVTAU:
            case Arm64Mnemonic.SCVTF:
            case Arm64Mnemonic.UCVTF:
                if (instruction.Op0Kind == Arm64OperandKind.Register && IsReg31(instruction.Op0Reg))
                {
                    Add(address, OpCode.Nop); // write to xzr, discard
                    break;
                }

                Add(address, OpCode.Move, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            case Arm64Mnemonic.MOVI:
            case Arm64Mnemonic.MVNI when instruction.Op1Kind == Arm64OperandKind.Immediate:
                {
                    // MOVI Vn.{2,4}S, #imm, LSL #shift materializes the same
                    // IEEE-754 bit pattern in every lane. Keeping only #imm
                    // turns 0.5f (0x3f << 24) into integer 63 and poisons every
                    // following vector multiply.
                    if (instruction.Op0Arrangement is Arm64ArrangementSpecifier.TwoS
                        or Arm64ArrangementSpecifier.FourS)
                    {
                        var bits = unchecked((uint)instruction.Op1Imm << (int)instruction.Op2Imm);
                        if (instruction.Mnemonic == Arm64Mnemonic.MVNI)
                            bits = ~bits;
                        var laneValue = BitConverter.Int32BitsToSingle(unchecked((int)bits));
                        Add(address, OpCode.Move, ConvertOperand(instruction, 0),
                            new Vector128Literal(laneValue, laneValue, laneValue, laneValue));
                        break;
                    }
                    var value = instruction.Mnemonic == Arm64Mnemonic.MVNI ? ~instruction.Op1Imm : instruction.Op1Imm;
                    Add(address, OpCode.Move, ConvertOperand(instruction, 0), Imm(value));
                    break;
                }
            case Arm64Mnemonic.MOVK:
                // inserts a 16-bit chunk, which after the movz that always precedes it is just an or
                Add(address, OpCode.Or, ConvertOperand(instruction, 0), ConvertOperand(instruction, 0), Imm(instruction.Op1Imm));
                break;
            case Arm64Mnemonic.MOVN:
                {
                    var temp = new Register(null, "TEMP");
                    Add(address, OpCode.Move, temp, ConvertOperand(instruction, 1));
                    Add(address, OpCode.Not, temp, temp);
                    Add(address, OpCode.Move, ConvertOperand(instruction, 0), temp);
                    break;
                }
            case Arm64Mnemonic.MVN:
                Add(address, OpCode.Not, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            case Arm64Mnemonic.ADR:
                Add(address, OpCode.Move, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1))
                    .NativeIntegerWidthBits = context.AppContext.Binary.PointerSizeBytes * 8;
                break;
            case Arm64Mnemonic.ADRP:
                {
                    var target = (long)(address & ~0xFFFUL) + instruction.Op1Imm;
                    Add(address, OpCode.Move, ConvertOperand(instruction, 0), Imm(target))
                        .NativeIntegerWidthBits = context.AppContext.Binary.PointerSizeBytes * 8;
                    adrpOffsets![NormalizeRegister(instruction.Op0Reg)] = (ulong)target;
                    break;
                }
            case Arm64Mnemonic.LDR:
            case Arm64Mnemonic.LDRB:
            case Arm64Mnemonic.LDRH:
            case Arm64Mnemonic.LDRSB:
            case Arm64Mnemonic.LDRSH:
            case Arm64Mnemonic.LDRSW:
            case Arm64Mnemonic.LDUR:
            case Arm64Mnemonic.LDURB:
            case Arm64Mnemonic.LDURH:
            case Arm64Mnemonic.LDURSB:
            case Arm64Mnemonic.LDURSH:
            case Arm64Mnemonic.LDURSW:
                {
                    EmitWriteback(beforeAccess: true);

                    var loadSize = instruction.Mnemonic switch
                    {
                        Arm64Mnemonic.LDRB or Arm64Mnemonic.LDRSB or Arm64Mnemonic.LDURB or Arm64Mnemonic.LDURSB => 1,
                        Arm64Mnemonic.LDRH or Arm64Mnemonic.LDRSH or Arm64Mnemonic.LDURH or Arm64Mnemonic.LDURSH => 2,
                        Arm64Mnemonic.LDRSW or Arm64Mnemonic.LDURSW => 4,
                        _ => RegisterWidthBytes(instruction.Op0Reg)
                    };

                    // ldr with a pc-relative literal is an absolute load
                    var source = instruction.Op1Kind == Arm64OperandKind.ImmediatePcRelative
                        ? new MemoryOperand(addend: (long)address + instruction.Op1Imm, accessSize: loadSize)
                        : MemOperand(accessSize: loadSize);

                    if (source is MemoryOperand { IsConstant: true } constant
                        && context.AppContext.Binary is ElfFile elf
                        && elf.IsReadOnlyRange((ulong)constant.Addend, loadSize)
                        && context.AppContext.Binary.TryMapVirtualAddressToRaw((ulong)constant.Addend, out var raw))
                    {
                        var bytes = context.AppContext.Binary.GetRawBinaryContent().Slice((int)raw, loadSize).ToArray();
                        if (IsScalarFloatRegister(instruction.Op0Reg))
                            source = loadSize == 4
                                ? new FloatLiteral(BitConverter.ToSingle(bytes, 0))
                                : new DoubleLiteral(BitConverter.ToDouble(bytes, 0));
                        else if (loadSize == 16)
                            source = new Vector128Literal(
                                BitConverter.ToSingle(bytes, 0), BitConverter.ToSingle(bytes, 4),
                                BitConverter.ToSingle(bytes, 8), BitConverter.ToSingle(bytes, 12));
                    }

                    if (instruction.Op0Kind == Arm64OperandKind.Register && IsReg31(instruction.Op0Reg))
                        Add(address, OpCode.Nop); // load to xzr = prefetch, discard
                    else
                        Add(address, OpCode.Move, ConvertOperand(instruction, 0), source)
                            .NativeMemoryAccessSize = loadSize;

                    EmitWriteback(beforeAccess: false);
                    break;
                }
            case Arm64Mnemonic.STR:
            case Arm64Mnemonic.STRB:
            case Arm64Mnemonic.STRH:
            case Arm64Mnemonic.STUR:
            case Arm64Mnemonic.STURB:
            case Arm64Mnemonic.STURH:
            {
                var storeSize = instruction.Mnemonic switch
                {
                    Arm64Mnemonic.STRB or Arm64Mnemonic.STURB => 1,
                    Arm64Mnemonic.STRH or Arm64Mnemonic.STURH => 2,
                    _ => instruction.Op0Reg switch
                    {
                        >= Arm64Register.X0 and <= Arm64Register.X31 => 8,
                        >= Arm64Register.W0 and <= Arm64Register.W31 => 4,
                        _ => 0 // SIMD stores are not managed-reference writes.
                    }
                };
                EmitWriteback(beforeAccess: true);
                Add(address, OpCode.Move, MemOperand(accessSize: storeSize), ConvertOperand(instruction, 0))
                    .NativeMemoryAccessSize = storeSize;
                EmitWriteback(beforeAccess: false);
                break;
            }
            case Arm64Mnemonic.LDP:
            case Arm64Mnemonic.LDPSW:
            case Arm64Mnemonic.STP:
                {
                    var pairSize = instruction.Op0Reg switch
                    {
                        >= Arm64Register.V0 and <= Arm64Register.V31 => 16,
                        >= Arm64Register.D0 and <= Arm64Register.D31 => 8,
                        >= Arm64Register.S0 and <= Arm64Register.S31 => 4,
                        >= Arm64Register.W0 and <= Arm64Register.W31 => 4,
                        _ => 8
                    };

                    EmitWriteback(beforeAccess: true);

                    if (instruction.Mnemonic == Arm64Mnemonic.STP)
                    {
                        var storeSize = instruction.Op0Reg is >= Arm64Register.X0 and <= Arm64Register.X31
                            or >= Arm64Register.W0 and <= Arm64Register.W31 ? pairSize : 0;
                        Add(address, OpCode.Move, MemOperand(accessSize: storeSize), ConvertOperand(instruction, 0))
                            .NativeMemoryAccessSize = storeSize;
                        Add(address, OpCode.Move, MemOperand(pairSize, storeSize), ConvertOperand(instruction, 1))
                            .NativeMemoryAccessSize = storeSize;
                    }
                    else
                    {
                        Add(address, OpCode.Move, ConvertOperand(instruction, 0), MemOperand(accessSize: pairSize))
                            .NativeMemoryAccessSize = pairSize;
                        Add(address, OpCode.Move, ConvertOperand(instruction, 1), MemOperand(pairSize, pairSize))
                            .NativeMemoryAccessSize = pairSize;
                    }

                    EmitWriteback(beforeAccess: false);
                    break;
                }
            case Arm64Mnemonic.ADD:
            case Arm64Mnemonic.SUB:
            case Arm64Mnemonic.ADDS:
            case Arm64Mnemonic.SUBS:
                {
                    var isSubtract = instruction.Mnemonic is Arm64Mnemonic.SUB or Arm64Mnemonic.SUBS;
                    var setsFlags = instruction.Mnemonic is Arm64Mnemonic.ADDS or Arm64Mnemonic.SUBS;

                    // stack pointer adjustment
                    if (IsReg31(instruction.Op0Reg) && IsReg31(instruction.Op1Reg) && instruction.Op2Kind == Arm64OperandKind.Immediate && !setsFlags)
                    {
                        Add(address, OpCode.ShiftStack, Imm(isSubtract ? -instruction.Op2Imm : instruction.Op2Imm));
                        break;
                    }

                    // in the immediate forms register 31 is sp, so this takes the address of a stack slot
                    if (IsReg31(instruction.Op1Reg) && instruction.Op2Kind == Arm64OperandKind.Immediate && !IsReg31(instruction.Op0Reg))
                    {
                        var slot = new StackOffset((int)(isSubtract ? -instruction.Op2Imm : instruction.Op2Imm));
                        Add(address, OpCode.Move, ConvertOperand(instruction, 0), new AddressOf(slot));
                        break;
                    }

                    // ADRP + ADD forms the exact address of a metadata/global slot. Keeping
                    // the page base as ordinary integer arithmetic lets metadata resolution
                    // mistake a different slot at the start of the page for this address.
                    if (!isSubtract && instruction.Op2Kind == Arm64OperandKind.Immediate
                        && adrpOffsets!.TryGetValue(NormalizeRegister(instruction.Op1Reg), out var page))
                    {
                        var target = page + ((ulong)instruction.Op2Imm << (int)instruction.Op3Imm);
                        Add(address, OpCode.Move, ConvertOperand(instruction, 0), Imm((long)target))
                            .NativeIntegerWidthBits = context.AppContext.Binary.PointerSizeBytes * 8;
                        adrpOffsets[NormalizeRegister(instruction.Op0Reg)] = target;
                        preserveAdrpOffset = true;
                        break;
                    }

                    var src1 = ConvertOperand(instruction, 1);
                    var src2 = ConvertOperand(instruction, 2);
                    if (instruction.FinalOpExtendType == Arm64ExtendType.SXTW
                        && instruction.Op0Reg is >= Arm64Register.X0 and <= Arm64Register.X30)
                    {
                        var extended = new Register(null, "TEMP_EXTEND");
                        Add(address, OpCode.SignExtend32, extended, src2);
                        src2 = extended;
                    }
                    if (instruction.Op3Imm != 0)
                    {
                        var shifted = new Register(null, "TEMP_SHIFT");
                        Add(address, OpCode.ShiftLeft, shifted, src2, Imm(instruction.Op3Imm));
                        src2 = shifted;
                    }
                    // a discarded result means this is only about the flags
                    var dest = IsReg31(instruction.Op0Reg) ? new Register(null, "TEMP") : ConvertOperand(instruction, 0);

                    // A following numeric conversion is still represented as a Move and can
                    // coalesce back into this result, so direct ADD/SUB width is not stable yet.
                    Add(address, isSubtract ? OpCode.Subtract : OpCode.Add, dest, src1, src2);

                    if (setsFlags)
                    {
                        if (isSubtract)
                            EmitCompareFlags(src1, src2);
                        else
                            EmitResultFlags(dest);
                    }

                    break;
                }
            case Arm64Mnemonic.CMP:
            case Arm64Mnemonic.FCMP:
            case Arm64Mnemonic.FCMPE:
                EmitCompareFlags(ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            case Arm64Mnemonic.CMN:
                // cmp against the negated operand
                if (instruction.Op1Kind == Arm64OperandKind.Immediate)
                {
                    EmitCompareFlags(ConvertOperand(instruction, 0), Imm(-instruction.Op1Imm));
                }
                else
                {
                    var negated = new Register(null, "TEMP");
                    AddInteger(address, OpCode.Negate, negated, ConvertOperand(instruction, 1));
                    EmitCompareFlags(ConvertOperand(instruction, 0), negated);
                }

                break;
            case Arm64Mnemonic.TST:
                {
                    var temp = new Register(null, "TEMP");
                    AddInteger(address, OpCode.And, temp, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                    EmitResultFlags(temp);
                    break;
                }
            case Arm64Mnemonic.AND:
            case Arm64Mnemonic.ANDS:
            case Arm64Mnemonic.ORR:
            case Arm64Mnemonic.EOR:
                {
                    var opCode = instruction.Mnemonic switch
                    {
                        Arm64Mnemonic.ORR => OpCode.Or,
                        Arm64Mnemonic.EOR => OpCode.Xor,
                        _ => OpCode.And
                    };

                    var dest = IsReg31(instruction.Op0Reg) ? new Register(null, "TEMP") : ConvertOperand(instruction, 0);
                    var right = EmitLogicalShiftedOperand();
                    if (right == null)
                    {
                        Add(address, OpCode.NotImplemented, new StringLiteral($"{instruction.Mnemonic} shift {instruction.Op3ShiftType} is not supported."));
                        break;
                    }
                    AddInteger(address, opCode, dest, ConvertOperand(instruction, 1), right);

                    if (instruction.Mnemonic == Arm64Mnemonic.ANDS)
                        EmitResultFlags(dest);

                    break;
                }
            case Arm64Mnemonic.BIT:
            case Arm64Mnemonic.BIF:
            case Arm64Mnemonic.BSL:
                if (instruction.Mnemonic == Arm64Mnemonic.BIF
                    && instruction.Op0Arrangement == Arm64ArrangementSpecifier.SixteenB
                    && vectorComparisons!.TryGetValue(NormalizeRegister(instruction.Op2Reg), out var upper)
                    && upper.Greater)
                {
                    Add(address, OpCode.VectorMin, ConvertOperand(instruction, 0), upper.Value, upper.Bound);
                    break;
                }
                if (!scalarizer.TryBitSelect(instruction, Add, ConvertOperand))
                    Add(address, OpCode.NotImplemented, new StringLiteral($"Instruction {instruction.Mnemonic} not yet implemented."));
                break;
            case Arm64Mnemonic.BIC:
            case Arm64Mnemonic.BICS:
            case Arm64Mnemonic.ORN:
            case Arm64Mnemonic.EON:
                {
                    if (instruction.Mnemonic == Arm64Mnemonic.BIC
                        && instruction.Op0Arrangement == Arm64ArrangementSpecifier.SixteenB
                        && vectorComparisons!.TryGetValue(NormalizeRegister(instruction.Op2Reg), out var lower)
                        && !lower.Greater
                        && UnityVector4()?.Methods.FirstOrDefault(candidate => candidate is
                            { Name: "get_zero", IsStatic: true, Parameters.Count: 0 }) is { } getZero)
                    {
                        var zero = new Register(null, "TEMP_VECTOR_ZERO");
                        Add(address, OpCode.Call, getZero, zero);
                        Add(address, OpCode.VectorMax, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1), zero);
                        break;
                    }
                    var temp = new Register(null, "TEMP");
                    var shiftedOperand = EmitLogicalShiftedOperand();
                    if (shiftedOperand == null)
                    {
                        Add(address, OpCode.NotImplemented, new StringLiteral($"{instruction.Mnemonic} shift {instruction.Op3ShiftType} is not supported."));
                        break;
                    }

                    Add(address, OpCode.Not, temp, shiftedOperand);
                    var opCode = instruction.Mnemonic switch
                    {
                        Arm64Mnemonic.ORN => OpCode.Or,
                        Arm64Mnemonic.EON => OpCode.Xor,
                        _ => OpCode.And
                    };
                    var dest = IsReg31(instruction.Op0Reg) ? new Register(null, "TEMP") : ConvertOperand(instruction, 0);
                    AddInteger(address, opCode, dest, ConvertOperand(instruction, 1), temp);

                    if (instruction.Mnemonic == Arm64Mnemonic.BICS)
                        EmitResultFlags(dest);

                    break;
                }
            case Arm64Mnemonic.CCMP:
            case Arm64Mnemonic.CCMN:
            case Arm64Mnemonic.FCCMP:
            case Arm64Mnemonic.FCCMPE:
                {
                    // if cond holds the flags come from the comparison, else straight from the nzcv immediate
                    var inverse = new Register(null, "TEMPCSEL");
                    Add(address, OpCode.Not, inverse, EmitCondition(instruction.FinalOpConditionCode));
                    Add(address, OpCode.ConditionalJump, Imm(address + 1), inverse);

                    var op1 = ConvertOperand(instruction, 1);
                    if (instruction.Mnemonic == Arm64Mnemonic.CCMN)
                    {
                        var negated = new Register(null, "TEMP");
                        Add(address, OpCode.Negate, negated, op1);
                        op1 = negated;
                    }

                    EmitCompareFlags(ConvertOperand(instruction, 0), op1);
                    Add(address, OpCode.Jump, Imm(address + 2));

                    var nzcv = instruction.Op2Imm;
                    Add(address + 1, OpCode.Move, flagN, Imm((nzcv >> 3) & 1));
                    Add(address + 1, OpCode.Move, flagZ, Imm((nzcv >> 2) & 1));
                    Add(address + 1, OpCode.Move, flagC, Imm((nzcv >> 1) & 1));
                    Add(address + 1, OpCode.Move, flagV, Imm(nzcv & 1));

                    Add(address + 2, OpCode.Nop);
                    break;
                }
            case Arm64Mnemonic.NEG:
            case Arm64Mnemonic.FNEG:
                AddInteger(address, OpCode.Negate, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1));
                break;
            case Arm64Mnemonic.LSL:
                AddInteger(address, OpCode.ShiftLeft, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1), ConvertOperand(instruction, 2));
                break;
            case Arm64Mnemonic.LSR:
            case Arm64Mnemonic.ASR:
                AddInteger(address, OpCode.ShiftRight, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1), ConvertOperand(instruction, 2));
                break;
            case Arm64Mnemonic.UBFX:
            case Arm64Mnemonic.SBFX:
                {
                    // dest = (src >> lsb) & ((1 << width) - 1)
                    var dest = ConvertOperand(instruction, 0);
                    AddInteger(address, OpCode.ShiftRight, dest, ConvertOperand(instruction, 1), Imm(instruction.Op2Imm));
                    AddInteger(address, OpCode.And, dest, dest, Imm((1L << (int)instruction.Op3Imm) - 1));
                    break;
                }
            case Arm64Mnemonic.UBFIZ:
            case Arm64Mnemonic.SBFIZ:
                {
                    // dest = (src & ((1 << width) - 1)) << shift
                    var dest = ConvertOperand(instruction, 0);
                    var temp = new Register(null, "TEMP");
                    AddInteger(address, OpCode.And, temp, ConvertOperand(instruction, 1), Imm((1L << (int)instruction.Op3Imm) - 1));
                    AddInteger(address, OpCode.ShiftLeft, dest, temp, Imm(instruction.Op2Imm));
                    break;
                }
            case Arm64Mnemonic.MUL:
            case Arm64Mnemonic.FMUL:
            case Arm64Mnemonic.SMULL:
            case Arm64Mnemonic.UMULL:
                // Integer-to-float conversions are still represented as moves and can be
                // coalesced into this result, so a direct MUL width is not yet stable here.
                Add(address, OpCode.Multiply, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1), ConvertOperand(instruction, 2));
                break;
            case Arm64Mnemonic.MNEG:
            case Arm64Mnemonic.SMNEGL:
            case Arm64Mnemonic.UMNEGL:
            case Arm64Mnemonic.FNMUL:
                {
                    var dest = ConvertOperand(instruction, 0);
                    AddInteger(address, OpCode.Multiply, dest, ConvertOperand(instruction, 1), ConvertOperand(instruction, 2));
                    AddInteger(address, OpCode.Negate, dest, dest);
                    break;
                }
            case Arm64Mnemonic.MADD:
            case Arm64Mnemonic.MSUB:
            case Arm64Mnemonic.SMADDL:
            case Arm64Mnemonic.UMADDL:
            case Arm64Mnemonic.SMSUBL:
            case Arm64Mnemonic.UMSUBL:
                {
                    // rd = ra +/- rn * rm
                    var isAdd = instruction.Mnemonic is Arm64Mnemonic.MADD or Arm64Mnemonic.SMADDL or Arm64Mnemonic.UMADDL;
                    var temp = new Register(null, "TEMP");
                    AddInteger(address, OpCode.Multiply, temp, ConvertOperand(instruction, 1), ConvertOperand(instruction, 2));
                    AddInteger(address, isAdd ? OpCode.Add : OpCode.Subtract, ConvertOperand(instruction, 0), ConvertOperand(instruction, 3), temp);
                    break;
                }
            case Arm64Mnemonic.EXTR:
                {
                    // dest = (rn:rm) >> lsb
                    var dest = ConvertOperand(instruction, 0);
                    var lsb = instruction.Op3Imm;

                    if (lsb == 0)
                    {
                        Add(address, OpCode.Move, dest, ConvertOperand(instruction, 2));
                        break;
                    }

                    var regSize = instruction.Op0Reg is >= Arm64Register.X0 and <= Arm64Register.X31 ? 64 : 32;
                    var temp = new Register(null, "TEMP");
                    var temp2 = new Register(null, "TEMP2");
                    AddInteger(address, OpCode.ShiftRight, temp, ConvertOperand(instruction, 2), Imm(lsb));
                    AddInteger(address, OpCode.ShiftLeft, temp2, ConvertOperand(instruction, 1), Imm(regSize - lsb));
                    AddInteger(address, OpCode.Or, dest, temp, temp2);
                    break;
                }
            case Arm64Mnemonic.SDIV:
            case Arm64Mnemonic.UDIV:
            case Arm64Mnemonic.FDIV:
                AddInteger(address, OpCode.Divide, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1), ConvertOperand(instruction, 2));
                break;
            case Arm64Mnemonic.FADD:
                Add(address, OpCode.Add, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1), ConvertOperand(instruction, 2));
                break;
            case Arm64Mnemonic.FSUB:
                Add(address, OpCode.Subtract, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1), ConvertOperand(instruction, 2));
                break;
            case Arm64Mnemonic.BL:
                AddCallAt(instruction.BranchTarget);
                break;
            case Arm64Mnemonic.BLR:
                {
                    var call = Add(address, OpCode.IndirectCall, ConvertOperand(instruction, 0), new Register(null, "X0") /* return value */);
                    call.AddOperands(CallingConventions.ResolveForUnmanaged(context.AppContext, address));
                    break;
                }
            case Arm64Mnemonic.BR:
                {
                    // tail call or jump table, either way it leaves the method
                    var jump = Add(address, OpCode.IndirectJump, ConvertOperand(instruction, 0), new Register(null, "X0") /* return value */);
                    jump.AddOperands(CallingConventions.ResolveForUnmanaged(context.AppContext, address));
                    break;
                }
            case Arm64Mnemonic.B:
            case Arm64Mnemonic.BC:
                {
                    var target = instruction.Mnemonic == Arm64Mnemonic.B ? instruction.BranchTarget : instruction.Op0PcRelImm;

                    if (instruction.MnemonicConditionCode != Arm64ConditionCode.NONE
                        && instruction.MnemonicConditionCode != Arm64ConditionCode.AL
                        && instruction.MnemonicConditionCode != Arm64ConditionCode.NV)
                    {
                        Add(address, OpCode.ConditionalJump, Imm(target), EmitCondition(instruction.MnemonicConditionCode));
                        break;
                    }

                    if (target < context.UnderlyingPointer || target >= context.UnderlyingPointer + (ulong)context.RawBytes.Length)
                    {
                        // unconditional branch out of the method is a tail call
                        AddCallAt(target);
                        AddReturn();
                    }
                    else
                    {
                        Add(address, OpCode.Jump, Imm(target));
                    }

                    break;
                }
            case Arm64Mnemonic.RET:
            case Arm64Mnemonic.RETAA:
            case Arm64Mnemonic.RETAB:
                AddReturn();
                break;
            case Arm64Mnemonic.CBZ:
            case Arm64Mnemonic.CBNZ:
                {
                    var target = (ulong)((long)address + instruction.Op1Imm);
                    var temp = new Register(null, "TEMP");

                    Add(address, OpCode.CheckEqual, temp, ConvertOperand(instruction, 0), Imm(0));

                    if (instruction.Mnemonic == Arm64Mnemonic.CBNZ)
                        Add(address, OpCode.Not, temp, temp);

                    Add(address, OpCode.ConditionalJump, Imm(target), temp);
                    break;
                }
            case Arm64Mnemonic.TBZ:
            case Arm64Mnemonic.TBNZ:
                {
                    var target = (ulong)((long)address + instruction.Op2Imm);
                    var temp = new Register(null, "TEMP");

                    Add(address, OpCode.And, temp, ConvertOperand(instruction, 0), Imm(1L << (int)instruction.Op1Imm));
                    Add(address, OpCode.CheckEqual, temp, temp, Imm(0));

                    if (instruction.Mnemonic == Arm64Mnemonic.TBNZ)
                        Add(address, OpCode.Not, temp, temp);

                    Add(address, OpCode.ConditionalJump, Imm(target), temp);
                    break;
                }
            case Arm64Mnemonic.CSEL:
            case Arm64Mnemonic.FCSEL:
                EmitConditionalAssign(instruction.FinalOpConditionCode,
                    () => Add(address, OpCode.Move, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1)),
                    falseAddress => Add(falseAddress, OpCode.Move, ConvertOperand(instruction, 0), ConvertOperand(instruction, 2)));
                break;
            case Arm64Mnemonic.CSINC:
                EmitConditionalAssign(instruction.FinalOpConditionCode,
                    () => Add(address, OpCode.Move, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1)),
                    falseAddress => Add(falseAddress, OpCode.Add, ConvertOperand(instruction, 0), ConvertOperand(instruction, 2), Imm(1)));
                break;
            case Arm64Mnemonic.CSINV:
                EmitConditionalAssign(instruction.FinalOpConditionCode,
                    () => Add(address, OpCode.Move, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1)),
                    falseAddress => Add(falseAddress, OpCode.Not, ConvertOperand(instruction, 0), ConvertOperand(instruction, 2)));
                break;
            case Arm64Mnemonic.CSNEG:
                EmitConditionalAssign(instruction.FinalOpConditionCode,
                    () => Add(address, OpCode.Move, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1)),
                    falseAddress => Add(falseAddress, OpCode.Negate, ConvertOperand(instruction, 0), ConvertOperand(instruction, 2)));
                break;
            case Arm64Mnemonic.CSET:
                Add(address, OpCode.Move, ConvertOperand(instruction, 0), EmitCondition(instruction.FinalOpConditionCode));
                break;
            case Arm64Mnemonic.CSETM:
                EmitConditionalAssign(instruction.FinalOpConditionCode,
                    () => Add(address, OpCode.Move, ConvertOperand(instruction, 0), Imm(-1L)),
                    falseAddress => Add(falseAddress, OpCode.Move, ConvertOperand(instruction, 0), Imm(0)));
                break;
            case Arm64Mnemonic.CINC:
                EmitConditionalAssign(instruction.FinalOpConditionCode,
                    () => Add(address, OpCode.Add, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1), Imm(1)),
                    falseAddress => Add(falseAddress, OpCode.Move, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1)));
                break;
            case Arm64Mnemonic.CNEG:
                EmitConditionalAssign(instruction.FinalOpConditionCode,
                    () => Add(address, OpCode.Negate, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1)),
                    falseAddress => Add(falseAddress, OpCode.Move, ConvertOperand(instruction, 0), ConvertOperand(instruction, 1)));
                break;
            case Arm64Mnemonic.NOP:
            // pointer auth and branch target hints are meaningless for analysis but might be jump targets
            case Arm64Mnemonic.BTI:
            case Arm64Mnemonic.BTI_C:
            case Arm64Mnemonic.BTI_J:
            case Arm64Mnemonic.BTI_JC:
            case Arm64Mnemonic.PACIASP:
            case Arm64Mnemonic.PACIBSP:
            case Arm64Mnemonic.AUTIASP:
            case Arm64Mnemonic.AUTIBSP:
                Add(address, OpCode.Nop);
                break;
            case Arm64Mnemonic.BRK:
            case Arm64Mnemonic.UDF:
                Add(address, OpCode.Interrupt);
                break;
            case Arm64Mnemonic.MRS:
                // system register read (thread pointer etc), value is opaque to analysis
                Add(address, OpCode.Move, ConvertOperand(instruction, 0), new Register(null, "SYSREG"));
                break;
            default:
                Add(address, OpCode.NotImplemented, new StringLiteral($"Instruction {instruction.Mnemonic} not yet implemented."));
                break;
        }

        scalarizer.NoteUnhandled(instruction);

        // any register write invalidates a tracked ADRP page address (ADRP itself just set one)
        if (!preserveAdrpOffset && instruction.Mnemonic != Arm64Mnemonic.ADRP && instruction.Op0Kind == Arm64OperandKind.Register)
            adrpOffsets!.Remove(NormalizeRegister(instruction.Op0Reg));
        if (instruction.MemIndexMode != Arm64MemoryIndexMode.Offset && instruction.MemBase != Arm64Register.INVALID)
            adrpOffsets!.Remove(NormalizeRegister(instruction.MemBase));
    }

    private static bool IsThreadStaticDataHelper(ApplicationAnalysisContext context, ulong target)
    {
        var binary = context.Binary;
        var raw = (int)binary.MapVirtualAddressToRaw(target);
        var content = binary.GetRawBinaryContent();
        if (raw <= 0 || raw + 8 > content.Length)
            return false;
        try
        {
            var instructions = Disassembler.Disassemble(content.Slice(raw, 8), target,
                new Disassembler.Options(true, true, false)).ToList();
            return instructions.Count == 2
                && instructions[0] is { Mnemonic: Arm64Mnemonic.LDR, Op0Reg: Arm64Register.W0,
                    MemBase: Arm64Register.X0 }
                && instructions[1].Mnemonic == Arm64Mnemonic.B;
        }
        catch
        {
            return false;
        }
    }

    private IOperand ConvertOperand(Arm64Instruction instruction, int operand)
    {
        var kind = operand switch
        {
            0 => instruction.Op0Kind,
            1 => instruction.Op1Kind,
            2 => instruction.Op2Kind,
            3 => instruction.Op3Kind,
            _ => throw new ArgumentOutOfRangeException(nameof(operand), $"Operand must be between 0 and 3, inclusive. Got {operand}")
        };

        if (kind is Arm64OperandKind.Immediate or Arm64OperandKind.ImmediatePcRelative)
        {
            var imm = operand switch
            {
                0 => instruction.Op0Imm,
                1 => instruction.Op1Imm,
                2 => instruction.Op2Imm,
                3 => instruction.Op3Imm,
                _ => throw new ArgumentOutOfRangeException(nameof(operand), $"Operand must be between 0 and 3, inclusive. Got {operand}")
            };

            if (kind == Arm64OperandKind.ImmediatePcRelative)
                imm += (long)instruction.Address;

            if (kind == Arm64OperandKind.Immediate
                && instruction.Op0Kind == Arm64OperandKind.Register
                && IsWordRegister(instruction.Op0Reg)
                && imm is >= 0 and <= uint.MaxValue)
                imm = unchecked((int)(uint)imm);

            return new Immediate(imm);
        }

        if (kind == Arm64OperandKind.FloatingPointImmediate)
        {
            var imm = operand switch
            {
                0 => instruction.Op0FpImm,
                1 => instruction.Op1FpImm,
                2 => instruction.Op2FpImm,
                3 => instruction.Op3FpImm,
                _ => throw new ArgumentOutOfRangeException(nameof(operand), $"Operand must be between 0 and 3, inclusive. Got {operand}")
            };

            return new DoubleLiteral(imm);
        }

        if (kind == Arm64OperandKind.Register)
        {
            var reg = operand switch
            {
                0 => instruction.Op0Reg,
                1 => instruction.Op1Reg,
                2 => instruction.Op2Reg,
                3 => instruction.Op3Reg,
                _ => throw new ArgumentOutOfRangeException(nameof(operand), $"Operand must be between 0 and 3, inclusive. Got {operand}")
            };

            // reads of integer register 31 are the zero register (sp-based reads are special-cased by callers)
            if (IsReg31(reg))
                return new Immediate(0);

            return Reg(reg);
        }

        if (kind == Arm64OperandKind.Memory)
        {
            var reg = instruction.MemBase;
            var offset = instruction.MemOffset;

            if (reg == Arm64Register.INVALID)
                //Offset only
                return new MemoryOperand(addend: offset);

            if (IsReg31(reg))
                return new StackOffset((int)offset);

            return new MemoryOperand(Reg(reg), addend: offset);
        }

        if (kind == Arm64OperandKind.VectorRegisterElement)
        {
            var reg = operand switch
            {
                0 => instruction.Op0Reg,
                1 => instruction.Op1Reg,
                2 => instruction.Op2Reg,
                3 => instruction.Op3Reg,
                _ => throw new ArgumentOutOfRangeException(nameof(operand), $"Operand must be between 0 and 3, inclusive. Got {operand}")
            };

            var vectorElement = operand switch
            {
                0 => instruction.Op0VectorElement,
                1 => instruction.Op1VectorElement,
                2 => instruction.Op2VectorElement,
                3 => instruction.Op3VectorElement,
                _ => throw new ArgumentOutOfRangeException(nameof(operand), $"Operand must be between 0 and 3, inclusive. Got {operand}")
            };

            var width = vectorElement.Width switch
            {
                Arm64VectorElementWidth.B => "B",
                Arm64VectorElementWidth.H => "H",
                Arm64VectorElementWidth.S => "S",
                Arm64VectorElementWidth.D => "D",
                _ => throw new ArgumentOutOfRangeException(nameof(vectorElement.Width), $"Unknown vector element width {vectorElement.Width}")
            };

            var name = $"{NormalizeRegister(reg)}.{width}{vectorElement.Index}";
            return new Register(null, name);
        }

        return new StringLiteral($"<UNIMPLEMENTED OPERAND TYPE {kind}>");
    }

    public override BaseKeyFunctionAddresses CreateKeyFunctionAddressesInstance() => new NewArm64KeyFunctionAddresses();

    public override string PrintAssembly(MethodAnalysisContext context) => context.RawBytes.Length <= 0 ? "" : string.Join("\n", Disassembler.Disassemble(context.RawBytes.AsSpan(), context.UnderlyingPointer, new Disassembler.Options(true, true, false)).ToList());
}
