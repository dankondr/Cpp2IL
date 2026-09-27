using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Utils.AsmResolver;

/// <summary>
/// Restores framework-surface <b>members</b> that recovered typedefs do not
/// carry but that decompiled code names anyway.
///
/// IL2CPP strips literal fields it can fold (System.Math::PI/E) and helper
/// methods the managed world never calls directly
/// (System.Runtime.CompilerServices.Unsafe::InitBlock/CopyBlock,
/// System.Buffer::MemoryCopy, UnityEngine.VectorN::Max/Min), while the
/// reconstructed method bodies still name them: Cpp2IL emits initblk/cpblk and
/// VectorMin/VectorMax memberrefs for native memset/memcpy/vector
/// instructions, and the decompiler renders floating-point literals equal to
/// multiples of PI or E as Math.PI/Math.E from its own BCL knowledge.
///
/// Every emitted member is metadata-justified: it is a real member of the real
/// type in the reference BCL/UnityEngine surface, and the demand for it is read
/// from the recovered ISIL rather than assumed. Members carry real bodies where
/// one exists (initblk/cpblk for the block helpers, the component-wise
/// comparison Unity's Max/Min implement) rather than diagnostic stubs.
/// </summary>
internal static class FrameworkSurfaceMembers
{
    /// <summary>
    /// Scans the recovered method bodies for members named by the emitted IL
    /// but absent from the recovered typedefs, then emits them. Returns the
    /// number of members created.
    /// </summary>
    public static int EmitMissing(ApplicationAnalysisContext context, List<AssemblyDefinition> assemblies)
    {
        var corlibModule = assemblies
            .Select(assembly => assembly.ManifestModule)
            .FirstOrDefault(module => module is not null &&
                (module.Assembly?.Name == "mscorlib"
                 || module.TopLevelTypes.Any(type => type.FullName == "System.Object")));
        if (corlibModule == null)
            return 0;

        var demand = new Demand();
        ScanDemands(context, demand, assemblies);

        var emitted = 0;
        if (demand.MathPi || demand.MathE)
            emitted += EmitMathConstants(corlibModule, demand);
        if (demand.UnsafeInitBlock || demand.UnsafeCopyBlock)
            emitted += EmitUnsafeBlockOperations(corlibModule, demand);
        if (demand.BufferMemoryCopy)
            emitted += EmitBufferMemoryCopy(corlibModule);
        foreach (var (type, kind) in demand.VectorMinMax)
            emitted += EmitVectorMinMax(type, kind);

        return emitted;
    }

    private sealed class Demand
    {
        public bool MathPi;
        public bool MathE;
        public bool UnsafeInitBlock;
        public bool UnsafeCopyBlock;
        public bool BufferMemoryCopy;
        public readonly HashSet<(TypeDefinition Type, MinMaxKind Kind)> VectorMinMax = new();
    }

    private enum MinMaxKind
    {
        Min,
        Max,
    }

    // Reads demand from the materialized IL first — exactly what the
    // decompiler consumes — and additionally from any live ISIL graphs (the
    // analysis representation, still present for formats that do not fill
    // bodies and for methods the fill step did not release).
    private static void ScanDemands(ApplicationAnalysisContext context, Demand demand,
        List<AssemblyDefinition> assemblies)
    {
        foreach (var assembly in assemblies)
        {
            foreach (var module in assembly.Modules)
            {
                foreach (var type in module.GetAllTypes())
                {
                    foreach (var method in type.Methods)
                        ScanEmittedBody(method, demand, assemblies);
                }
            }
        }

        foreach (var assembly in context.Assemblies)
        {
            foreach (var type in assembly.Types)
            {
                foreach (var method in type.Methods)
                {
                    if (method.ControlFlowGraph == null)
                        continue;
                    foreach (var instruction in method.ControlFlowGraph.Instructions)
                    {
                        switch (instruction.OpCode)
                        {
                            case OpCode.MemorySet:
                                demand.UnsafeInitBlock = true;
                                break;
                            case OpCode.MemoryCopy:
                                demand.UnsafeCopyBlock = true;
                                break;
                            case OpCode.MemoryMove:
                                demand.BufferMemoryCopy = true;
                                break;
                            case OpCode.VectorMin:
                                RecordVectorDemand(instruction, method, demand, MinMaxKind.Min);
                                break;
                            case OpCode.VectorMax:
                                RecordVectorDemand(instruction, method, demand, MinMaxKind.Max);
                                break;
                        }
                        foreach (var operand in instruction.Operands)
                            ScanOperand(operand, demand);
                    }
                }
            }
        }
    }

    private static void ScanEmittedBody(MethodDefinition method, Demand demand,
        List<AssemblyDefinition> assemblies)
    {
        if (method.CilMethodBody is not { } body)
            return;
        foreach (var instruction in body.Instructions)
        {
            var opcode = instruction.OpCode;
            if (opcode == CilOpCodes.Initblk)
                demand.UnsafeInitBlock = true;
            else if (opcode == CilOpCodes.Cpblk)
                demand.UnsafeCopyBlock = true;
            else if (opcode == CilOpCodes.Ldc_R8 && instruction.Operand is double doubleValue)
            {
                if (RendersMathMember(doubleValue, isDouble: true, out var name))
                    MarkMathDemand(demand, name);
            }
            else if (opcode == CilOpCodes.Ldc_R4 && instruction.Operand is float floatValue)
            {
                if (RendersMathMember(floatValue, isDouble: false, out var name))
                    MarkMathDemand(demand, name);
            }
            else if (opcode == CilOpCodes.Call || opcode == CilOpCodes.Callvirt || opcode == CilOpCodes.Newobj)
            {
                var descriptor = instruction.Operand is MethodSpecification specification
                    ? specification.Method
                    : instruction.Operand as IMethodDescriptor;
                if (descriptor?.DeclaringType is not { } declaring)
                    continue;
                var memberName = descriptor.Name?.ToString();
                switch (declaring.FullName)
                {
                    case "System.Buffer" when memberName == "MemoryCopy":
                        demand.BufferMemoryCopy = true;
                        break;
                    case "UnityEngine.Vector2" or "UnityEngine.Vector3" or "UnityEngine.Vector4"
                        when memberName is "Min" or "Max":
                        var vectorType = declaring as TypeDefinition ?? assemblies
                            .SelectMany(assembly => assembly.Modules)
                            .SelectMany(module => module.GetAllTypes())
                            .FirstOrDefault(candidate => candidate.FullName == declaring.FullName);
                        if (vectorType != null)
                            demand.VectorMinMax.Add((vectorType,
                                memberName == "Min" ? MinMaxKind.Min : MinMaxKind.Max));
                        break;
                }
            }
        }
    }

    private static void ScanOperand(IOperand operand, Demand demand)
    {
        switch (operand)
        {
            case DoubleLiteral literal:
                if (RendersMathMember(literal.Value, isDouble: true, out var name))
                    MarkMathDemand(demand, name);
                break;
            case FloatLiteral literal:
                if (RendersMathMember(literal.Value, isDouble: false, out name))
                    MarkMathDemand(demand, name);
                break;
            case Vector128Literal vector:
                if (RendersMathMember(vector.X, isDouble: false, out name)) MarkMathDemand(demand, name);
                if (RendersMathMember(vector.Y, isDouble: false, out name)) MarkMathDemand(demand, name);
                if (RendersMathMember(vector.Z, isDouble: false, out name)) MarkMathDemand(demand, name);
                if (RendersMathMember(vector.W, isDouble: false, out name)) MarkMathDemand(demand, name);
                break;
            case AddressOf addressOf:
                ScanOperand(addressOf.Target, demand);
                break;
            case ArrayAccess access:
                ScanOperand(access.Index, demand);
                break;
            case ArrayElementFieldReference elementAccess:
                ScanOperand(elementAccess.Index, demand);
                break;
            case MemoryOperand memory:
                if (memory.Base != null)
                    ScanOperand(memory.Base, demand);
                if (memory.Index != null)
                    ScanOperand(memory.Index, demand);
                break;
            case ReferenceCast cast:
                ScanOperand(cast.Value, demand);
                break;
            case Instruction nested:
                foreach (var nestedOperand in nested.Operands)
                    ScanOperand(nestedOperand, demand);
                break;
        }
    }

    private static void MarkMathDemand(Demand demand, string name)
    {
        if (name == "PI")
            demand.MathPi = true;
        else
            demand.MathE = true;
    }

    private static void RecordVectorDemand(Instruction instruction, MethodAnalysisContext context,
        Demand demand, MinMaxKind kind)
    {
        // Same resolution the emitter applies: whatever operand carries the
        // Unity vector type picks the typedef the Min/Max call targets.
        var vector = instruction.Operands
            .Select(operand => IlGenerator.EmittedOperandType(operand, context))
            .FirstOrDefault(IsUnityVector);
        if (vector?.GetExtraData<TypeDefinition>("AsmResolverType") is { } definition)
            demand.VectorMinMax.Add((definition, kind));
    }

    private static bool IsUnityVector(TypeAnalysisContext? type)
        => type?.DefaultFullName is "UnityEngine.Vector2" or "UnityEngine.Vector3" or "UnityEngine.Vector4";

    // --- literal predicate (mirrors the decompiler's float conversion) ---

    private const int MaxDenominatorDouble = 1000;
    private const int MaxDenominatorFloat = 360;
    private const int RegularFractionDenominatorFloat = 200;
    private const float MathFPi = 3.14159274f;
    private const float MathFE = 2.71828175f;

    private static readonly int[] PreferredFractionDenominators =
    {
        127, 128, 255, 256, 1023, 1024, 4095, 4096, 8192, 16384, 32767, 32768, 65535, 65536, 1048576,
    };

    // True when the decompiler renders `value` as Math.<name> (name is "PI" or
    // "E"): the literal is non-integral, too long for a plain rendering, not
    // already an exact regular or preferred fraction, and equal to PI*n/d or
    // n/(d*PI) under an exact check. For floats the decompiler falls back to
    // System.Math whenever the imported MathF typedef lacks PI/E consts, so the
    // demanded member is always on System.Math.
    private static bool RendersMathMember(double value, bool isDouble, out string name)
    {
        name = "";
        if (isDouble)
        {
            if (Math.Floor(value) == value)
                return false;
        }
        else if (Math.Floor((float)value) == (float)value)
        {
            return false;
        }

        var str = isDouble
            ? value.ToString("r", CultureInfo.InvariantCulture)
            : ((float)value).ToString("r", CultureInfo.InvariantCulture);
        var useFraction = str.Length - (str.StartsWith("-", StringComparison.OrdinalIgnoreCase) ? 2 : 1) > 5;
        if (!useFraction)
            return false;

        var (num, den) = isDouble
            ? FractionApprox(value, MaxDenominatorDouble)
            : FractionApprox((float)value, RegularFractionDenominatorFloat);
        var hasRegularFraction = IsValidFraction(num, den)
            && IsEqual(num, den, value, isDouble)
            && Math.Abs(den) != 1;
        if (hasRegularFraction)
            return false;

        // A "preferred" machine-scale fraction (denominator a power of two or
        // 2^n-1) claims the literal before the PI/E path runs.
        if (TryGetPreferredFraction(value, isDouble, out _, out _, out var score)
            && score <= str.Length + (isDouble ? 0 : 1))
            return false;

        if (RendersMathConstant(value, isDouble, pi: true))
        {
            name = "PI";
            return true;
        }
        if (RendersMathConstant(value, isDouble, pi: false))
        {
            name = "E";
            return true;
        }
        return false;
    }

    private static bool RendersMathConstant(double value, bool isDouble, bool pi)
    {
        var maxDenominator = isDouble ? MaxDenominatorDouble : MaxDenominatorFloat;
        double field = isDouble ? (pi ? Math.PI : Math.E) : (pi ? MathFPi : MathFE);

        var (num, den) = isDouble
            ? FractionApprox(value / field, maxDenominator)
            : FractionApprox((float)value / (float)field, maxDenominator);
        if (IsValidFraction(num, den) && IsExtracted(value, isDouble, field, num, den))
            return true;

        (num, den) = isDouble
            ? FractionApprox(value * field, maxDenominator)
            : FractionApprox((float)value * (float)field, maxDenominator);
        return IsValidFraction(num, den) && IsExtracted(value, isDouble, field, num, den);
    }

    // The decompiler verifies `field * n / d == value` (rendered field*n/d)
    // and, failing that, `n / (d * field) == value` (rendered n/(d*field)).
    private static bool IsExtracted(double value, bool isDouble, double field, long n, long d)
    {
        if (isDouble)
            return field * n / d == value || n / (d * field) == value;
        return (float)field * n / d == (float)value || (float)n / (d * (float)field) == (float)value;
    }

    private static bool IsValidFraction(long num, long den)
    {
        if (!(den > 0 && num != 0))
            return false;
        if (den == 1 || Math.Abs(num) == 1)
            return true;
        return Math.Abs(num) < den && (den % 2 == 0 || den % 3 == 0 || den % 5 == 0);
    }

    private static bool IsEqual(long num, long den, double constantValue, bool isDouble)
        => isDouble
            ? constantValue == num / (double)den
            : (float)constantValue == num / (float)den;

    private static int GetIntegerLiteralLength(long value)
    {
        var length = value < 0 ? 1 : 0;
        do
        {
            length++;
            value /= 10;
        } while (value != 0);
        return length;
    }

    private static int GetFractionDisplayLength(long num, long den, bool isDouble)
        => GetIntegerLiteralLength(num) + GetIntegerLiteralLength(den) + 3 + 2 * (isDouble ? 2 : 1);

    private static int GetPreferredFractionScore(long num, long den, bool isDouble)
    {
        var isPowerOfTwo = (den & (den - 1)) == 0;
        var readabilityBonus = isPowerOfTwo ? 1 : 2;
        return GetFractionDisplayLength(num, den, isDouble) - readabilityBonus;
    }

    private static bool TryGetPreferredFraction(double constantValue, bool isDouble,
        out long num, out long den, out int score)
    {
        num = 0;
        den = 0;
        score = int.MaxValue;

        var value = isDouble ? constantValue : (float)constantValue;
        if (!(Math.Abs(value) < 1.0))
            return false;

        foreach (var candidateDen in PreferredFractionDenominators)
        {
            var candidateNum = (long)Math.Round(value * candidateDen);
            if (candidateNum == 0 || candidateNum <= -candidateDen || candidateNum >= candidateDen)
                continue;
            if (!IsEqual(candidateNum, candidateDen, constantValue, isDouble))
                continue;

            var candidateScore = GetPreferredFractionScore(candidateNum, candidateDen, isDouble);
            if (candidateScore < score || (candidateScore == score && candidateDen < den))
            {
                num = candidateNum;
                den = candidateDen;
                score = candidateScore;
            }
        }
        return score != int.MaxValue;
    }

    private static (long Num, long Den) FractionApprox(double value, int maxDenominator)
    {
        // Continued-fraction approximation.
        if (Math.Abs(value) > 0x7FFFFFFF)
            return (0, 0);

        var startValue = value;
        if (value < 0)
            value = -value;

        long ai;
        var m = new long[2, 2];
        m[0, 0] = m[1, 1] = 1;

        var v = value;
        while (m[1, 0] * (ai = (long)v) + m[1, 1] <= maxDenominator)
        {
            var t = m[0, 0] * ai + m[0, 1];
            m[0, 1] = m[0, 0];
            m[0, 0] = t;
            t = m[1, 0] * ai + m[1, 1];
            m[1, 1] = m[1, 0];
            m[1, 0] = t;
            if (v - ai == 0)
                break;
            v = 1 / (v - ai);
            if (Math.Abs(v) >= long.MaxValue)
                break;
        }

        if (m[1, 0] == 0)
            return (0, 0);

        var firstN = m[0, 0];
        var firstD = m[1, 0];

        ai = (maxDenominator - m[1, 1]) / m[1, 0];
        var secondN = m[0, 0] * ai + m[0, 1];
        var secondD = m[1, 0] * ai + m[1, 1];

        var firstDelta = Math.Abs(value - firstN / (double)firstD);
        var secondDelta = Math.Abs(value - secondN / (double)secondD);

        if (firstDelta < secondDelta)
            return (startValue < 0 ? -firstN : firstN, firstD);
        return (startValue < 0 ? -secondN : secondN, secondD);
    }

    // --- emission ---

    private static int EmitMathConstants(ModuleDefinition corlibModule, Demand demand)
    {
        var emitted = 0;
        var math = EnsureType(corlibModule, "System", "Math",
            TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed, ref emitted);
        var factory = corlibModule.CorLibTypeFactory;
        if (demand.MathPi)
            EnsureConstantField(math, "PI", factory.Double, Math.PI, ref emitted);
        if (demand.MathE)
            EnsureConstantField(math, "E", factory.Double, Math.E, ref emitted);
        return emitted;
    }

    private static int EmitUnsafeBlockOperations(ModuleDefinition corlibModule, Demand demand)
    {
        var emitted = 0;
        var factory = corlibModule.CorLibTypeFactory;
        var unsafeType = EnsureType(corlibModule, "System.Runtime.CompilerServices", "Unsafe",
            TypeAttributes.NotPublic | TypeAttributes.Abstract | TypeAttributes.Sealed, ref emitted);
        var voidStar = new PointerTypeSignature(factory.Void);

        if (demand.UnsafeInitBlock)
        {
            // The generic shape is what reconstructed bodies bind: initblk in
            // the emitted IL is decompiled as Unsafe.InitBlock(ref addr, ...)
            // against whatever element type the pointer had. The body is the
            // raw initblk opcode the lifted code carried - the same
            // instruction the BCL original wraps.
            emitted += EnsureUnsafeGenericBlockMethod(unsafeType, "InitBlock", ["T"],
                [factory.Byte, factory.UInt32], CilOpCodes.Initblk);
            emitted += EnsureUnsafePointerBlockMethod(unsafeType, "InitBlock",
                [voidStar, factory.Byte, factory.UInt32], CilOpCodes.Initblk);
        }
        if (demand.UnsafeCopyBlock)
        {
            emitted += EnsureUnsafeGenericBlockMethod(unsafeType, "CopyBlock", ["TDst", "TSrc"],
                [factory.UInt32], CilOpCodes.Cpblk);
            emitted += EnsureUnsafePointerBlockMethod(unsafeType, "CopyBlock",
                [voidStar, voidStar, factory.UInt32], CilOpCodes.Cpblk);
        }
        return emitted;
    }

    private static int EnsureUnsafeGenericBlockMethod(TypeDefinition unsafeType, string name,
        string[] typeParameters, CorLibTypeSignature[] tailParameters, CilOpCode operation)
    {
        if (unsafeType.Methods.Any(m => m.Name?.ToString() == name
                && m.Signature is { } s && !s.ParameterTypes.Any(p => p is PointerTypeSignature)))
            return 0;
        var module = unsafeType.DeclaringModule!;
        var factory = module.CorLibTypeFactory;
        var signature = MethodSignature.CreateStatic(factory.Void,
            typeParameters
                .Select((_, index) => (TypeSignature)new ByReferenceTypeSignature(
                    new GenericParameterSignature(GenericParameterType.Method, index)))
                .Concat(tailParameters)
                .ToList());
        signature.IsGeneric = true;
        signature.GenericParameterCount = typeParameters.Length;
        var method = new MethodDefinition(name,
            MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.HideBySig, signature);
        foreach (var parameter in typeParameters)
            method.GenericParameters.Add(new GenericParameter(parameter));
        var body = new CilMethodBody();
        body.Instructions.Add(CilOpCodes.Ldarg_0);
        body.Instructions.Add(CilOpCodes.Ldarg_1);
        body.Instructions.Add(CilOpCodes.Ldarg_2);
        body.Instructions.Add(operation);
        body.Instructions.Add(CilOpCodes.Ret);
        method.CilMethodBody = body;
        unsafeType.Methods.Add(method);
        return 1;
    }

    private static int EnsureUnsafePointerBlockMethod(TypeDefinition unsafeType, string name,
        TypeSignature[] parameters, CilOpCode operation)
    {
        if (unsafeType.Methods.Any(m => m.Name?.ToString() == name
                && m.Signature is { ParameterTypes.Count: > 0 } s
                && s.ParameterTypes[0] is PointerTypeSignature))
            return 0;
        var module = unsafeType.DeclaringModule!;
        var factory = module.CorLibTypeFactory;
        var signature = MethodSignature.CreateStatic(factory.Void, parameters);
        var method = new MethodDefinition(name,
            MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.HideBySig, signature);
        var body = new CilMethodBody();
        body.Instructions.Add(CilOpCodes.Ldarg_0);
        body.Instructions.Add(CilOpCodes.Ldarg_1);
        body.Instructions.Add(CilOpCodes.Ldarg_2);
        body.Instructions.Add(operation);
        body.Instructions.Add(CilOpCodes.Ret);
        method.CilMethodBody = body;
        unsafeType.Methods.Add(method);
        return 1;
    }

    private static int EmitBufferMemoryCopy(ModuleDefinition corlibModule)
    {
        var emitted = 0;
        var factory = corlibModule.CorLibTypeFactory;
        var buffer = EnsureType(corlibModule, "System", "Buffer",
            TypeAttributes.Public | TypeAttributes.Abstract | TypeAttributes.Sealed, ref emitted);
        if (buffer.Methods.Any(m => m.Name?.ToString() == "MemoryCopy"))
            return emitted;
        var voidStar = new PointerTypeSignature(factory.Void);
        var signature = MethodSignature.CreateStatic(factory.Void,
            [voidStar, voidStar, factory.UInt64, factory.UInt64]);
        var method = new MethodDefinition("MemoryCopy",
            MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.HideBySig, signature);
        var body = new CilMethodBody();
        // cpblk copies sourceBytesToCopy bytes from source to destination; the
        // bounds contract stays with the caller, matching the BCL shape.
        body.Instructions.Add(CilOpCodes.Ldarg_1);
        body.Instructions.Add(CilOpCodes.Ldarg_0);
        body.Instructions.Add(CilOpCodes.Ldarg_3);
        body.Instructions.Add(CilOpCodes.Cpblk);
        body.Instructions.Add(CilOpCodes.Ret);
        method.CilMethodBody = body;
        buffer.Methods.Add(method);
        emitted++;
        return emitted;
    }

    // Unity's VectorN.Max/Min are component-wise Mathf.Max/Min (a > b ? a : b
    // per component); emit the same shape over the typedef's component fields
    // and matching-arity constructor.
    private static int EmitVectorMinMax(TypeDefinition type, MinMaxKind kind)
    {
        var name = kind == MinMaxKind.Max ? "Max" : "Min";
        if (type.Methods.Any(m => m.Name?.ToString() == name))
            return 0;

        var components = new[] { "x", "y", "z", "w" }
            .Select(component => type.Fields.FirstOrDefault(field => field.Name?.ToString() == component))
            .TakeWhile(field => field != null)
            .Cast<FieldDefinition>()
            .ToArray();
        if (components.Length < 2)
            return 0;
        var ctor = type.Methods.FirstOrDefault(m => m.IsConstructor && !m.IsStatic
            && m.Signature is { } s && s.ParameterTypes.Count == components.Length);
        if (ctor == null)
            return 0;

        var signature = MethodSignature.CreateStatic(type.ToTypeSignature(),
            [type.ToTypeSignature(), type.ToTypeSignature()]);
        var method = new MethodDefinition(name,
            MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.HideBySig, signature);
        var body = new CilMethodBody();
        var instructions = body.Instructions;
        foreach (var field in components)
        {
            // For each component keep the larger (Max) or smaller (Min) of
            // lhs.c / rhs.c on the stack: the C# `a > b ? a : b`.
            var keepFirst = new CilInstructionLabel();
            var done = new CilInstructionLabel();
            instructions.Add(CilOpCodes.Ldarg_0);
            instructions.Add(CilOpCodes.Ldfld, field);
            instructions.Add(CilOpCodes.Ldarg_1);
            instructions.Add(CilOpCodes.Ldfld, field);
            instructions.Add(kind == MinMaxKind.Max ? CilOpCodes.Bgt : CilOpCodes.Blt, keepFirst);
            instructions.Add(CilOpCodes.Ldarg_1);
            instructions.Add(CilOpCodes.Ldfld, field);
            instructions.Add(CilOpCodes.Br, done);
            var keepFirstInstruction = new CilInstruction(CilOpCodes.Ldarg_0);
            instructions.Add(keepFirstInstruction);
            instructions.Add(CilOpCodes.Ldfld, field);
            keepFirst.Instruction = keepFirstInstruction;
            var doneInstruction = new CilInstruction(CilOpCodes.Nop);
            instructions.Add(doneInstruction);
            done.Instruction = doneInstruction;
        }
        instructions.Add(CilOpCodes.Newobj, ctor);
        instructions.Add(CilOpCodes.Ret);
        method.CilMethodBody = body;
        type.Methods.Add(method);
        return 1;
    }

    private static TypeDefinition EnsureType(ModuleDefinition module, string ns, string name,
        TypeAttributes attributes, ref int emitted)
    {
        var existing = module.TopLevelTypes.FirstOrDefault(type => !type.IsNested
            && type.Name?.ToString() == name && type.Namespace?.ToString() == ns);
        if (existing != null)
            return existing;
        var type = new TypeDefinition(ns, name, attributes,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        emitted++;
        return type;
    }

    private static void EnsureConstantField(TypeDefinition type, string name, CorLibTypeSignature signature,
        double value, ref int emitted)
    {
        if (type.Fields.Any(f => f.Name?.ToString() == name))
            return;
        type.Fields.Add(new FieldDefinition(name,
            FieldAttributes.Public | FieldAttributes.Static | FieldAttributes.Literal | FieldAttributes.HasDefault,
            new FieldSignature(signature))
        { Constant = AsmResolverConstants.GetOrCreateConstant(value) });
        emitted++;
    }
}
