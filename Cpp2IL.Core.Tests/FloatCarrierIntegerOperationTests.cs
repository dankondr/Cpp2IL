using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using ReflectionMethodAttributes = System.Reflection.MethodAttributes;

namespace Cpp2IL.Core.Tests;

/// <summary>
/// ARM64 `fmov` between the FP and integer register banks moves identical bits —
/// `BitConverter.*To*Bits`, never a `conv.*` numeric conversion. A float-typed
/// operand in an integer-domain bitwise op is therefore a proven bit
/// reinterpretation: the op is legal on the same-width integer carrier, and a
/// float comes back only at a proven FP consumer (a float-typed destination).
/// These tests pin that rule by JIT-executing the generated method — the emitted
/// IL must not only parse, it must return the exact bit pattern — and by keeping
/// genuine numeric conversions (fcvtzs-style `Move`) and width-disagreeing ops on
/// their existing paths.
/// </summary>
public class FloatCarrierIntegerOperationTests
{
    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
    }

    // `orr w0, w8, w0` where w8 was `fmov`d from s0: BitConverter.SingleToInt32Bits(value) | mask.
    [TestCase(1.5f, -2147483648, -1077936128)]
    [TestCase(1.5f, 0, 0x3FC00000)]
    [TestCase(0f, -2147483648, -2147483648)]
    public void SingleBitsThroughOr(float value, int mask, int expected)
    {
        var run = EmitCarrierFixture(OpCode.Or, App.SystemTypes.SystemSingleType,
            App.SystemTypes.SystemInt32Type, App.SystemTypes.SystemInt32Type,
            out var method);
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Call
                && i.Operand?.ToString()?.Contains("SingleToInt32Bits") == true), Is.True,
            () => string.Join("\n", method.CilMethodBody.Instructions));
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Or), Is.True);
        Assert.That(run.Invoke(null, [value, mask]), Is.EqualTo(expected));
    }

    [Test]
    public void SingleOrPreservesNegativeZero()
    {
        var run = EmitCarrierFixture(OpCode.Or, App.SystemTypes.SystemSingleType,
            App.SystemTypes.SystemInt32Type, App.SystemTypes.SystemInt32Type, out _);
        Assert.That(run.Invoke(null, [BitConverter.Int32BitsToSingle(unchecked((int)0x80000000)), 0]),
            Is.EqualTo(unchecked((int)0x80000000)));
    }

    [Test]
    public void SingleOrPreservesInfinities()
    {
        var run = EmitCarrierFixture(OpCode.Or, App.SystemTypes.SystemSingleType,
            App.SystemTypes.SystemInt32Type, App.SystemTypes.SystemInt32Type, out _);
        Assert.That(run.Invoke(null, [float.PositiveInfinity, 0]), Is.EqualTo(0x7F800000));
        Assert.That(run.Invoke(null, [float.NegativeInfinity, 0]), Is.EqualTo(unchecked((int)0xFF800000)));
    }

    [Test]
    public void SingleOrPreservesNaNPayload()
    {
        var run = EmitCarrierFixture(OpCode.Or, App.SystemTypes.SystemSingleType,
            App.SystemTypes.SystemInt32Type, App.SystemTypes.SystemInt32Type, out _);
        var nanPayload = BitConverter.Int32BitsToSingle(unchecked((int)0x7FC00001));
        Assert.That(run.Invoke(null, [nanPayload, 0]), Is.EqualTo(unchecked((int)0x7FC00001)));
    }

    // `eor x0, x8, x0` where x8 was `fmov`d from d0: BitConverter.DoubleToInt64Bits(value) ^ mask.
    [TestCase(1.5, -9223372036854775808L, -4613937818241073152L)]
    [TestCase(1.5, 0L, 0x3FF8000000000000)]
    public void DoubleBitsThroughXor(double value, long mask, long expected)
    {
        var run = EmitCarrierFixture(OpCode.Xor, App.SystemTypes.SystemDoubleType,
            App.SystemTypes.SystemInt64Type, App.SystemTypes.SystemInt64Type,
            out var method);
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Call
                && i.Operand?.ToString()?.Contains("DoubleToInt64Bits") == true), Is.True,
            () => string.Join("\n", method.CilMethodBody.Instructions));
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Xor), Is.True);
        Assert.That(run.Invoke(null, [value, mask]), Is.EqualTo(expected));
    }

    [Test]
    public void DoubleXorPreservesNegativeZero()
    {
        var run = EmitCarrierFixture(OpCode.Xor, App.SystemTypes.SystemDoubleType,
            App.SystemTypes.SystemInt64Type, App.SystemTypes.SystemInt64Type, out _);
        Assert.That(run.Invoke(null, [BitConverter.Int64BitsToDouble(unchecked((long)0x8000000000000000)), 0L]),
            Is.EqualTo(unchecked((long)0x8000000000000000)));
    }

    [Test]
    public void DoubleXorPreservesInfinities()
    {
        var run = EmitCarrierFixture(OpCode.Xor, App.SystemTypes.SystemDoubleType,
            App.SystemTypes.SystemInt64Type, App.SystemTypes.SystemInt64Type, out _);
        Assert.That(run.Invoke(null, [double.PositiveInfinity, 0L]), Is.EqualTo(0x7FF0000000000000L));
        Assert.That(run.Invoke(null, [double.NegativeInfinity, 0L]),
            Is.EqualTo(unchecked((long)0xFFF0000000000000)));
    }

    [Test]
    public void DoubleXorPreservesNaNPayload()
    {
        var run = EmitCarrierFixture(OpCode.Xor, App.SystemTypes.SystemDoubleType,
            App.SystemTypes.SystemInt64Type, App.SystemTypes.SystemInt64Type, out _);
        var nanPayload = BitConverter.Int64BitsToDouble(unchecked((long)0x7FF8000000000001));
        Assert.That(run.Invoke(null, [nanPayload, 0L]), Is.EqualTo(unchecked((long)0x7FF8000000000001)));
    }

    // `and w8` on `fmov` bits and `mvn w8` on `fmov` bits follow the same carrier rule.
    [Test]
    public void SingleBitsThroughAnd()
    {
        var run = EmitCarrierFixture(OpCode.And, App.SystemTypes.SystemSingleType,
            App.SystemTypes.SystemInt32Type, App.SystemTypes.SystemInt32Type, out _);
        // sign bit of -1.5f cleared; the mask selects lanes of the bit pattern
        Assert.That(run.Invoke(null, [-1.5f, 0x7FFFFFFF]), Is.EqualTo(0x3FC00000));
        Assert.That(run.Invoke(null, [1.5f, 0x00FF000F]), Is.EqualTo(0x00C00000));
    }

    [Test]
    public void SingleBitsThroughNot()
    {
        var (method, module) = EmitFixture(OpCode.Not, App.SystemTypes.SystemSingleType,
            null, App.SystemTypes.SystemInt32Type);
        var run = LoadAndGet(module);
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Not), Is.True,
            () => string.Join("\n", method.CilMethodBody.Instructions));
        Assert.That(method.CilMethodBody.Instructions.Any(i => i.OpCode == CilOpCodes.Call
                && i.Operand?.ToString()?.Contains("SingleToInt32Bits") == true), Is.True);
        Assert.That(run.Invoke(null, [1.5f]), Is.EqualTo(unchecked((int)~0x3FC00000)));
    }

    // The store is a V-register float again (`fmov s8, w8` after the op): the carrier
    // result reinterprets back at its own width — a proven FP consumer.
    [Test]
    public void FloatConsumerGetsFloatBitsBack()
    {
        var run = EmitCarrierFixture(OpCode.Or, App.SystemTypes.SystemSingleType,
            App.SystemTypes.SystemInt32Type, App.SystemTypes.SystemSingleType,
            out var method);
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Call
                && i.Operand?.ToString()?.Contains("Int32BitsToSingle") == true), Is.True,
            () => string.Join("\n", method.CilMethodBody.Instructions));
        var result = run.Invoke(null, [1.5f, unchecked((int)0x80000000)]);
        Assert.That(BitConverter.SingleToInt32Bits((float)result!), Is.EqualTo(unchecked((int)0xBFC00000)));
    }

    [Test]
    public void DoubleConsumerGetsDoubleBitsBack()
    {
        var run = EmitCarrierFixture(OpCode.Xor, App.SystemTypes.SystemDoubleType,
            App.SystemTypes.SystemInt64Type, App.SystemTypes.SystemDoubleType,
            out var method);
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Call
                && i.Operand?.ToString()?.Contains("Int64BitsToDouble") == true), Is.True,
            () => string.Join("\n", method.CilMethodBody.Instructions));
        var result = run.Invoke(null, [1.5, unchecked((long)0x8000000000000000)]);
        Assert.That(BitConverter.DoubleToInt64Bits((double)result!), Is.EqualTo(unchecked((long)0xBFF8000000000000)));
    }

    // A float slot reached by `Move` is a numeric conversion (fcvtzs), not a bit
    // reinterpretation: conv.i4 stays, no BitConverter call appears, and the value
    // truncates numerically.
    [Test]
    public void NumericConversionKeepsNumericSemantics()
    {
        var app = App;
        var value = new LocalVariable("value", new Register(null, "V0"))
            { Type = app.SystemTypes.SystemSingleType };
        var result = new LocalVariable("result", new Register(null, "X0_v1"))
            { Type = app.SystemTypes.SystemInt32Type };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "ToInt",
            app.SystemTypes.SystemInt32Type, ReflectionMethodAttributes.Static,
            [app.SystemTypes.SystemSingleType], ["value"]);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, result, value),
            new Instruction(1, OpCode.Return, result)]);
        context.Locals = new List<LocalVariable> { value, result };
        context.ParameterLocals = new List<LocalVariable> { value };
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("NumericConversion.dll");
        SeedCorLibTypes(module, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemVoidType);
        var type = new TypeDefinition("Tests", "Carrier", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32, [module.CorLibTypeFactory.Single]));
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "value", 0));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);
        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Conv_I4), Is.True,
            () => string.Join("\n", il));
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                && i.Operand?.ToString()?.Contains("BitConverter") == true), Is.False);

        var run = LoadAndGet(module);
        Assert.That(run.Invoke(null, [12.75f]), Is.EqualTo(12));
        Assert.That(run.Invoke(null, [-12.75f]), Is.EqualTo(-12));
    }

    // A Single operand next to an Int64 operand (and vice versa) has no single
    // carrier the native code could have used: the op stays unrecoverable.
    [TestCase("System.Single", "System.Int64")]
    [TestCase("System.Double", "System.Int32")]
    public void MixedWidthStaysUnrecoverable(string floatName, string intName)
    {
        var app = App;
        var floatType = floatName == "System.Single"
            ? app.SystemTypes.SystemSingleType : app.SystemTypes.SystemDoubleType;
        var intType = intName == "System.Int32"
            ? app.SystemTypes.SystemInt32Type : app.SystemTypes.SystemInt64Type;
        var value = new LocalVariable("value", new Register(null, "V0")) { Type = floatType };
        var mask = new LocalVariable("mask", new Register(null, "X0")) { Type = intType };
        var result = new LocalVariable("result", new Register(null, "X0_v1")) { Type = intType };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            intType, ReflectionMethodAttributes.Static, [floatType, intType], ["value", "mask"]);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Or, result, value, mask),
            new Instruction(1, OpCode.Return, result)]);
        context.Locals = new List<LocalVariable> { value, mask, result };
        context.ParameterLocals = new List<LocalVariable> { value, mask };
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("MixedWidth.dll");
        SeedCorLibTypes(module, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemInt64Type, app.SystemTypes.SystemVoidType);
        var type = new TypeDefinition("Tests", "Carrier", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(CorLibSignature(module, intType),
                [CorLibSignature(module, floatType), CorLibSignature(module, intType)]));
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "value", 0));
        method.ParameterDefinitions.Add(new ParameterDefinition(2, "mask", 0));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);
        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Throw), Is.True,
                () => string.Join("\n", il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand?.ToString()?.Contains("Unrecoverable integer operation") == true), Is.True);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString()?.Contains("BitConverter") == true), Is.False);
        });
    }

    // A destination of the other float width is no proven FP consumer for this
    // carrier either: the op stays unrecoverable.
    [Test]
    public void MismatchedFloatConsumerStaysUnrecoverable()
    {
        var app = App;
        var value = new LocalVariable("value", new Register(null, "V0"))
            { Type = app.SystemTypes.SystemSingleType };
        var mask = new LocalVariable("mask", new Register(null, "X0"))
            { Type = app.SystemTypes.SystemInt32Type };
        var result = new LocalVariable("result", new Register(null, "V0_v1"))
            { Type = app.SystemTypes.SystemDoubleType };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemDoubleType, ReflectionMethodAttributes.Static,
            [app.SystemTypes.SystemSingleType, app.SystemTypes.SystemInt32Type], ["value", "mask"]);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Or, result, value, mask),
            new Instruction(1, OpCode.Return, result)]);
        context.Locals = new List<LocalVariable> { value, mask, result };
        context.ParameterLocals = new List<LocalVariable> { value, mask };
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("MismatchedConsumer.dll");
        SeedCorLibTypes(module, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType);
        var type = new TypeDefinition("Tests", "Carrier", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Double,
                [module.CorLibTypeFactory.Single, module.CorLibTypeFactory.Int32]));
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "value", 0));
        method.ParameterDefinitions.Add(new ParameterDefinition(2, "mask", 0));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Throw), Is.True,
            () => string.Join("\n", method.CilMethodBody.Instructions));
    }

    // `lsr x8, x9, #32` on a double's bits yields the carrier's high dword; the
    // i32 destination truncates it exactly like a W-register read.
    [Test]
    public void DoubleShiftRightKeepsHighDword()
    {
        var app = App;
        var value = new LocalVariable("value", new Register(null, "V0"))
            { Type = app.SystemTypes.SystemDoubleType };
        var result = new LocalVariable("result", new Register(null, "X0_v1"))
            { Type = app.SystemTypes.SystemInt32Type };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemInt32Type, ReflectionMethodAttributes.Static,
            [app.SystemTypes.SystemDoubleType], ["value"]);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.ShiftRight, result, value, new Immediate(32)),
            new Instruction(1, OpCode.Return, result)]);
        context.Locals = new List<LocalVariable> { value, result };
        context.ParameterLocals = new List<LocalVariable> { value };
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("HighDword.dll");
        SeedCorLibTypes(module, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemDoubleType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemInt64Type, app.SystemTypes.SystemVoidType);
        var type = new TypeDefinition("Tests", "Carrier", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32, [module.CorLibTypeFactory.Double]));
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "value", 0));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Call
                && i.Operand?.ToString()?.Contains("DoubleToInt64Bits") == true), Is.True,
            () => string.Join("\n", method.CilMethodBody.Instructions));

        var run = LoadAndGet(module);
        Assert.That(run.Invoke(null, [1.5]), Is.EqualTo(unchecked((int)0x3FF80000)));
        Assert.That(run.Invoke(null, [-1.5]), Is.EqualTo(unchecked((int)0xBFF80000)));
    }

    // `orr w8, w9, w10` zero-extends its result into x8: an i64 destination must
    // see conv.u8 semantics, not a sign-extended carrier.
    [Test]
    public void WiderDestinationSeesZeroExtendedCarrier()
    {
        var app = App;
        var value = new LocalVariable("value", new Register(null, "V0"))
            { Type = app.SystemTypes.SystemSingleType };
        var mask = new LocalVariable("mask", new Register(null, "X0"))
            { Type = app.SystemTypes.SystemInt32Type };
        var result = new LocalVariable("result", new Register(null, "X0_v1"))
            { Type = app.SystemTypes.SystemInt64Type };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemInt64Type, ReflectionMethodAttributes.Static,
            [app.SystemTypes.SystemSingleType, app.SystemTypes.SystemInt32Type], ["value", "mask"]);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Or, result, value, mask),
            new Instruction(1, OpCode.Return, result)]);
        context.Locals = new List<LocalVariable> { value, mask, result };
        context.ParameterLocals = new List<LocalVariable> { value, mask };
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("WideDestination.dll");
        SeedCorLibTypes(module, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemInt64Type, app.SystemTypes.SystemVoidType);
        var type = new TypeDefinition("Tests", "Carrier", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int64,
                [module.CorLibTypeFactory.Single, module.CorLibTypeFactory.Int32]));
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "value", 0));
        method.ParameterDefinitions.Add(new ParameterDefinition(2, "mask", 0));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);
        var run = LoadAndGet(module);
        // 0x3FC00000 | 0x80000000 = 0xBFC00000; zero-extended, not sign-extended.
        Assert.That(run.Invoke(null, [1.5f, unchecked((int)0x80000000)]), Is.EqualTo(0x00000000BFC00000L));
    }

    private static System.Reflection.MethodInfo EmitCarrierFixture(OpCode opcode,
        TypeAnalysisContext operandType, TypeAnalysisContext mateType, TypeAnalysisContext resultType,
        out MethodDefinition method)
    {
        var (m, module) = EmitFixture(opcode, operandType, mateType, resultType);
        method = m;
        return LoadAndGet(module);
    }

    // Builds op(result, value, mate?) → return result, generates the body, writes the
    // module and loads it so the returned MethodInfo JITs the emitted IL.
    private static (MethodDefinition method, ModuleDefinition module) EmitFixture(OpCode opcode,
        TypeAnalysisContext valueType, TypeAnalysisContext? mateType, TypeAnalysisContext resultType)
    {
        var app = App;
        var value = new LocalVariable("value", new Register(null, "V0")) { Type = valueType };
        var mate = mateType == null
            ? null
            : new LocalVariable("mask", new Register(null, "X0")) { Type = mateType };
        var result = new LocalVariable("result", new Register(null, "X0_v1")) { Type = resultType };

        var parameterTypes = mate == null ? [valueType] : new[] { valueType, mateType! };
        var parameterNames = mate == null ? new[] { "value" } : new[] { "value", "mask" };
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            resultType, ReflectionMethodAttributes.Static, parameterTypes, parameterNames);
        var opInstruction = mate == null
            ? new Instruction(0, opcode, result, value)
            : new Instruction(0, opcode, result, value, mate);
        context.ControlFlowGraph = new ISILControlFlowGraph(
            [opInstruction, new Instruction(1, OpCode.Return, result)]);
        context.Locals = mate == null
            ? new List<LocalVariable> { value, result }
            : new List<LocalVariable> { value, mate, result };
        context.ParameterLocals = mate == null
            ? new List<LocalVariable> { value }
            : new List<LocalVariable> { value, mate };
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("FloatCarrier.dll");
        SeedCorLibTypes(module, app.SystemTypes.SystemObjectType, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemInt64Type, app.SystemTypes.SystemBooleanType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemStringType);
        var type = new TypeDefinition("Tests", "Carrier", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var signature = MethodSignature.CreateStatic(CorLibSignature(module, resultType),
            parameterTypes.Select(t => CorLibSignature(module, t)));
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static, signature);
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "value", 0));
        if (mate != null)
            method.ParameterDefinitions.Add(new ParameterDefinition(2, "mask", 0));
        type.Methods.Add(method);
        IlGenerator.GenerateIl(context, method);
        return (method, module);
    }

    private static System.Reflection.MethodInfo LoadAndGet(ModuleDefinition module)
    {
        // The emitted body declares locals typed by placeholder corlib definitions;
        // rebind primitives to real corlib signatures so the produced assembly JITs.
        foreach (var def in module.TopLevelTypes.SelectMany(t => t.Methods))
        {
            if (def.CilMethodBody == null)
                continue;
            foreach (var local in def.CilMethodBody.LocalVariables)
                local.VariableType = local.VariableType.FullName switch
                {
                    "System.Single" => module.CorLibTypeFactory.Single,
                    "System.Double" => module.CorLibTypeFactory.Double,
                    "System.Int32" => module.CorLibTypeFactory.Int32,
                    "System.Int64" => module.CorLibTypeFactory.Int64,
                    "System.Boolean" => module.CorLibTypeFactory.Boolean,
                    "System.Object" => module.CorLibTypeFactory.Object,
                    _ => local.VariableType,
                };
        }
        var assembly = new AssemblyDefinition("FloatCarrierAssembly", new Version(1, 0));
        assembly.Modules.Add(module);
        using var stream = new MemoryStream();
        module.Write(stream);
        var loaded = System.Reflection.Assembly.Load(stream.ToArray());
        return loaded.GetType("Tests.Carrier")!.GetMethod("Run")!;
    }

    private static TypeSignature CorLibSignature(ModuleDefinition module, TypeAnalysisContext type) =>
        type.FullName switch
        {
            "System.Single" => module.CorLibTypeFactory.Single,
            "System.Double" => module.CorLibTypeFactory.Double,
            "System.Int32" => module.CorLibTypeFactory.Int32,
            "System.Int64" => module.CorLibTypeFactory.Int64,
            "System.Boolean" => module.CorLibTypeFactory.Boolean,
            "System.Void" => module.CorLibTypeFactory.Void,
            _ => module.CorLibTypeFactory.Object,
        };

    private static void SeedCorLibTypes(ModuleDefinition module, params TypeAnalysisContext[] types)
    {
        foreach (var type in types)
        {
            var baseRef = type is { IsValueType: true }
                ? module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType")
                : null;
            type.PutExtraData("AsmResolverType",
                new TypeDefinition(type.Namespace, type.Name,
                    TypeAttributes.Public | (type.IsValueType ? TypeAttributes.Sealed | TypeAttributes.SequentialLayout : TypeAttributes.Class),
                    baseRef));
        }
    }
}
