using System;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using ReflectionMethodAttributes = System.Reflection.MethodAttributes;

namespace Cpp2IL.Core.Tests.Isil;

/// <summary>
/// Remaining ARM64 SIMD clusters in the Castle corpus: scalar/vector floating
/// compare masks (FCMGT/FCMLT/FCMGE/FCMLE/FCMEQ), three-way bit selects
/// (BIT/BIF/BSL), and pairwise float adds (FADDP). Lift-only tests pin the
/// emitted ISIL shape; the fixtures execute native semantics through the
/// generated IL as the oracle.
/// </summary>
public class Arm64SimdLeftoverOpsTests
{
    private static System.Collections.Generic.List<Instruction> Lift(params uint[] words)
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Test",
            app.SystemTypes.SystemVoidType, System.Reflection.MethodAttributes.Public | System.Reflection.MethodAttributes.Static, []);
        return new NewArmV8InstructionSet().ConvertInstructions(
            Disassembler.Disassemble(words.SelectMany(BitConverter.GetBytes).ToArray(), 0), context);
    }

    // int MaskSelect(float a, float b, int x, int y) = a > b ? x : y
    // fcmgt emits the all-ones/zero mask; the bit select consumes it.
    private static readonly uint[] MaskSelect =
    [
        0x7EA1E403, // fcmgt s3, s0, s1
        0x1E270004, // fmov s4, w0
        0x1E270025, // fmov s5, w1
        0x2EA31C85, // bit v5.8b, v4.8b, v3.8b   ; v5 = (x & m) | (y & ~m)
        0x0E043CA0, // mov w0, v5.s[0]
        0xD65F03C0, // ret
    ];

    // int Blend(int a, int b, int m) = (a & m) | (b & ~m) via BSL's
    // destination-as-mask semantics
    private static readonly uint[] BlendBsl =
    [
        0x0E040C00, // dup v0.2s, w0
        0x0E040C21, // dup v1.2s, w1
        0x0E040C42, // dup v2.2s, w2
        0x2E611C02, // bsl v2.8b, v0.8b, v1.8b   ; v2 = (a & m) | (b & ~m)
        0x0E043C40, // mov w0, v2.s[0]
        0xD65F03C0, // ret
    ];

    // float PairSum(float x, float y) = x + y via scalar pairwise add over an
    // INS-built vector
    private static readonly uint[] PairSum =
    [
        0x6E040402, // mov v2.s[0], v0.s[0]
        0x6E0C0422, // mov v2.s[1], v1.s[0]
        0x7E30D840, // faddp s0, v2.2s
        0xD65F03C0, // ret
    ];

    // float QuadSum(float a, float b, float c, float d): vector FADDP.2S folds
    // (a+b, c+d) then the scalar FADDP reduces it — (a+b)+(c+d).
    private static readonly uint[] QuadSum =
    [
        0x6E040404, // mov v4.s[0], v0.s[0]
        0x6E0C0424, // mov v4.s[1], v1.s[0]
        0x6E040445, // mov v5.s[0], v2.s[0]
        0x6E0C0465, // mov v5.s[1], v3.s[0]
        0x2E25D486, // faddp v6.2s, v4.2s, v5.2s
        0x7E30D8C0, // faddp s0, v6.2s
        0xD65F03C0, // ret
    ];

    // int GreaterMask(float a, float b) = b > a ? -1 : 0 — vector FCMGT.2S
    // lanes fold to all-ones/zero masks; the extracted lane is the mask of
    // b > a (v2 lane 1 = b, v3 lane 1 = a).
    private static readonly uint[] GreaterMask =
    [
        0x6E040402, // mov v2.s[0], v0.s[0]
        0x6E0C0422, // mov v2.s[1], v1.s[0]
        0x0E040403, // dup v3.2s, v0.s[0]        ; v3 = [a, a]
        0x2EA3E446, // fcmgt v6.2s, v2.2s, v3.2s ; v6 = [a>a:0, b>a:mask]
        0x0E0C3CC0, // mov w0, v6.s[1]
        0xD65F03C0, // ret
    ];

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static object? Run(uint[] words, TypeAnalysisContext returnType,
        TypeAnalysisContext[] paramTypes, string[] paramNames,
        Func<LocalVariable, TypeAnalysisContext> localTypes, object?[] args)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Test",
            returnType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            paramTypes, paramNames);
        var instructionSet = new NewArmV8InstructionSet();
        var il = instructionSet.ConvertInstructions(
            Disassembler.Disassemble(words.SelectMany(BitConverter.GetBytes).ToArray(), 0), context);
        Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False,
            $"unlifted instructions: {string.Join(" | ", il.Where(i => i.OpCode == OpCode.NotImplemented))}");

        context.ControlFlowGraph = new ISILControlFlowGraph(il);
        context.ParameterOperands = instructionSet.GetParameterOperandsFromMethod(context);
        StackAnalyzer.Analyze(context);
        context.DominatorInfo = new DominatorInfo(context.ControlFlowGraph);
        SsaForm.Build(context);
        LocalVariables.CreateAll(context);
        SsaForm.Remove(context);
        context.AnalysisWarnings = [];
        foreach (var local in context.Locals)
            local.Type = localTypes(local);

        var module = new ModuleDefinition("SimdLeftoverFixture.dll",
            new AssemblyReference("System.Private.CoreLib", typeof(object).Assembly.GetName().Version!));
        var singlePlaceholder = new TypeDefinition("System", "Single", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(singlePlaceholder);
        app.SystemTypes.SystemSingleType.PutExtraData("AsmResolverType", singlePlaceholder);
        var intPlaceholder = new TypeDefinition("System", "Int32", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(intPlaceholder);
        app.SystemTypes.SystemInt32Type.PutExtraData("AsmResolverType", intPlaceholder);
        var type = new TypeDefinition("Tests", "Case", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var corlib = module.CorLibTypeFactory;
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(ToCorlib(corlib, returnType),
                paramTypes.Select(t => ToCorlib(corlib, t)).ToArray()));
        type.Methods.Add(method);
        for (var i = 0; i < paramNames.Length; i++)
            method.ParameterDefinitions.Add(new ParameterDefinition((ushort)(i + 1), paramNames[i], 0));

        var desiredTypes = context.Locals.Select(l => ToCorlib(corlib, l.Type!)).ToList();
        IlGenerator.GenerateIl(context, method);
        foreach (var local in method.CilMethodBody!.LocalVariables)
            local.VariableType = local.Index < desiredTypes.Count
                ? desiredTypes[local.Index]
                : corlib.Int32; // emit-time spill locals have no analysis counterpart

        var assembly = new AssemblyDefinition("SimdLeftoverFixture", new Version(1, 0));
        assembly.Modules.Add(module);
        using var stream = new System.IO.MemoryStream();
        module.Write(stream);
        var loaded = System.Reflection.Assembly.Load(stream.ToArray());
        return loaded.GetType("Tests.Case")!.GetMethod("Run")!.Invoke(null, args);

        TypeSignature ToCorlib(CorLibTypeFactory factory, TypeAnalysisContext type) =>
            type.FullName switch
            {
                "System.Single" => factory.Single,
                "System.Double" => factory.Double,
                "System.Int64" => factory.Int64,
                _ => factory.Int32,
            };
    }

    private static TypeAnalysisContext Single => Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemSingleType;
    private static TypeAnalysisContext Int32 => Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type;

    [TestCase(1f, 0f, 7, 9, 7)]
    [TestCase(0f, 1f, 7, 9, 9)]
    [TestCase(2.5f, 2.5f, 3, 4, 4)]
    public void ScalarFcmgtMaskSelectsThroughBit(float a, float b, int x, int y, int expected)
    {
        var result = Run(MaskSelect, Int32, [Single, Single, Int32, Int32], ["a", "b", "x", "y"],
            local => local.Register.Name is "V0" or "V1" ? Single : Int32,
            [a, b, x, y]);
        Assert.That(result, Is.EqualTo(expected));
    }

    // bsl v2 = (v0 & v2) | (v1 & ~v2): a selected where the mask is set
    [TestCase(5, 2, -1, 5)]
    [TestCase(5, 2, 0, 2)]
    [TestCase(0x12345678, 0x77777777, 0x0F0F0F0F, 0x72747678)]
    public void VectorBslBlendsByMask(int a, int b, int m, int expected)
    {
        var result = Run(BlendBsl, Int32, [Int32, Int32, Int32], ["a", "b", "m"],
            _ => Int32, [a, b, m]);
        Assert.That(result, Is.EqualTo(expected));
    }

    [TestCase(1.5f, 2.5f, 4f)]
    [TestCase(-3f, 1.25f, -1.75f)]
    public void ScalarFaddpAddsInsLanes(float x, float y, float expected)
    {
        var result = Run(PairSum, Single, [Single, Single], ["x", "y"], _ => Single, [x, y]);
        Assert.That((float)result!, Is.EqualTo(expected).Within(1e-6f));
    }

    [TestCase(1f, 2f, -1)]
    [TestCase(3f, 2f, 0)]
    [TestCase(1f, 1f, 0)]
    public void VectorCompareMaskExecutesAsInt(float a, float b, int expected)
    {
        // V0/V1 carry the float args; the V2/V3 element locals carry them as
        // float lanes; V6's lanes are integer masks, as is the extracted X0.
        var result = Run(GreaterMask, Int32, [Single, Single], ["a", "b"],
            local => local.Register.Name is "V0" or "V1"
                || local.Register.Name.StartsWith("V2.")
                || local.Register.Name.StartsWith("V3.")
                ? Single : Int32,
            [a, b]);
        Assert.That(result, Is.EqualTo(expected));
    }

    [TestCase(1f, 2f, 3f, 4f, 10f)]
    [TestCase(0.5f, -1f, 0.25f, 2f, 1.75f)]
    public void VectorFaddpFeedsScalarFaddp(float a, float b, float c, float d, float expected)
    {
        var result = Run(QuadSum, Single, [Single, Single, Single, Single], ["a", "b", "c", "d"],
            _ => Single, [a, b, c, d]);
        Assert.That((float)result!, Is.EqualTo(expected).Within(1e-6f));
    }

    [Test]
    public void ScalarFloatComparesEmitMaskOps()
    {
        // three-register forms
        foreach (var (word, check) in new (uint, OpCode)[]
        {
            (0x7EA1E403, OpCode.CheckGreater), // fcmgt s3, s0, s1
            (0x5E21E403, OpCode.CheckEqual),   // fcmeq s3, s0, s1
            (0x7E21E403, OpCode.CheckGreater), // fcmge s3, s0, s1
        })
        {
            var il = Lift(word);
            Assert.That(il.Any(i => i.OpCode == check), Is.True, $"0x{word:X8}");
            Assert.That(il.Any(i => i.OpCode == OpCode.Negate), Is.True, $"0x{word:X8} must emit the all-ones mask");
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False, $"0x{word:X8}");
        }

        // versus-zero forms: fcmgt s0, s0, #0 and fcmge s0, s0, #0
        foreach (var word in new uint[] { 0x5EA0C800, 0x7EA0C800 })
        {
            var il = Lift(word);
            Assert.That(il.Any(i => i.OpCode == OpCode.Negate), Is.True, $"0x{word:X8}");
            Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False, $"0x{word:X8}");
        }
    }

    [Test]
    public void VectorComparesFoldLanesIntoMasks()
    {
        // INS-built lanes give every source lane real element-local provenance
        var il = Lift(
            0x6E040402, // mov v2.s[0], v0.s[0]
            0x6E0C0422, // mov v2.s[1], v1.s[0]
            0x0E040403, // dup v3.2s, v0.s[0]
            0x2EA3E446, // fcmgt v6.2s, v2.2s, v3.2s
            0xD65F03C0);
        Assert.That(il.Any(i => i.OpCode == OpCode.CheckGreater), Is.True);
        Assert.That(il.Any(i => i.OpCode == OpCode.Negate), Is.True);
        Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);

        // 4S and 2D shapes fold the same way
        foreach (var word in new uint[] { 0x6EA3E446, 0x6EE3E446 })
        {
            var full = Lift(
                0x6E040402, 0x6E0C0422, 0x6E140402, 0x6E1C0402, // v2 = [a,b,a,a]
                0x4E040403,                                     // dup v3.4s, v0.s[0] = [a,a,a,a]
                word,                                           // fcmgt v6.4s/2d, v2, v3
                0xD65F03C0);
            Assert.That(full.Any(i => i.OpCode == OpCode.CheckGreater), Is.True, $"0x{word:X8}");
            Assert.That(full.Any(i => i.OpCode == OpCode.NotImplemented), Is.False, $"0x{word:X8}");
        }
    }

    [Test]
    public void FaddpOnOpaqueWholeRegisterCarrierStaysDiagnostic()
    {
        // ldr d0 loads a whole-register local; FADDP S0, V0.2S would need the
        // high lane via a bit-shift of that local — refused: the register may
        // carry a managed Vector2/aggregate, not an integer lane carrier.
        var il = Lift(
            0xFD400000, // ldr d0, [x0]
            0x7E30D840, // faddp s0, v0.2s
            0xD65F03C0);
        Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.True);
    }

    [Test]
    public void UnsupportedCompareAndPairwiseShapesStayDiagnostic()
    {
        foreach (var word in new uint[]
        {
            0x5EF8C812, // fcmgt h0, h0, h18 — fp16 scalar compare
            0x7E30D840, // faddp s0, v0.2s with no proven lanes
            0x2E611C02, // bsl v2.8b, v0.8b, v1.8b with fully opaque inputs
        })
            Assert.That(Lift(word).Any(i => i.OpCode == OpCode.NotImplemented), Is.True, $"0x{word:X8}");
    }

    [Test]
    public void BitSelectsFoldWindows()
    {
        // proven lanes fold without diagnostics
        var il = Lift(
            0x0E040C00, // dup v0.2s, w0
            0x0E040C21, // dup v1.2s, w1
            0x0E040C42, // dup v2.2s, w2
            0x2EA21C01, // bit v1.8b, v0.8b, v2.8b
            0xD65F03C0);
        Assert.That(il.Any(i => i.OpCode == OpCode.Or), Is.True);
        Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False);
    }
}
