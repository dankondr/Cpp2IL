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
/// Paired fixture: real IL2CPP ARM64 machine code for a scalar SIMD
/// interpolation routine lifted through the instruction set must emit IL that
/// computes the same result as the native arithmetic — synthetic ISIL tests
/// cannot prove that on their own.
/// </summary>
public class Arm64SimdSemanticFixtureTests
{
    // RootMotion.Interp::OutQuintic(Single, Single, Single) — verbatim machine
    // code from the IL2CPP binary. The compiler vectorized the Horner
    // evaluation of c * ((t-1)^5 + 1) + b: a DUP broadcast, lane-wise FMULs by
    // a scalar element, and scalar FMUL/FADD/FMOV plumbing across the same
    // registers.
    private static readonly uint[] OutQuintic =
    [
        0x0f00f683, // fmov v3.2s, #5
        0x1e200804, // fmul s4, s0, s0            ; s4 = t*t
        0x1e249007, // fmov s7, #10
        0x6e040403, // mov v3.s[0], v0.s[0]      ; v3 = [t, 5]
        0x0f849063, // fmul v3.2s, v3.2s, v4.s[0]; v3 = [t^3, 5t^2]
        0x0f849065, // fmul v5.2s, v3.2s, v4.s[0]; v5 = [t^5, 5t^4]
        0x1e2308e3, // fmul s3, s7, s3           ; s3 = 10t^3
        0x1e270884, // fmul s4, s4, s7           ; s4 = 10t^2
        0x0e0c04a6, // dup v6.2s, v5.s[1]        ; v6 = [5t^4, 5t^4]
        0x0ea6d4a5, // fsub v5.2s, v5.2s, v6.2s  ; v5.s0 = t^5 - 5t^4
        0x1e252863, // fadd s3, s3, s5           ; s3 = t^5 - 5t^4 + 10t^3
        0x1e229005, // fmov s5, #5
        0x1e250800, // fmul s0, s0, s5           ; s0 = 5t
        0x1e243863, // fsub s3, s3, s4           ; s3 = ... - 10t^2
        0x1e232800, // fadd s0, s0, s3           ; s0 = 5t + s3
        0x1e220800, // fmul s0, s0, s2           ; s0 = c * (5t + s3)
        0x1e212800, // fadd s0, s0, s1           ; s0 += b
        0xd65f03c0, // ret
    ];

    private static float ReferenceOutQuintic(float t, float b, float c)
    {
        // the same arithmetic in the native instruction order
        var s4 = t * t;
        var v3s0 = t * s4;
        var v5s0 = v3s0 * s4;
        var v5s1 = 5f * s4 * s4;
        var s3 = 10f * v3s0;
        s4 *= 10f;
        v5s0 -= v5s1;
        var s0 = t * 5f;
        s3 += v5s0;
        s3 -= s4;
        s0 += s3;
        s0 *= c;
        return s0 + b;
    }

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    [TestCase(0.5f, 1f, 3f)]
    [TestCase(1f, 0f, 2f)]
    [TestCase(0.25f, -4f, 0.5f)]
    [TestCase(0f, 7f, -2f)]
    public void LiftedOutQuinticExecutesNativeSemantics(float t, float b, float c)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var single = app.SystemTypes.SystemSingleType;
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "OutQuintic",
            single, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            [single, single, single], ["t", "b", "c"]);
        var instructionSet = new NewArmV8InstructionSet();
        var il = instructionSet.ConvertInstructions(
            Disassembler.Disassemble(OutQuintic.SelectMany(BitConverter.GetBytes).ToArray(), 0), context);
        Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False,
            $"unlifted instructions: {string.Join(" | ", il.Where(i => i.OpCode == OpCode.NotImplemented))}");

        // run the real analysis spine: SSA splits each arg register's initial
        // value (the parameter local) from every later write, which is what
        // keeps ldarg reads and accumulator writes from desyncing
        context.ControlFlowGraph = new ISILControlFlowGraph(il);
        context.ParameterOperands = instructionSet.GetParameterOperandsFromMethod(context);
        StackAnalyzer.Analyze(context);
        context.DominatorInfo = new DominatorInfo(context.ControlFlowGraph);
        SsaForm.Build(context);
        LocalVariables.CreateAll(context);
        SsaForm.Remove(context);
        context.AnalysisWarnings = [];
        // every local in this method is a float — untyped locals would emit
        // object-typed arithmetic, which IlGenerator cannot recover
        foreach (var local in context.Locals)
            local.Type = single;

        var module = new ModuleDefinition("OutQuinticFixture.dll",
            new AssemblyReference("System.Private.CoreLib", typeof(object).Assembly.GetName().Version!));
        var singlePlaceholder = new TypeDefinition("System", "Single", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(singlePlaceholder);
        single.PutExtraData("AsmResolverType", singlePlaceholder);
        var type = new TypeDefinition("Tests", "OutQuintic", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("OutQuintic", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Single,
                [module.CorLibTypeFactory.Single, module.CorLibTypeFactory.Single, module.CorLibTypeFactory.Single]));
        type.Methods.Add(method);
        // ParameterForLocal maps analysis parameters to the emitted signature
        // by name — without these the args would emit as default-initialized locals
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "t", 0));
        method.ParameterDefinitions.Add(new ParameterDefinition(2, "b", 0));
        method.ParameterDefinitions.Add(new ParameterDefinition(3, "c", 0));

        IlGenerator.GenerateIl(context, method);
        // The fixture game's locals arrive untyped; every local in this method is a float.
        foreach (var local in method.CilMethodBody!.LocalVariables)
            local.VariableType = module.CorLibTypeFactory.Single;

        var assembly = new AssemblyDefinition("OutQuinticFixture", new Version(1, 0));
        assembly.Modules.Add(module);
        using var stream = new System.IO.MemoryStream();
        module.Write(stream);
        var loaded = System.Reflection.Assembly.Load(stream.ToArray());
        var actual = loaded.GetType("Tests.OutQuintic")!.GetMethod("OutQuintic")!.Invoke(null, [t, b, c]);
        Assert.That((float)actual!, Is.EqualTo(ReferenceOutQuintic(t, b, c)).Within(1e-5f));
    }
}
