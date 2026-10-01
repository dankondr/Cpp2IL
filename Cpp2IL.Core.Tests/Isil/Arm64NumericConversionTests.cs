using System;
using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Tests.Regression;
using Disarm;
using ReflectionMethodAttributes = System.Reflection.MethodAttributes;

namespace Cpp2IL.Core.Tests.Isil;

// Scalar ARM64 numeric conversions (fcvt*/scvtf/ucvtf family) are conversions,
// not moves: the result's type is the destination register's width, and copy
// forwarding must not merge an integer with the float it was converted from.
// `fmov` between the integer and FP banks stays a bit move. These tests assert
// only the emitted behaviour, so they compile against the control lifter and
// fail there on the diagnosed merge.
public class Arm64NumericConversionTests
{
    private const uint Ret = 0xd65f03c0;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        // Unity 6 metadata keeps the full System.Math/System.MathF surface.
        TestGameLoader.LoadSimpleV106Game();
    }

    private static List<Instruction> Lift(params uint[] words)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Test",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        return new NewArmV8InstructionSet().ConvertInstructions(
            Disassembler.Disassemble(Blob(words), 0), context);
    }

    private static byte[] Blob(uint[] words)
    {
        var bytes = new byte[words.Length * 4];
        for (var i = 0; i < words.Length; i++)
            BitConverter.GetBytes(words[i]).CopyTo(bytes, i * 4);
        return bytes;
    }

    // Runs the same analysis spine the real pipeline does - SSA construction,
    // type resolution, copy simplification, SSA removal - so the local types and
    // emitted IL reflect what a recovered method would carry.
    private static MethodAnalysisContext AnalyzeLifted(uint[] words,
        TypeAnalysisContext returnType, TypeAnalysisContext[] parameters)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var instructionSet = new NewArmV8InstructionSet();
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            returnType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static,
            parameters, parameters.Select((_, i) => $"a{i}").ToArray());
        var il = instructionSet.ConvertInstructions(Disassembler.Disassemble(Blob(words), 0x10000), context);
        context.ControlFlowGraph = new ISILControlFlowGraph(il);
        context.ParameterOperands = instructionSet.GetParameterOperandsFromMethod(context);
        StackAnalyzer.Analyze(context);
        context.DominatorInfo = new DominatorInfo(context.ControlFlowGraph);
        SsaForm.Build(context);
        LocalVariables.CreateAll(context);
        LocalVariables.ResolveTypesAndFields(context);
        SsaSimplifier.Run(context);
        SsaForm.Remove(context);
        context.AnalysisWarnings = [];
        return context;
    }

    private static (ModuleDefinition module, MethodDefinition method) EmitIntoModule(
        MethodAnalysisContext context, TypeAnalysisContext[] parameters)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("NumericConversionFixture.dll",
            new AssemblyReference("System.Private.CoreLib", typeof(object).Assembly.GetName().Version!));
        SyntheticFixture.SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemBooleanType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemInt64Type,
            app.SystemTypes.SystemUInt32Type, app.SystemTypes.SystemUInt64Type,
            app.SystemTypes.SystemSingleType, app.SystemTypes.SystemDoubleType);
        var type = new TypeDefinition("Tests", "Run", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var returnType = context.ReturnType.FullName switch
        {
            "System.Int32" => module.CorLibTypeFactory.Int32,
            "System.Int64" => module.CorLibTypeFactory.Int64,
            "System.Single" => module.CorLibTypeFactory.Single,
            "System.Double" => module.CorLibTypeFactory.Double,
            _ => module.CorLibTypeFactory.Void,
        };
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(returnType, parameters.Select(p => p.FullName switch
            {
                "System.Int32" => module.CorLibTypeFactory.Int32,
                "System.Int64" => module.CorLibTypeFactory.Int64,
                "System.Single" => module.CorLibTypeFactory.Single,
                "System.Double" => module.CorLibTypeFactory.Double,
                _ => module.CorLibTypeFactory.Object,
            })));
        type.Methods.Add(method);
        for (var i = 0; i < parameters.Length; i++)
            method.ParameterDefinitions.Add(new ParameterDefinition((ushort)(i + 1), $"a{i}", 0));

        IlGenerator.GenerateIl(context, method);
        return (module, method);
    }

    private static object? EmitAndInvoke(uint[] words, TypeAnalysisContext returnType,
        TypeAnalysisContext[] parameters, object[] args)
    {
        var context = AnalyzeLifted(words, returnType, parameters);
        var (module, method) = EmitIntoModule(context, parameters);
        var factory = module.CorLibTypeFactory;
        foreach (var local in method.CilMethodBody!.LocalVariables)
        {
            var mapped = local.VariableType.FullName switch
            {
                "System.Int32" or "System.UInt32" or "System.Boolean" => factory.Int32,
                "System.Int64" or "System.UInt64" => factory.Int64,
                "System.Single" => factory.Single,
                "System.Double" => factory.Double,
                _ => factory.Object,
            };
            local.VariableType = mapped;
        }

        var assembly = new AssemblyDefinition("NumericConversionFixture", new Version(1, 0));
        assembly.Modules.Add(module);
        using var stream = new System.IO.MemoryStream();
        module.Write(stream);
        var loaded = System.Reflection.Assembly.Load(stream.ToArray());
        return loaded.GetType("Tests.Run")!.GetMethod("Run")!.Invoke(null, args);
    }

    private static IEnumerable<string> Diagnostics(MethodDefinition method) =>
        method.CilMethodBody!.Instructions
            .Where(i => i.OpCode == CilOpCodes.Ldstr)
            .Select(i => i.Operand as string ?? "");

    // `fmov` between the GPR and FP banks is a register-width bit move, not a
    // numeric conversion - it keeps lifting as a plain Move.
    [Test]
    public void FmovBetweenBanksStaysBitMove()
    {
        foreach (var (word, mnemonic) in new[]
        {
            (0x9e670101u, "fmov d1, x8"),  // GPR -> FP
            (0x9e660008u, "fmov x8, d0"),  // FP -> GPR
            (0x1e260000u, "fmov w0, s0"),  // FP -> GPR, 32-bit
        })
        {
            var il = Lift(word);
            Assert.That(il.All(i => i.OpCode is OpCode.Move or OpCode.Nop or OpCode.Return), Is.True,
                $"0x{word:x8} {mnemonic}: {string.Join(" | ", il)}");
        }
    }

    // The IL2CPP saturating cast: w19 = d0 == d1 ? 0x80000000 : (int)d0.
    // With the conversion lifted as a Move, copy forwarding types the merged
    // W19 Double and the -2147483648 literal cannot fill the slot. As a
    // Convert, both phi edges are Int32 and the literal fills it.
    [Test]
    public void FcvtzsCselSaturationFillsAnIntSlot()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var words = new uint[]
        {
            0x1e780008, // fcvtzs w8, d0
            0x52b0001c, // mov w28, #-0x80000000
            0x1e612000, // fcmp d0, d1
            0x1a880393, // csel w19, w28, w8, eq
            0x2a1303e0, // mov w0, w19
            Ret,
        };
        var context = AnalyzeLifted(words, app.SystemTypes.SystemInt32Type,
            [app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemDoubleType]);
        var (module, method) = EmitIntoModule(context,
            [app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemDoubleType]);

        Assert.Multiple(() =>
        {
            Assert.That(method.CilMethodBody!.LocalVariables.Any(local =>
                local.VariableType.FullName == "System.Int32"), Is.True);
            Assert.That(Diagnostics(method).Where(d => d.Contains("cannot fill")), Is.Empty,
                string.Join(" | ", Diagnostics(method)));
            Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Conv_I4), Is.True);
            Assert.That(method.CilMethodBody!.Instructions.Any(i =>
                i.OpCode == CilOpCodes.Ldc_I4
                && i.Operand is int value && value == int.MinValue), Is.True);
        });
    }

    [Test]
    public void FcvtzsCselSaturationExecutesTruncatingSemantics()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var result = EmitAndInvoke([
            0x1e780008, // fcvtzs w8, d0
            0x52b0001c, // mov w28, #-0x80000000
            0x1e612000, // fcmp d0, d1
            0x1a880393, // csel w19, w28, w8, eq
            0x2a1303e0, // mov w0, w19
            Ret,
        ], app.SystemTypes.SystemInt32Type,
            [app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemDoubleType], [3.7, 0.0]);
        Assert.That(result, Is.EqualTo(3));

        result = EmitAndInvoke([
            0x1e780008, 0x52b0001c, 0x1e612000, 0x1a880393, 0x2a1303e0, Ret,
        ], app.SystemTypes.SystemInt32Type,
            [app.SystemTypes.SystemDoubleType, app.SystemTypes.SystemDoubleType], [1.5, 1.5]);
        Assert.That(result, Is.EqualTo(int.MinValue));
    }

    // The fixed-point form scvtf s, w, #fbits converts the integer and scales
    // it by 2^-fbits: 7 with 2 fraction bits is 1.75.
    [Test]
    public void ScvtfFixedPointExecutesScaledSemantics()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var result = EmitAndInvoke([
            0x528000e1, // mov w1, #7
            0x1e02f820, // scvtf s0, w1, #2
            Ret,
        ], app.SystemTypes.SystemSingleType, [], []);
        Assert.That(result, Is.EqualTo(1.75f));
    }

    // fcvtzs w, s, #fbits scales by 2^fbits before truncating.
    [Test]
    public void FcvtzsFixedPointExecutesScaledSemantics()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var result = EmitAndInvoke([
            0x1e18e800, // fcvtzs w0, s0, #6
            Ret,
        ], app.SystemTypes.SystemInt32Type, [app.SystemTypes.SystemSingleType], [0.25f]);
        Assert.That(result, Is.EqualTo(16));
    }

    // scvtf of an integer constant converts the number, never its bit pattern.
    [Test]
    public void ScvtfOfIntegerConstantEmitsTheNumber()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var context = AnalyzeLifted([
            0x528000e1, // mov w1, #7
            0x1e220020, // scvtf s0, w1
            Ret,
        ], app.SystemTypes.SystemSingleType, []);
        var (module, method) = EmitIntoModule(context, []);

        Assert.Multiple(() =>
        {
            Assert.That(Diagnostics(method).Where(d => d.Contains("cannot fill")), Is.Empty,
                string.Join(" | ", Diagnostics(method)));
            Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Conv_R4), Is.True);
            Assert.That(method.CilMethodBody!.Instructions.Any(i =>
                i.OpCode == CilOpCodes.Ldc_I4 && i.Operand is int value && value == 7), Is.True,
                "the constant converts as the number 7, not as a float bit pattern");
        });
    }
}
