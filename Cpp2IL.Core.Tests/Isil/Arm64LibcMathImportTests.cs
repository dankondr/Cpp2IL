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
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Disarm;
using ReflectionMethodAttributes = System.Reflection.MethodAttributes;

namespace Cpp2IL.Core.Tests.Isil;

// Structural recovery of scalar libc math imports through ARM64 PLT/GOT
// veneers: adrp+ldr(+add)+br trampoline + dynamic-relocation symbol name on the
// pointer slot. No addresses are hard-coded — the fixture is fully synthetic.
public class Arm64LibcMathImportTests
{
    // The bl/b call target must lie inside the loaded fixture image so the
    // pre-call structural checks can read it; a small offset into .text is
    // never itself a method entry.
    private static ulong Veneer =>
        Cpp2IlApi.CurrentAppContext!.Binary.GetVirtualAddressOfPrimaryExecutableSection() + 0x40;

    // The synthetic call site sits just below the veneer so bl stays in range.
    private static ulong MethodVa => Veneer - 0x40;

    private const uint Ret = 0xd65f03c0;
    private const uint BrX17 = 0xd61f0220;
    private const uint BrX16 = 0xd61f0200;
    private const uint MovX0X1 = 0xaa0103e0;

    private static uint Bl(ulong pc, ulong target) => 0x94000000 | (uint)((target - pc) >> 2 & 0x03ffffff);
    private static uint B(ulong pc, ulong target) => 0x14000000 | (uint)((target - pc) >> 2 & 0x03ffffff);

    private static uint Adrp(int rd, long deltaBytes)
    {
        var imm = deltaBytes >> 12;
        var immlo = (uint)(imm & 0x3);
        var immhi = (uint)((imm >> 2) & 0x7ffff);
        return 0x90000000 | immlo << 29 | immhi << 5 | (uint)rd;
    }

    private static uint Ldr64(int rt, int rn, int byteOffset) =>
        0xf9400000 | (uint)((byteOffset / 8) << 10) | (uint)(rn << 5) | (uint)rt;

    private static uint Add64(int rd, int rn, int imm) =>
        0x91000000 | (uint)(imm << 10) | (uint)(rn << 5) | (uint)rd;

    private static ulong PageOf(ulong va) => va & ~0xfffUL;

    private static byte[] Blob(uint[] words)
    {
        var bytes = new byte[words.Length * 4];
        for (var i = 0; i < words.Length; i++)
            BitConverter.GetBytes(words[i]).CopyTo(bytes, i * 4);
        return bytes;
    }

    private static Func<ulong, uint?> Reader(IReadOnlyDictionary<ulong, uint> words) =>
        a => words.TryGetValue(a, out var w) ? w : null;

    private static Func<ulong, string?> SlotNames(IReadOnlyDictionary<ulong, string> names) =>
        a => names.TryGetValue(a, out var n) ? n : null;

    private static uint[] GotVeneerWords(long pageDelta, int slotOffset, bool withAdd) =>
        withAdd
            ? [Adrp(16, pageDelta), Ldr64(17, 16, slotOffset), Add64(16, 16, slotOffset), BrX17]
            : [Adrp(16, pageDelta), Ldr64(17, 16, slotOffset), BrX17];

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        // Unity 6 metadata keeps the full System.Math/System.MathF surface; the
        // 2019 game only carries the BCL members it actually used (Asin/Acos/
        // Atan2/Exp are absent and honestly lift as NotImplemented there).
        TestGameLoader.LoadSimpleV106Game();
    }

    [TestCase(true)]
    [TestCase(false)]
    public void GotVeneerImportResolvesRelocationSymbolName(bool withAdd)
    {
        foreach (var veneerVa in new[] { 0x80000UL, 0x7fff000UL })
        {
            // GOT page two pages above the veneer page, slot at +0x38
            var words = GotVeneerWords(0x2000, 0x38, withAdd);
            var slot = PageOf(veneerVa) + 0x2000 + 0x38;
            var dict = new Dictionary<ulong, uint>();
            for (var i = 0; i < words.Length; i++)
                dict[veneerVa + (ulong)i * 4] = words[i];

            var names = new Dictionary<ulong, string> { [slot] = "sinf" };
            Assert.That(NewArm64KeyFunctionAddresses.TryResolveGotVeneerImportName(
                    Reader(dict), SlotNames(names), veneerVa, out var name),
                Is.True, $"withAdd={withAdd} at {veneerVa:X}");
            Assert.That(name, Is.EqualTo("sinf"));
        }
    }

    [Test]
    public void GotVeneerWithoutRelocationNameDoesNotResolve()
    {
        var veneerVa = 0x80000UL;
        var words = GotVeneerWords(0x2000, 0x38, true);
        var dict = new Dictionary<ulong, uint>();
        for (var i = 0; i < words.Length; i++)
            dict[veneerVa + (ulong)i * 4] = words[i];

        // Valid veneer, but the slot carries no named relocation.
        Assert.That(NewArm64KeyFunctionAddresses.TryResolveGotVeneerImportName(
            Reader(dict), SlotNames(new Dictionary<ulong, string>()), veneerVa, out _), Is.False);
        // The slot has a name, but the wrong one: this is still structurally an
        // import — resolution returns the name and the whitelist decides.
        var wrongSlot = PageOf(veneerVa) + 0x2000 + 0x40;
        Assert.That(NewArm64KeyFunctionAddresses.TryResolveGotVeneerImportName(
            Reader(dict), SlotNames(new Dictionary<ulong, string> { [wrongSlot] = "sinf" }), veneerVa, out _), Is.False);
    }

    [Test]
    public void FloatImportBridgesToDoubleMathWhenMathFIsAbsent()
    {
        // 2019-era corlib has System.Math but no System.MathF: a single-precision
        // import bridges through the double overload with float32 width marks,
        // exactly like the scalar fsqrt/fsin emission paths.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();

        var il = LiftVoid([Bl(MethodVa, Veneer)], _ => _ == Veneer ? "sinf" : null);

        var call = il.FirstOrDefault(i => i.OpCode == OpCode.Call);
        Assert.That(call, Is.Not.Null, "no call emitted for sinf");
        var callee = call!.Operands[0] as MethodAnalysisContext;
        Assert.That(callee?.Name, Is.EqualTo("Sin"));
        Assert.That(callee?.DeclaringType?.FullName, Is.EqualTo("System.Math"));
        Assert.That(call.NativeFloatWidthBits, Is.EqualTo(32));
        Assert.That(il.Any(i => i.OpCode == OpCode.Move
            && i.NativeFloatWidthBits == 32
            && i.Operands[1].Equals(new Register(null, "V0"))), Is.True,
            "sinf must bridge V0 through a float32-marked move into the double overload");
    }

    [Test]
    public void NamedSlotWithoutVeneerDoesNotResolve()
    {
        var address = 0x80000UL;
        var words = new Dictionary<ulong, uint>
        {
            [address] = MovX0X1,
            [address + 4] = Ret,
        };
        var names = new Dictionary<ulong, string> { [PageOf(address) + 0x38] = "sinf" };
        Assert.That(NewArm64KeyFunctionAddresses.TryResolveGotVeneerImportName(
            Reader(words), SlotNames(names), address, out _), Is.False);
    }

    private static List<Instruction> Lift(uint[] words, Func<ulong, string?>? resolver, TypeAnalysisContext returnType)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Test",
            returnType, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, []);
        return new NewArmV8InstructionSet().ConvertInstructions(
            Disassembler.Disassemble(Blob(words), MethodVa), context, resolver);
    }

    private static List<Instruction> LiftVoid(uint[] words, Func<ulong, string?>? resolver)
        => Lift(words, resolver, Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemVoidType);

    [TestCase("sinf", "Sin", 1)]
    [TestCase("cosf", "Cos", 1)]
    [TestCase("tanf", "Tan", 1)]
    [TestCase("asinf", "Asin", 1)]
    [TestCase("acosf", "Acos", 1)]
    [TestCase("atanf", "Atan", 1)]
    [TestCase("expf", "Exp", 1)]
    [TestCase("logf", "Log", 1)]
    [TestCase("atan2f", "Atan2", 2)]
    [TestCase("powf", "Pow", 2)]
    [TestCase("sin", "Sin", 1)]
    [TestCase("cos", "Cos", 1)]
    [TestCase("tan", "Tan", 1)]
    [TestCase("asin", "Asin", 1)]
    [TestCase("acos", "Acos", 1)]
    [TestCase("atan", "Atan", 1)]
    [TestCase("exp", "Exp", 1)]
    [TestCase("log", "Log", 1)]
    [TestCase("atan2", "Atan2", 2)]
    [TestCase("pow", "Pow", 2)]
    public void ScalarMathImportLiftsToManagedCall(string import, string method, int argumentCount)
    {
        var il = LiftVoid([Bl(MethodVa, Veneer)], _ => _ == Veneer ? import : null);

        var call = il.FirstOrDefault(i => i.OpCode == OpCode.Call);
        Assert.That(call, Is.Not.Null, $"no call emitted for {import}");
        Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False,
            $"{import}: {string.Join(" | ", il.Where(i => i.OpCode == OpCode.NotImplemented))}");
        Assert.That(il.Any(i => i.Operands.FirstOrDefault() is StringLiteral), Is.False,
            $"{import} must not lift as a key-function string literal");

        var callee = call!.Operands[0] as MethodAnalysisContext;
        Assert.That(callee, Is.Not.Null, $"{import} call target is not a resolved method");
        Assert.That(callee!.Name, Is.EqualTo(method));
        Assert.That(callee.DeclaringType?.FullName,
            Is.AnyOf("System.MathF", "System.Math", "UnityEngine.Mathf"), $"{import} -> {callee}");
        Assert.That(callee.Parameters.Count, Is.EqualTo(argumentCount));

        // Scalar AAPCS64: destination and first arguments are V0/V1.
        Assert.That(call.Operands[1], Is.EqualTo(new Register(null, "V0")));
    }

    [TestCase("fmod", 64)]
    [TestCase("fmodf", 32)]
    public void FmodImportLiftsToTruncatedRemainder(string import, int width)
    {
        var il = LiftVoid([Bl(MethodVa, Veneer)], _ => _ == Veneer ? import : null);

        var modulo = il.FirstOrDefault(i => i.OpCode == OpCode.Modulo);
        Assert.That(modulo, Is.Not.Null, $"no remainder emitted for {import}");
        Assert.That(il.Any(i => i.OpCode == OpCode.Call), Is.False,
            $"{import} must not become a call (IEEERemainder has different semantics)");
        Assert.That(modulo!.NativeFloatWidthBits, Is.EqualTo(width));
        Assert.That(modulo.Operands[0], Is.EqualTo(new Register(null, "V0")));
        Assert.That(modulo.Operands[1], Is.EqualTo(new Register(null, "V0")));
        Assert.That(modulo.Operands[2], Is.EqualTo(new Register(null, "V1")));
    }

    [Test]
    public void TailCallToScalarMathImportRewritesAndReturns()
    {
        var il = LiftVoid([B(MethodVa, Veneer)], _ => _ == Veneer ? "sinf" : null);

        Assert.That(il.Any(i => i.OpCode == OpCode.Call
            && i.Operands[0] is MethodAnalysisContext { Name: "Sin" }), Is.True);
        Assert.That(il.Any(i => i.OpCode == OpCode.Return), Is.True);
    }

    [TestCase("memmove")]
    [TestCase("memcpy")]
    [TestCase("memset")]
    [TestCase("modf")]
    [TestCase("sincos")]
    [TestCase("sincosf")]
    [TestCase("__cxa_end_catch")]
    [TestCase("some_unknown_libc_symbol")]
    public void NonWhitelistedImportStaysUnresolved(string import)
    {
        var il = LiftVoid([Bl(MethodVa, Veneer)], _ => _ == Veneer ? import : null);

        var call = il.Single(i => i.OpCode == OpCode.Call);
        Assert.That(call.Operands[0], Is.EqualTo(new Immediate((long)Veneer)),
            $"{import} must keep its address operand");
        Assert.That(il.Any(i => i.Operands.FirstOrDefault() is StringLiteral), Is.False,
            $"{import} must not become a key-function string literal");
    }

    [Test]
    public void UnnamedTargetStaysUnresolved()
    {
        // Resolver has no relocation name for the veneer: unknown stays unknown.
        var il = LiftVoid([Bl(MethodVa, Veneer)], _ => null);
        Assert.That(il.Single(i => i.OpCode == OpCode.Call).Operands[0],
            Is.EqualTo(new Immediate((long)Veneer)));
    }

    [Test]
    public void ProductionBinaryWithoutRelocationsStaysUnresolved()
    {
        // The fixture games are PE binaries — no dynamic relocation names exist,
        // so the structural lookup finds nothing and the call keeps its address.
        var il = LiftVoid([Bl(MethodVa, Veneer)], null);
        Assert.That(il.Single(i => i.OpCode == OpCode.Call).Operands[0],
            Is.EqualTo(new Immediate((long)Veneer)));
    }

    // Emission + JIT: the lifted call/remainder runs the real analysis spine,
    // generates CIL into a module, and executes on the runtime. Math calls hit
    // a forwarding stub (AsmResolverMethod) that delegates to the genuine BCL
    // implementation, so the produced value is the real result.
    private static object? EmitAndInvoke(string importName, bool isDouble, object[] args)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var fp = isDouble ? app.SystemTypes.SystemDoubleType : app.SystemTypes.SystemSingleType;
        var parameters = args.Select(_ => fp).ToArray();
        var names = args.Select((_, i) => $"a{i}").ToArray();
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Proxy",
            fp, ReflectionMethodAttributes.Public | ReflectionMethodAttributes.Static, parameters, names);
        var instructionSet = new NewArmV8InstructionSet();
        var il = instructionSet.ConvertInstructions(
            Disassembler.Disassemble(Blob([Bl(MethodVa, Veneer), Ret]), MethodVa), context,
            va => va == Veneer ? importName : null);
        Assert.That(il.Any(i => i.OpCode == OpCode.NotImplemented), Is.False,
            $"{importName}: {string.Join(" | ", il.Where(i => i.OpCode == OpCode.NotImplemented))}");

        context.ControlFlowGraph = new ISILControlFlowGraph(il);
        context.ParameterOperands = instructionSet.GetParameterOperandsFromMethod(context);
        StackAnalyzer.Analyze(context);
        context.DominatorInfo = new DominatorInfo(context.ControlFlowGraph);
        SsaForm.Build(context);
        LocalVariables.CreateAll(context);
        SsaForm.Remove(context);
        context.AnalysisWarnings = [];
        foreach (var local in context.Locals)
            local.Type = fp;

        var module = new ModuleDefinition("LibcMathImportFixture.dll",
            new AssemblyReference("System.Private.CoreLib", typeof(object).Assembly.GetName().Version!));
        foreach (var systemType in new[] { app.SystemTypes.SystemSingleType, app.SystemTypes.SystemDoubleType })
            systemType.PutExtraData("AsmResolverType",
                new TypeDefinition("System", systemType.Name, TypeAttributes.Public, module.CorLibTypeFactory.Object.Type));

        // For a Call, the callee context emits through its AsmResolverMethod.
        // Give it a stub that forwards to the real System.Math implementation.
        var call = il.FirstOrDefault(i => i.OpCode == OpCode.Call);
        if (call?.Operands[0] is MethodAnalysisContext callee)
            SeedForwardingStub(module, callee);

        var type = new TypeDefinition("Tests", "Proxy", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var fpCorLib = isDouble ? module.CorLibTypeFactory.Double : module.CorLibTypeFactory.Single;
        var method = new MethodDefinition("Proxy", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(fpCorLib, args.Select(_ => fpCorLib)));
        type.Methods.Add(method);
        for (var i = 0; i < names.Length; i++)
            method.ParameterDefinitions.Add(new ParameterDefinition((ushort)(i + 1), names[i], 0));

        IlGenerator.GenerateIl(context, method);
        foreach (var local in method.CilMethodBody!.LocalVariables)
            local.VariableType = fpCorLib;

        var assembly = new AssemblyDefinition("LibcMathImportFixture", new Version(1, 0));
        assembly.Modules.Add(module);
        using var stream = new System.IO.MemoryStream();
        module.Write(stream);
        var loaded = System.Reflection.Assembly.Load(stream.ToArray());
        return loaded.GetType("Tests.Proxy")!.GetMethod("Proxy")!.Invoke(null, args);
    }

    private static void SeedForwardingStub(ModuleDefinition module, MethodAnalysisContext callee)
    {
        var factory = module.CorLibTypeFactory;
        var declaring = new TypeDefinition(callee.DeclaringType?.Namespace ?? "System",
            callee.DeclaringType?.Name ?? "Math", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(declaring);

        var toManaged = (TypeAnalysisContext t) => t.FullName == "System.Double" ? factory.Double : factory.Single;
        var parameters = callee.Parameters.Select(p => toManaged(p.ParameterType)).ToArray();
        var returnType = toManaged(callee.ReturnType);
        var stub = new MethodDefinition(callee.Name,
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(returnType, parameters));
        declaring.Methods.Add(stub);

        // Forward to the real corlib implementation, widening singles to
        // double — System.Math has a double overload for every mapped name.
        var realMath = factory.CorLibScope.CreateTypeReference("System", "Math");
        var realTarget = realMath.CreateMemberReference(callee.Name,
            MethodSignature.CreateStatic(factory.Double, parameters.Select(_ => factory.Double)));
        var body = new CilMethodBody();
        for (var i = 0; i < parameters.Length; i++)
        {
            body.Instructions.Add(i == 0 ? CilOpCodes.Ldarg_0 : CilOpCodes.Ldarg_1);
            if (parameters[i] == factory.Single)
                body.Instructions.Add(CilOpCodes.Conv_R8);
        }
        body.Instructions.Add(CilOpCodes.Call, realTarget);
        if (returnType == factory.Single)
            body.Instructions.Add(CilOpCodes.Conv_R4);
        body.Instructions.Add(CilOpCodes.Ret);
        stub.CilMethodBody = body;
        callee.PutExtraData("AsmResolverMethod", stub);
    }

    [Test]
    public void LiftedSinImportExecutesManagedSemantics()
    {
        var result = EmitAndInvoke("sin", isDouble: true, [0.75]);
        Assert.That(result, Is.EqualTo(Math.Sin(0.75)).Within(1e-12));
    }

    [Test]
    public void LiftedSinfImportExecutesManagedSemantics()
    {
        var result = EmitAndInvoke("sinf", isDouble: false, [0.5f]);
        Assert.That(result, Is.EqualTo(MathF.Sin(0.5f)).Within(1e-6f));
    }

    [Test]
    public void LiftedPowfImportExecutesManagedSemantics()
    {
        var result = EmitAndInvoke("powf", isDouble: false, [2f, 3f]);
        Assert.That(result, Is.EqualTo(MathF.Pow(2f, 3f)).Within(1e-6f));
    }

    [Test]
    public void LiftedFmodImportExecutesRemainderSemantics()
    {
        // C fmod truncates the quotient and keeps the dividend's sign;
        // Math.IEEERemainder rounds it (half-to-even) — the emitted `rem` must
        // agree with fmod, which is exactly what C# % lowers to.
        Assert.That(-5.5 % 2.0, Is.EqualTo(-1.5));
        Assert.That(Math.IEEERemainder(-5.5, 2.0), Is.EqualTo(0.5));
        Assert.That(5.5 % -2.0, Is.EqualTo(1.5));
        Assert.That(double.IsNaN(1.0 % 0.0), Is.True);
        Assert.That(double.IsNaN(double.PositiveInfinity % 2.0), Is.True);
        var floatDividend = -5.5f;
        Assert.That(floatDividend % 2f, Is.EqualTo(-1.5f));

        var result = EmitAndInvoke("fmod", isDouble: true, [-5.5, 2.0]);
        Assert.That(result, Is.EqualTo(-1.5));
        result = EmitAndInvoke("fmodf", isDouble: false, [5.5f, -2f]);
        Assert.That(result, Is.EqualTo(1.5f));
    }
}
