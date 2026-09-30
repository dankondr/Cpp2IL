using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: ambiguity/misuse errors under real reference assemblies
// (castle-recovery#133 — CS0104/CS0118/CS0121 in the reference-mode compile).
// All 93 sites classify as ilspy-owned: every emitted operand is
// signature-exact and every colliding name is a real type or namespace, so the
// ambiguity lives in the decompiler's name/cast emission (a stripped
// decompile-time reference view that hid the second candidate) or, for the
// CS0118 `Type`/`Google.Type` collision, in the compile driver's
// all-of-refdir reference set. These tests pin the emission contract the
// verdict rests on: a call bound to one overload among same-name siblings
// emits exactly that signature, and a widened numeric argument keeps its
// explicit conv — the two facts that place the fault downstream of Cpp2IL.
public class AmbiguityOperandFidelityTests
{
    private static ApplicationAnalysisContext App => Cpp2IlApi.CurrentAppContext!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    // A Tests.Math holder with Ceiling(System.Double)/Ceiling(System.Int32)
    // siblings — the same-name overload pair the real System.Math reference
    // adds next to the recovered float64-only one.
    private static (InjectedMethodAnalysisContext f64, MethodDefinition f64Def,
        ModuleDefinition module)
        NewOverloadFixture(ApplicationAnalysisContext app)
    {
        var f64 = app.SystemTypes.SystemDoubleType;
        var i32 = app.SystemTypes.SystemInt32Type;
        var mathType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "Tests", "Math", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var f64Ctx = mathType.InjectMethodContext("Ceiling", f64,
            R.MethodAttributes.Public | R.MethodAttributes.Static, f64);
        var i32Ctx = mathType.InjectMethodContext("Ceiling", f64,
            R.MethodAttributes.Public | R.MethodAttributes.Static, i32);

        var module = new ModuleDefinition("Ambiguity.dll");
        var mathDefinition = new TypeDefinition("Tests", "Math",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(mathDefinition);
        mathType.PutExtraData("AsmResolverType", mathDefinition);
        var f64Def = new MethodDefinition("Ceiling",
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Double,
                [module.CorLibTypeFactory.Double]));
        var i32Def = new MethodDefinition("Ceiling",
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Double,
                [module.CorLibTypeFactory.Int32]));
        mathDefinition.Methods.Add(f64Def);
        mathDefinition.Methods.Add(i32Def);
        f64Ctx.PutExtraData("AsmResolverMethod", f64Def);
        i32Ctx.PutExtraData("AsmResolverMethod", i32Def);
        return (f64Ctx, f64Def, module);
    }

    [Test]
    public void OverloadedCallBindsTheExactSignature()
    {
        var app = App;
        var (f64, _, module) = NewOverloadFixture(app);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemDoubleType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemVoidType);
        var arg = new LocalVariable("arg", new Register(null, "arg"))
            { Type = app.SystemTypes.SystemDoubleType };
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemDoubleType };
        var (caller, method) = ForeignCaller(app, module, [
            new(-1, OpCode.Move, arg, new Immediate(0)),
            new(0, OpCode.Call, f64, result, arg),
            new(1, OpCode.Return)], [arg, result]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var call = il.SingleOrDefault(i => i.OpCode == CilOpCodes.Call);
        Assert.That(call, Is.Not.Null,
            () => string.Join("\n", il.Select(i => i.ToString())));
        var operand = (IMethodDescriptor)call!.Operand!;
        Assert.Multiple(() =>
        {
            Assert.That(operand.Name?.ToString(), Is.EqualTo("Ceiling"));
            // The emitted call binds the float64 sibling by signature, not by name.
            Assert.That(operand.Signature!.ParameterTypes.Select(t => t.FullName),
                Is.EqualTo(new[] { "System.Double" }));
            Assert.That(operand.Signature.ReturnType.FullName, Is.EqualTo("System.Double"));
        });
    }

    [Test]
    public void WidenedNumericArgumentKeepsExplicitConversion()
    {
        var app = App;
        var (f64, _, module) = NewOverloadFixture(app);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemDoubleType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemVoidType);
        var num = new LocalVariable("num", new Register(null, "num"))
            { Type = app.SystemTypes.SystemInt32Type };
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemDoubleType };
        var (caller, method) = ForeignCaller(app, module, [
            new(-1, OpCode.Move, num, new Immediate(5)),
            new(0, OpCode.Call, f64, result, num),
            new(1, OpCode.Return)], [num, result]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var callIndex = Enumerable.Range(0, il.Count)
            .FirstOrDefault(i => il[i].OpCode == CilOpCodes.Call);
        Assert.That(callIndex, Is.GreaterThan(0),
            () => string.Join("\n", il.Select(i => i.ToString())));
        // An Int32 argument into the float64 parameter keeps conv.r8 in the IL;
        // the decompiler may print the argument implicitly, but the conversion
        // is real — this is the operand fidelity the CS0121 verdict rests on.
        Assert.That(il.Take(callIndex).Any(i => i.OpCode == CilOpCodes.Conv_R8), Is.True,
            () => string.Join("\n", il.Select(i => i.ToString())));
    }
}
