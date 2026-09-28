using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: compile bucket invalid-conversion - the vector/scalar binop
// shape. A VectorN scalar binop (vector * float, vector / int, -vector) is one
// arithmetic op whose result register holds a vector. Typing that local with a
// consumer's scalar view made the emission store a VectorN result into an
// int/float/double local, which ilspy renders as the invalid `(double)(v * x)`
// cast. The vector operand proves the result type, so the local carries the
// vector and the consumer is emitted from it - or drops to the decompiler-issue
// diagnostic when no conversion exists.
public class VectorOperatorResultTypingTests
{
    private static (InjectedTypeAnalysisContext Vector, LocalVariable Vec, LocalVariable Scalar,
        LocalVariable Result, LocalVariable Slot) BuildOperands(ApplicationAnalysisContext app,
        string slotTypeName = "System.Double")
    {
        var vector = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "UnityEngine", "Vector3", app.SystemTypes.SystemValueTypeType, R.TypeAttributes.Public);
        var vec = new LocalVariable("vec", new Register(null, "vec")) { Type = vector };
        var scalar = new LocalVariable("scalar", new Register(null, "scalar"))
            { Type = app.SystemTypes.SystemSingleType };
        var result = new LocalVariable("result", new Register(null, "result"));
        var slot = new LocalVariable("slot", new Register(null, "slot"))
            { Type = slotTypeName == "System.Double"
                ? app.SystemTypes.SystemDoubleType
                : app.SystemTypes.SystemSingleType };
        return (vector, vec, scalar, result, slot);
    }

    [Test]
    public void VectorScalarMultiplyResultKeepsVectorType()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var (vector, vec, scalar, result, slot) = BuildOperands(app);
        var module = new ModuleDefinition("VectorOps.dll");
        SeedCorLibTypes(app, module, vector, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemSingleType, app.SystemTypes.SystemDoubleType,
            app.SystemTypes.SystemVoidType);
        var vectorDef = vector.GetExtraData<TypeDefinition>("AsmResolverType")!;
        var vectorSig = vectorDef.ToTypeSignature();
        var opDef = new MethodDefinition("op_Multiply",
            MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.SpecialName
                | MethodAttributes.HideBySig,
            MethodSignature.CreateStatic(vectorSig, [vectorSig, module.CorLibTypeFactory.Single]));
        vectorDef.Methods.Add(opDef);
        var opMultiply = vector.InjectMethodContext("op_Multiply", vector,
            R.MethodAttributes.Public | R.MethodAttributes.Static | R.MethodAttributes.SpecialName
                | R.MethodAttributes.HideBySig,
            vector, app.SystemTypes.SystemSingleType);
        opMultiply.PutExtraData("AsmResolverMethod", opDef);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Multiply, result, vec, scalar),
            new(1, OpCode.Move, slot, result),
            new(2, OpCode.Return)], [vec, scalar, result, slot]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(result.Type?.FullName, Is.EqualTo("UnityEngine.Vector3"),
                "the vector operator's result local is the vector, not the consumer's scalar view");
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString().Contains("op_Multiply") == true), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            // The double-typed consumer has no conversion from a vector: it is
            // the diagnosed synthetic default, not a stloc of a vector into a
            // double slot.
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr && i.Operand is string text
                    && text.Contains("synthetic default value")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_R8), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void VectorDividedByIntegerResultKeepsVectorType()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var (vector, vec, scalar, result, _) = BuildOperands(app);
        scalar.Type = app.SystemTypes.SystemInt32Type;
        var module = new ModuleDefinition("VectorOps.dll");
        SeedCorLibTypes(app, module, vector, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemSingleType, app.SystemTypes.SystemVoidType);
        var (caller, _) = ForeignCaller(app, module, [
            new(0, OpCode.Divide, result, vec, scalar),
            new(1, OpCode.Return)], [vec, scalar, result]);

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.That(result.Type?.FullName, Is.EqualTo("UnityEngine.Vector3"),
            "the integer-typed operand must not type the vector operator's result as int32");
    }

    [Test]
    public void VectorNegateResultKeepsVectorType()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var (vector, vec, _, result, slot) = BuildOperands(app, "System.Single");
        var module = new ModuleDefinition("VectorOps.dll");
        SeedCorLibTypes(app, module, vector, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemSingleType, app.SystemTypes.SystemVoidType);
        var (caller, _) = ForeignCaller(app, module, [
            new(0, OpCode.Negate, result, vec),
            new(1, OpCode.Move, slot, result),
            new(2, OpCode.Return)], [vec, result, slot]);

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.That(result.Type?.FullName, Is.EqualTo("UnityEngine.Vector3"),
            "a negated vector's result local is the vector, not the consumer's float view");
    }
}
