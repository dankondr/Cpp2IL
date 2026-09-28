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

// Recovery cluster: compile bucket invalid-conversion - a vector binop whose
// destination is a scalarized register view (Vn / Vn.Sk). The lifter models a
// SIMD register's lane windows as independent locals, so one physical register
// hosts several lifetimes: a vector operator writes it on one, a scalar convert
// or lane write on a sibling. When the sibling's scalar seed reaches the vector
// def site's version first, the def's local locks in a type that cannot hold
// the vector result, and emission renders it as an invalid `(int)(vec * x)`
// store. The def site's own lifetime needs its own vector-typed local; scalar
// consumers of that lifetime then read the lane-0 field via the operand
// splitter, while the sibling lifetime keeps its scalar type.
public class VectorRegisterViewDefSiteSplitTests
{
    private static InjectedTypeAnalysisContext Vector3(ApplicationAnalysisContext app)
    {
        var vector = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "UnityEngine", "Vector3", app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        var offset = 0;
        foreach (var name in new[] { "x", "y", "z" })
        {
            vector.Fields.Add(new InjectedFieldAnalysisContext(name, app.SystemTypes.SystemSingleType,
                R.FieldAttributes.Public, vector, offset));
            offset += 4;
        }

        return vector;
    }

    private static void InjectVectorMultiply(InjectedTypeAnalysisContext vector, ModuleDefinition module,
        ApplicationAnalysisContext app)
    {
        var vectorDef = vector.GetExtraData<TypeDefinition>("AsmResolverType")!;
        foreach (var field in vector.Fields.OfType<InjectedFieldAnalysisContext>())
        {
            var fieldDefinition = new FieldDefinition(field.Name, FieldAttributes.Public,
                new FieldSignature(module.CorLibTypeFactory.Single));
            vectorDef.Fields.Add(fieldDefinition);
            field.PutExtraData("AsmResolverField", fieldDefinition);
        }

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
    }

    [Test]
    public void ScalarSeededRegisterViewVectorDefSiteGetsOwnLocal()
    {
        // V0.S0 carries two lifetimes: a lane-width-marked multiply def (v6) and a
        // scalar move def (v9). On development the width marker seeds the multiply's
        // version Int32, so `vec * arg` stores into an int local; the split gives the
        // multiply's def site a Vector3 local while the sibling move keeps its own.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = Vector3(app);
        var module = new ModuleDefinition("VectorOps.dll");
        SeedCorLibTypes(app, module, vector, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemSingleType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType);
        InjectVectorMultiply(vector, module, app);

        var vec = new LocalVariable("vec", new Register(null, "V1", 1)) { Type = vector };
        var arg = new LocalVariable("arg", new Register(null, "S2", 3))
            { Type = app.SystemTypes.SystemSingleType };
        var result = new LocalVariable("result", new Register(null, "V0.S0", 6));
        var laneView = new LocalVariable("laneView", new Register(null, "V0.S0", 9));
        var lane = new LocalVariable("lane", new Register(null, "S8", 1))
            { Type = app.SystemTypes.SystemSingleType };
        var sink = new LocalVariable("sink", new Register(null, "V2", 1)) { Type = vector };

        var multiply = new Instruction(0, OpCode.Multiply, result, vec, arg)
        {
            // The scalarizer marks 32-bit lane writes with their native width; when
            // such a write shares the view, its marker is the seed that smears the
            // binop's def site.
            NativeIntegerWidthBits = 32,
        };
        var (caller, method) = ForeignCaller(app, module, [
            multiply,
            new(1, OpCode.Move, sink, result),
            new(2, OpCode.Move, laneView, arg),
            new(3, OpCode.Move, lane, result),
            new(4, OpCode.Return)], [vec, arg, result, laneView, lane, sink]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var split = (LocalVariable)multiply.Operands[0];
        var laneRead = caller.ControlFlowGraph!.Instructions.Single(
            i => i.OpCode == OpCode.Move && ReferenceEquals(i.Destination, lane));
        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(split, Is.Not.SameAs(result),
                "the def site's lifetime gets a fresh local off the register view");
            Assert.That(split.Type?.FullName, Is.EqualTo("UnityEngine.Vector3"),
                "the split local carries the vector result type");
            Assert.That(result.Type?.FullName, Is.EqualTo("System.Int32"),
                "the register view keeps the sibling lifetime's scalar seed");
            Assert.That(laneView.Type?.FullName, Is.EqualTo("System.Single"),
                "the scalar-conversion lifetime keeps its own type");
            Assert.That(caller.ControlFlowGraph.Instructions
                    .SelectMany(i => i.Operands)
                    .OfType<LocalVariable>()
                    .Any(local => ReferenceEquals(local, result)), Is.False,
                "no operand still reads the orphaned scalar-typed def local");
            // The scalar consumer of the def site's value reads the vector's lane-0
            // field - the slot a scalar register view actually sees.
            Assert.That(laneRead.Operands[1], Is.TypeOf<FieldReference>(),
                () => laneRead.ToString());
            Assert.That(((FieldReference)laneRead.Operands[1]).Field.Name, Is.EqualTo("x"));
            Assert.That(((FieldReference)laneRead.Operands[1]).Local, Is.SameAs(split));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString()?.Contains("op_Multiply") == true), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldfld), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr && i.Operand is string text
                    && text.Contains("synthetic default value")), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void ScalarPhiMergedRegisterViewDoesNotTypeVectorDefSite()
    {
        // A phi merging the register's scalar lifetime with a vector binop's def
        // version back-propagates the scalar seed onto the def site. For that to
        // reach the def version, both multiply operands stay untyped until after
        // the phi runs (their typing moves come later in the list). The split
        // retargets the phi input to the vector local, leaving the merge result -
        // and the sibling lifetime - scalar.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector = Vector3(app);
        var module = new ModuleDefinition("VectorOps.dll");
        SeedCorLibTypes(app, module, vector, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemSingleType, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType);

        var vecParam = new LocalVariable("vecParam", new Register(null, "X0", 0)) { Type = vector };
        var argParam = new LocalVariable("argParam", new Register(null, "X1", 0))
            { Type = app.SystemTypes.SystemSingleType };
        var vec = new LocalVariable("vec", new Register(null, "V1", 2));
        var arg = new LocalVariable("arg", new Register(null, "S2", 1));
        var converted = new LocalVariable("converted", new Register(null, "W3", 1))
            { Type = app.SystemTypes.SystemInt32Type };
        var result = new LocalVariable("result", new Register(null, "V0.S0", 6));
        var scalarView = new LocalVariable("scalarView", new Register(null, "V0.S0", 8));
        var merged = new LocalVariable("merged", new Register(null, "V0.S0", 10));

        var multiply = new Instruction(0, OpCode.Multiply, result, vec, arg);
        var phi = new Instruction(3, OpCode.Phi, merged, scalarView, result);
        var (caller, _) = ForeignCaller(app, module, [
            multiply,
            new(1, OpCode.Move, scalarView, converted),
            phi,
            new(4, OpCode.Move, vec, vecParam),
            new(5, OpCode.Move, arg, argParam),
            new(6, OpCode.Return)],
            [vec, arg, converted, result, scalarView, merged, vecParam, argParam]);

        LocalVariables.ResolveTypesAndFields(caller);

        var split = (LocalVariable)multiply.Operands[0];
        Assert.Multiple(() =>
        {
            Assert.That(split, Is.Not.SameAs(result));
            Assert.That(split.Type?.FullName, Is.EqualTo("UnityEngine.Vector3"),
                "the phi's scalar seed must not lock the vector def site's type");
            Assert.That(scalarView.Type?.FullName, Is.EqualTo("System.Int32"));
            Assert.That(merged.Type?.FullName, Is.EqualTo("System.Int32"),
                "the merge keeps the scalar type of its remaining inputs");
            Assert.That(phi.Operands[2], Is.SameAs(split),
                "the phi input reads the vector def site's own local");
        });
    }
}
