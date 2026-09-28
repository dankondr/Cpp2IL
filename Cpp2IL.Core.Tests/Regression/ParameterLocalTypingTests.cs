using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: parameter typing — a parameter whose register never
// appears in the lifted instructions produces no local, so ParameterLocals has
// a hole where its parameter index stood. Re-mapping params onto locals
// positionally then shifts every later local onto the preceding parameter's
// type: an `out` parameter's local lands on a plain parameter type, a store
// through it stops being a managed-pointer store, and the emitted body writes
// a private pointer local instead of the out cell (CS0177 on the ilspy tree).
public class ParameterLocalTypingTests
{
    [Test]
    public void OutParameterLocalKeepsItsOwnParameterType()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var objectType = app.SystemTypes.SystemObjectType;
        var int32 = app.SystemTypes.SystemInt32Type;
        var voidType = app.SystemTypes.SystemVoidType;
        var objectByRef = new ByRefTypeAnalysisContext(objectType);

        // Registers x0..x2 carry p0, p1, p2; the lifted body only ever touches
        // x2, so p0's and p1's registers produce no locals.
        var pointerSize = app.Binary.PointerSizeBytes;
        var callerType = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "ForeignCaller", objectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = new InjectedMethodAnalysisContext(callerType, "Run", voidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static,
            [int32, int32, objectByRef],
            ["p0", "p1", "p2"],
            [R.ParameterAttributes.None, R.ParameterAttributes.None, R.ParameterAttributes.Out]);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move,
                new MemoryOperand(new Register(2, "X2"), accessSize: pointerSize), new Immediate(0)),
            new Instruction(1, OpCode.Return)]);
        caller.ParameterOperands = [new Register(0, "X0"), new Register(1, "X1"), new Register(2, "X2")];
        caller.AnalysisWarnings = [];

        LocalVariables.CreateAll(caller);
        LocalVariables.ResolveTypesAndFields(caller);

        var resultLocal = caller.ParameterLocals.Single();
        Assert.That(resultLocal.Type, Is.TypeOf<ByRefTypeAnalysisContext>(),
            "the `out` parameter local must keep its own parameter type even though "
            + "the earlier parameter registers produced no locals");

        var module = new ModuleDefinition("OutParam.dll");
        SeedCorLibTypes(app, module, objectType, int32, voidType);
        var owner = new TypeDefinition("Tests", "ForeignCaller", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
            [
                module.CorLibTypeFactory.Int32,
                module.CorLibTypeFactory.Int32,
                module.CorLibTypeFactory.Object.MakeByReferenceType()
            ]));
        owner.Methods.Add(method);
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "p0", default));
        method.ParameterDefinitions.Add(new ParameterDefinition(2, "p1", default));
        method.ParameterDefinitions.Add(new ParameterDefinition(3, "p2", ParameterAttributes.Out));

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldarg), Is.True,
                "a store through an out-parameter local loads the parameter's managed pointer\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stind_Ref), Is.True,
                "the store must write through the pointer (stind.ref), not clobber a pointer local\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stloc), Is.False,
                "storing into the pointer local leaves the out parameter unassigned\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }
}
