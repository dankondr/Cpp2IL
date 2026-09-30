using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: compile bucket invalid-conversion (castle-recovery#115).
// `Quaternion.Internal_ToEulerRad` decompiles to `get_eulerAngles` * 0.017453292.
// get_eulerAngles is an instance method on a value type, so the receiver must be
// emitted as `Quaternion&` - pushing the Quaternion value leaves ilspy rendering
// `((Quaternion*)local)->eulerAngles`, a CS0030 invalid conversion.
public class QuaternionReceiverEmissionTests
{
    private static (InjectedTypeAnalysisContext quaternion, InjectedTypeAnalysisContext vector,
        MethodAnalysisContext toEuler) QuaternionFixture(ApplicationAnalysisContext app,
        ModuleDefinition module)
    {
        var vector = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "UnityEngine", "Vector3", app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        var quaternion = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "UnityEngine", "Quaternion", app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        var single = app.SystemTypes.SystemSingleType;
        foreach (var (name, offset) in new[] { "x", "y", "z", "w" }.Select((n, i) => (n, i * 4)))
            quaternion.Fields.Add(new InjectedFieldAnalysisContext(name, single,
                R.FieldAttributes.Public, quaternion, offset));
        var multiply = vector.InjectMethodContext("op_Multiply", vector,
            R.MethodAttributes.Public | R.MethodAttributes.Static, vector, single);
        var getter = quaternion.InjectMethodContext("get_eulerAngles", vector,
            R.MethodAttributes.Public, []);
        var toEuler = quaternion.InjectMethodContext("Internal_ToEulerRad", vector,
            R.MethodAttributes.Public | R.MethodAttributes.Static, quaternion);

        SeedCorLibTypes(app, module, vector, quaternion, single,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType);
        var vectorDef = new TypeDefinition("UnityEngine", "Vector3",
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        var quaternionDef = new TypeDefinition("UnityEngine", "Quaternion",
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(vectorDef);
        module.TopLevelTypes.Add(quaternionDef);
        vector.PutExtraData("AsmResolverType", vectorDef);
        quaternion.PutExtraData("AsmResolverType", quaternionDef);
        var multiplyDef = new MethodDefinition("op_Multiply",
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(vectorDef.ToTypeSignature(),
                [vectorDef.ToTypeSignature(), module.CorLibTypeFactory.Single]));
        var getterDef = new MethodDefinition("get_eulerAngles", MethodAttributes.Public,
            MethodSignature.CreateInstance(vectorDef.ToTypeSignature()));
        vectorDef.Methods.Add(multiplyDef);
        quaternionDef.Methods.Add(getterDef);
        multiply.PutExtraData("AsmResolverMethod", multiplyDef);
        getter.PutExtraData("AsmResolverMethod", getterDef);
        return (quaternion, vector, toEuler);
    }

    private static void AssertStructReceiverIsAddress(MethodDefinition method)
    {
        var il = method.CilMethodBody!.Instructions;
        var call = il.FirstOrDefault(i => i.OpCode == CilOpCodes.Call
            && i.Operand?.ToString()?.Contains("get_eulerAngles") == true);
        Assert.That(call, Is.Not.Null,
            () => "expected a get_eulerAngles call:\n" + string.Join("\n", il.Select(i => i.ToString())));
        var index = il.IndexOf(call!);
        Assert.That(il[index - 1].OpCode, Is.EqualTo(CilOpCodes.Ldloca)
                .Or.EqualTo(CilOpCodes.Ldarga).Or.EqualTo(CilOpCodes.Ldflda)
                .Or.EqualTo(CilOpCodes.Ldelema).Or.EqualTo(CilOpCodes.Ldsflda),
            () => "the get_eulerAngles receiver must be a managed address (Quaternion&):\n"
                + string.Join("\n", il.Select(i => i.ToString())));
    }

    [Test]
    public void ToEulerRadLocalReceiverEmitsStructAddress()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("Quaternion.dll");
        var (quaternion, vector, toEuler) = QuaternionFixture(app, module);
        var quat = new LocalVariable("quat", new Register(null, "quat"), quaternion);
        var result = new LocalVariable("result", new Register(null, "result"), vector);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Call, toEuler, result, quat),
            new(1, OpCode.Return)], [quat, result]);

        IlGenerator.GenerateIl(caller, method);

        AssertStructReceiverIsAddress(method);
    }

    [Test]
    public void ToEulerRadNestedFieldReceiverEmitsContainerAddress()
    {
        // A whole-Quaternion SIMD read resolves to the field's first component
        // (`this.rotation.x`): the managed address of the rotation field itself is
        // the get_eulerAngles receiver.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("Quaternion.dll");
        var (quaternion, vector, toEuler) = QuaternionFixture(app, module);

        var owner = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Owner", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var rotation = new InjectedFieldAnalysisContext("rotation", quaternion,
            R.FieldAttributes.Public, owner, 16);
        owner.Fields.Add(rotation);
        var caller = owner.InjectMethodContext("Run", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public, []);
        var thisLocal = new LocalVariable("this", new Register(null, "this"), owner) { IsThis = true };
        var result = new LocalVariable("result", new Register(null, "result"), vector);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Call, toEuler, result,
                new FieldReference(quaternion.Fields.Single(field => field.Name == "x"),
                    thisLocal, 16, [rotation], 16)),
            new(1, OpCode.Return)]);
        caller.Locals = [thisLocal, result];
        caller.ParameterLocals = [thisLocal];
        caller.AnalysisWarnings = [];
        var ownerDef = new TypeDefinition("Tests", "Owner", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(ownerDef);
        owner.PutExtraData("AsmResolverType", ownerDef);
        var rotationDef = new FieldDefinition("rotation", FieldAttributes.Public,
            new FieldSignature(quaternion.GetExtraData<TypeDefinition>("AsmResolverType")!.ToTypeSignature()));
        ownerDef.Fields.Add(rotationDef);
        rotation.PutExtraData("AsmResolverField", rotationDef);
        var method = new MethodDefinition("Run", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        ownerDef.Methods.Add(method);

        IlGenerator.GenerateIl(caller, method);

        AssertStructReceiverIsAddress(method);
    }
}
