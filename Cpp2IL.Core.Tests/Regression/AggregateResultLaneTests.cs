using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: multi-register call results (castle-recovery#205). An HFA
// returns one lane per V register and a 9-16 byte composite returns in an X
// pair - the lifts carry the extra lanes on the call's ImplicitDefinitions, and
// AggregateResultLanes projects a lane read onto the field its bytes hold. The
// regression: stores of V1..Vn after `GetPosition()` became `Move this.pos.y,
// v @ V1` with V1 undefined instead of `this.pos.y = res.y`.
public class AggregateResultLaneTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static Register Reg(string name) => new(null, name);

    private static InjectedTypeAnalysisContext InjectStruct(string name,
        params (string Name, TypeAnalysisContext Type, int Offset)[] fields)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var type = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", name,
            app.AssembliesByName["mscorlib"].GetTypeByFullName("System.ValueType")!,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        foreach (var (fieldName, fieldType, offset) in fields)
            type.Fields.Add(new InjectedFieldAnalysisContext(fieldName, fieldType,
                R.FieldAttributes.Public, type, offset));
        return type;
    }

    private static InjectedTypeAnalysisContext Vector3()
        => InjectStruct("Vector3", ThreeFloats());

    private static (string Name, TypeAnalysisContext Type, int Offset)[] ThreeFloats()
        => FloatFields("x", "y", "z");

    private static (string Name, TypeAnalysisContext Type, int Offset)[] FloatFields(
        params string[] names)
        => names.Select((n, i) => (n, (TypeAnalysisContext)Cpp2IlApi.CurrentAppContext!
            .SystemTypes.SystemSingleType, i * 4)).ToArray();

    private static InjectedTypeAnalysisContext CallerTypeWithField(string fieldName,
        TypeAnalysisContext fieldType, int fieldOffset)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var callerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests",
            "LaneCaller", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        callerType.Fields.Add(new InjectedFieldAnalysisContext(fieldName, fieldType,
            R.FieldAttributes.Public, callerType, fieldOffset));
        return callerType;
    }

    // The production order: CFG -> dominators -> SSA -> CreateAll -> fixpoint.
    private static InjectedMethodAnalysisContext Drive(InjectedTypeAnalysisContext callerType,
        Instruction[] instructions, params TypeAnalysisContext[] parameterTypes)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        app.InstructionSet = new Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet();
        var caller = callerType.InjectMethodContext("Run", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public, parameterTypes);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions.ToList());
        caller.ParameterOperands = app.InstructionSet.CallingConventionResolver!
            .ResolveForManaged(caller).ToList();
        caller.AnalysisWarnings = [];
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph);
        SsaForm.Build(caller);
        LocalVariables.CreateAll(caller);
        LocalVariables.ResolveTypesAndFields(caller);
        return caller;
    }

    private static MethodDefinition Emit(InjectedMethodAnalysisContext caller, ModuleDefinition module,
        params TypeAnalysisContext[] types)
    {
        SeedTypes(module, types);
        var callerType = new TypeDefinition("Tests", "EmittedCaller",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(callerType);
        var method = new MethodDefinition("Run", MethodAttributes.Public,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        callerType.Methods.Add(method);
        IlGenerator.GenerateIl(caller, method);
        return method;
    }

    // Injected members stand in for corlib members: primitives map to the module's
    // corlib factory signatures, anything else gets a real TypeDefinition.
    private static TypeSignature SignatureFor(ModuleDefinition module, TypeAnalysisContext type)
        => type.FullName switch
        {
            "System.Single" => module.CorLibTypeFactory.Single,
            "System.Double" => module.CorLibTypeFactory.Double,
            "System.Int32" => module.CorLibTypeFactory.Int32,
            "System.Int64" => module.CorLibTypeFactory.Int64,
            "System.Object" => module.CorLibTypeFactory.Object,
            "System.Void" => module.CorLibTypeFactory.Void,
            _ => type.ToTypeSignature(),
        };

    private static void SeedTypes(ModuleDefinition module, IEnumerable<TypeAnalysisContext> types)
    {
        foreach (var type in types.Where(t => t != null))
        {
            if (type.GetExtraData<TypeDefinition>("AsmResolverType") != null)
                continue;
            var definition = new TypeDefinition(type.Namespace, type.Name,
                TypeAttributes.Public | (type.IsValueType
                    ? TypeAttributes.Sealed | TypeAttributes.SequentialLayout
                    : TypeAttributes.Class),
                type.IsValueType
                    ? module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType")
                    : module.CorLibTypeFactory.Object.Type);
            module.TopLevelTypes.Add(definition);
            type.PutExtraData("AsmResolverType", definition);
        }
        foreach (var type in types.Where(t => t != null))
        {
            var owner = type.GetExtraData<TypeDefinition>("AsmResolverType")!;
            foreach (var field in type.Fields)
            {
                if (field.GetExtraData<FieldDefinition>("AsmResolverField") != null)
                    continue;
                var definition = new FieldDefinition(field.Name,
                    AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public,
                    new FieldSignature(SignatureFor(module, field.FieldType)));
                owner.Fields.Add(definition);
                field.PutExtraData("AsmResolverField", definition);
            }
        }
    }

    private static void SeedCallee(MethodAnalysisContext callee, ModuleDefinition module,
        TypeAnalysisContext returnType)
    {
        SeedTypes(module, [callee.DeclaringType!, returnType]);
        if (callee.GetExtraData<MethodDefinition>("AsmResolverMethod") == null)
            callee.PutExtraData("AsmResolverMethod", new MethodDefinition(callee.Name,
                MethodAttributes.Public | MethodAttributes.Static,
                MethodSignature.CreateStatic(SignatureFor(module, returnType))));
    }

    private static FieldReference LaneSource(Instruction instruction)
        => (FieldReference)instruction.Operands[1];

    [Test]
    public void Vector3ReturnStoresIntoConsecutiveFields()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector3 = Vector3();
        var callerType = CallerTypeWithField("pos", vector3, 0x80);
        var getPosition = callerType.InjectMethodContext("GetPosition", vector3,
            R.MethodAttributes.Public | R.MethodAttributes.Static);

        // ldr x19, this -> bl GetPosition -> stp s0,s1,[x19+0x80]; str s2,[x19+0x88]
        var call = new Instruction(0x14, OpCode.Call, getPosition, Reg("V0"));
        call.ImplicitDefinitions.AddRange([Reg("V1"), Reg("V2")]);
        Instruction storeX = new(0x18, OpCode.Move, new MemoryOperand(Reg("X19"), addend: 0x80, accessSize: 4), Reg("V0")) { NativeMemoryAccessSize = 4 };
        Instruction storeY = new(0x1c, OpCode.Move, new MemoryOperand(Reg("X19"), addend: 0x84, accessSize: 4), Reg("V1")) { NativeMemoryAccessSize = 4 };
        Instruction storeZ = new(0x20, OpCode.Move, new MemoryOperand(Reg("X19"), addend: 0x88, accessSize: 4), Reg("V2")) { NativeMemoryAccessSize = 4 };
        var caller = Drive(callerType, [
            new Instruction(0x10, OpCode.Move, Reg("X19"), Reg("X0")),
            call, storeX, storeY, storeZ, new Instruction(0x24, OpCode.Return)]);

        var result = (LocalVariable)call.Destination!;
        Assert.Multiple(() =>
        {
            Assert.That(LaneSource(storeX).Field.Name, Is.EqualTo("x"));
            Assert.That(LaneSource(storeY).Field.Name, Is.EqualTo("y"));
            Assert.That(LaneSource(storeZ).Field.Name, Is.EqualTo("z"));
            Assert.That(LaneSource(storeY).Local, Is.SameAs(result));
            Assert.That(LaneSource(storeZ).Local, Is.SameAs(result));
        });

        var module = new ModuleDefinition("Lanes.dll");
        SeedCallee(getPosition, module, vector3);
        var method = Emit(caller, module, callerType, vector3);
        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stfld), Is.True);
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldstr
                && (i.Operand as string)?.Contains("Undefined local") == true), Is.EqualTo(0));
        });
    }

    [Test]
    public void QuaternionReturnProjectsAllFourLanes()
    {
        var quaternion = InjectStruct("Quaternion", FloatFields("x", "y", "z", "w"));
        var callerType = CallerTypeWithField("rotation", quaternion, 0x80);
        var getRotation = callerType.InjectMethodContext("GetRotation", quaternion,
            R.MethodAttributes.Public | R.MethodAttributes.Static);

        var call = new Instruction(0x14, OpCode.Call, getRotation, Reg("V0"));
        call.ImplicitDefinitions.AddRange([Reg("V1"), Reg("V2"), Reg("V3")]);
        Instruction storeY = new(0x18, OpCode.Move, new MemoryOperand(Reg("X19"), addend: 0x84, accessSize: 4), Reg("V1")) { NativeMemoryAccessSize = 4 };
        Instruction storeZ = new(0x1c, OpCode.Move, new MemoryOperand(Reg("X19"), addend: 0x88, accessSize: 4), Reg("V2")) { NativeMemoryAccessSize = 4 };
        Instruction storeW = new(0x20, OpCode.Move, new MemoryOperand(Reg("X19"), addend: 0x8c, accessSize: 4), Reg("V3")) { NativeMemoryAccessSize = 4 };
        var caller = Drive(callerType, [
            new Instruction(0x10, OpCode.Move, Reg("X19"), Reg("X0")),
            call, storeY, storeZ, storeW, new Instruction(0x24, OpCode.Return)]);

        var result = (LocalVariable)call.Destination!;
        Assert.Multiple(() =>
        {
            Assert.That(LaneSource(storeY).Field.Name, Is.EqualTo("y"));
            Assert.That(LaneSource(storeZ).Field.Name, Is.EqualTo("z"));
            Assert.That(LaneSource(storeW).Field.Name, Is.EqualTo("w"));
            Assert.That(LaneSource(storeW).Local, Is.SameAs(result));
        });
    }

    [Test]
    public void ScalarFloatReturnLeavesLaneOneDiagnosed()
    {
        var single = Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemSingleType;
        var callerType = CallerTypeWithField("radius", single, 0x80);
        var getScalar = callerType.InjectMethodContext("GetScalar", single,
            R.MethodAttributes.Public | R.MethodAttributes.Static);

        // str s1, [x19+0x84] after a scalar float call: V1 is not the callee's lane
        // and must keep its diagnostic - no projection is guessed.
        var call = new Instruction(0x14, OpCode.Call, getScalar, Reg("V0"));
        Instruction store = new(0x18, OpCode.Move, new MemoryOperand(Reg("X19"), addend: 0x84, accessSize: 4), Reg("V1")) { NativeMemoryAccessSize = 4 };
        var caller = Drive(callerType, [
            new Instruction(0x10, OpCode.Move, Reg("X19"), Reg("X0")),
            call, store, new Instruction(0x1c, OpCode.Return)]);

        Assert.That(store.Operands[1], Is.TypeOf<LocalVariable>());

        var module = new ModuleDefinition("Lanes.dll");
        SeedCallee(getScalar, module, single);
        var method = Emit(caller, module, callerType, single);
        Assert.That(method.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr
            && (i.Operand as string)?.Contains("Undefined local") == true), Is.True,
            "the unproven lane keeps its undefined-local diagnostic");
    }

    [Test]
    public void SixteenByteStructReturnDefinesBothXRegisters()
    {
        var pair = InjectStruct("LongPair",
            ("lo", (TypeAnalysisContext)Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt64Type, 0),
            ("hi", (TypeAnalysisContext)Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt64Type, 8));
        var callerType = CallerTypeWithField("span", pair, 0x80);
        var getPair = callerType.InjectMethodContext("GetPair", pair,
            R.MethodAttributes.Public | R.MethodAttributes.Static);

        // ldp x0,x1 -> stp x0,x1,[x19+0x80]: X1 is the pair's high half.
        var call = new Instruction(0x14, OpCode.Call, getPair, Reg("X0"));
        call.ImplicitDefinitions.Add(Reg("X1"));
        Instruction storeLo = new(0x18, OpCode.Move, new MemoryOperand(Reg("X19"), addend: 0x80, accessSize: 8), Reg("X0")) { NativeMemoryAccessSize = 8 };
        Instruction storeHi = new(0x1c, OpCode.Move, new MemoryOperand(Reg("X19"), addend: 0x88, accessSize: 8), Reg("X1")) { NativeMemoryAccessSize = 8 };
        var caller = Drive(callerType, [
            new Instruction(0x10, OpCode.Move, Reg("X19"), Reg("X0")),
            call, storeLo, storeHi, new Instruction(0x20, OpCode.Return)]);

        var result = (LocalVariable)call.Destination!;
        Assert.Multiple(() =>
        {
            Assert.That(LaneSource(storeHi).Field.Name, Is.EqualTo("hi"));
            Assert.That(LaneSource(storeHi).Local, Is.SameAs(result));
            Assert.That(LaneSource(storeHi).Offset, Is.EqualTo(8));
        });
    }

    [Test]
    public void AggregateParameterLanesReadAsFields()
    {
        var vector3 = Vector3();
        var callerType = CallerTypeWithField("pos", vector3, 0x80);

        // str s1,[x19+0x84] with v in V0..V2 at entry: V1 is v.y's home lane.
        Instruction store = new(0x14, OpCode.Move, new MemoryOperand(Reg("X19"), addend: 0x84, accessSize: 4), Reg("V1")) { NativeMemoryAccessSize = 4 };
        var caller = Drive(callerType, [
            new Instruction(0x10, OpCode.Move, Reg("X19"), Reg("X0")),
            store, new Instruction(0x18, OpCode.Return)],
            vector3);

        var lane = LaneSource(store);
        Assert.Multiple(() =>
        {
            Assert.That(lane.Field.Name, Is.EqualTo("y"));
            Assert.That(lane.Local, Is.SameAs(caller.ParameterLocals.First(p => !p.IsThis)));
        });
    }
}
