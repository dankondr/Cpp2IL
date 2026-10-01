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
        => DriveReturning(callerType, Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemVoidType,
            instructions, parameterTypes);

    private static InjectedMethodAnalysisContext DriveReturning(InjectedTypeAnalysisContext callerType,
        TypeAnalysisContext returnType, Instruction[] instructions,
        params TypeAnalysisContext[] parameterTypes)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        app.InstructionSet = new Cpp2IL.Core.InstructionSets.NewArmV8InstructionSet();
        var caller = callerType.InjectMethodContext("Run", returnType,
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
        => EmitReturning(caller, module, null, types);

    private static MethodDefinition EmitReturning(InjectedMethodAnalysisContext caller,
        ModuleDefinition module, TypeAnalysisContext? returnType, params TypeAnalysisContext[] types)
    {
        // Locals typed as a corlib primitive still go through ToTypeSignature,
        // which wants an AsmResolverType - seed the primitives a typed local or
        // field can reference the same way injected types are seeded.
        foreach (var type in caller.Locals.Select(l => l.Type).Where(t => t != null)
                     .Concat(types).Distinct())
            SeedTypeTree(module, type!);
        SeedTypes(module, types);
        var callerType = new TypeDefinition("Tests", "EmittedCaller",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(callerType);
        var method = new MethodDefinition("Run", MethodAttributes.Public,
            MethodSignature.CreateInstance(returnType == null
                ? module.CorLibTypeFactory.Void
                : SignatureFor(module, returnType)));
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

    private static void SeedTypeTree(ModuleDefinition module, TypeAnalysisContext type)
    {
        var pending = new Queue<TypeAnalysisContext>();
        pending.Enqueue(type);
        while (pending.Count > 0)
        {
            var next = pending.Dequeue();
            if (next.GetExtraData<TypeDefinition>("AsmResolverType") != null)
                continue;
            var definition = new TypeDefinition(next.Namespace, next.Name,
                TypeAttributes.Public | (next.IsValueType
                    ? TypeAttributes.Sealed | TypeAttributes.SequentialLayout
                    : TypeAttributes.Class),
                next.IsValueType
                    ? module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType")
                    : module.CorLibTypeFactory.Object.Type);
            module.TopLevelTypes.Add(definition);
            next.PutExtraData("AsmResolverType", definition);
            foreach (var field in next.Fields)
                pending.Enqueue(field.FieldType);
        }
    }

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

    [Test]
    public void Vector2ResultLanesLiftAsSinglesInFloatArithmetic()
    {
        var vector2 = InjectStruct("Vector2", FloatFields("x", "y"));
        var callerType = CallerTypeWithField("pos", vector2, 0x80);
        var getItem = callerType.InjectMethodContext("GetItem", vector2,
            R.MethodAttributes.Public | R.MethodAttributes.Static);

        // fadd s2, s0, s1 after `bl GetItem`: both result lanes feed scalar
        // float math, so each reads as the field at its offset - lane 0 as
        // result.x, lane 1 as result.y - and no lane register carries the
        // whole aggregate type.
        var call = new Instruction(0x14, OpCode.Call, getItem, Reg("V0"));
        call.ImplicitDefinitions.Add(Reg("V1"));
        var add = new Instruction(0x18, OpCode.Add, Reg("V2"), Reg("V0"), Reg("V1"))
        { NativeFloatWidthBits = 32 };
        var caller = Drive(callerType, [
            new Instruction(0x10, OpCode.Move, Reg("X19"), Reg("X0")),
            call, add, new Instruction(0x1c, OpCode.Return)]);

        var result = (LocalVariable)call.Destination!;
        Assert.Multiple(() =>
        {
            Assert.That(add.Operands[1], Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)add.Operands[1]).Field.Name, Is.EqualTo("x"));
            Assert.That(((FieldReference)add.Operands[1]).Local, Is.SameAs(result));
            Assert.That(add.Operands[2], Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)add.Operands[2]).Field.Name, Is.EqualTo("y"));
            Assert.That(((FieldReference)add.Operands[2]).Local, Is.SameAs(result));
            Assert.That(((LocalVariable)add.Operands[0]).Type?.FullName,
                Is.EqualTo("System.Single"));
            var lane = caller.Locals.First(local => local.Register.Name == "V1"
                && local.Register.Version == 1);
            Assert.That(lane.Type?.FullName, Is.EqualTo("System.Single"));
            Assert.That(caller.Locals.Count(local => local != result
                && local.Type == vector2), Is.EqualTo(0),
                "no local besides the result local carries the aggregate type");
        });

        var module = new ModuleDefinition("Lanes.dll");
        SeedCallee(getItem, module, vector2);
        var method = Emit(caller, module, callerType, vector2);
        Assert.That(method.CilMethodBody!.Instructions.All(i => i.OpCode != CilOpCodes.Ldstr),
            "the lane-typed add lifts with no diagnostic note");
    }

    [Test]
    public void Vector2ReturnRebuildsStructFromLanes()
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector2 = InjectStruct("Vector2", FloatFields("x", "y"));
        var callerType = CallerTypeWithField("pos", vector2, 0x80);

        // scvtf s0,w19; scvtf s1,w0; ret in a method returning Vector2: the
        // lifter reads V1 as the second lane of the result (the mirror of the
        // call's implicit lane definitions).
        var ret = new Instruction(0x18, OpCode.Return, Reg("V0"), Reg("V1"));
        var caller = DriveReturning(callerType, vector2, [
            new Instruction(0x10, OpCode.Move, Reg("V0"), new Immediate(1)),
            new Instruction(0x14, OpCode.Move, Reg("V1"), new Immediate(2)),
            ret]);

        var result = (LocalVariable)ret.Operands[0];
        var stores = caller.ControlFlowGraph!.Instructions
            .Where(i => i.OpCode == OpCode.Move && i.Operands[0] is FieldReference)
            .Select(i => (FieldReference)i.Operands[0]).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(result.Type, Is.SameAs(vector2));
            Assert.That(stores.Select(f => f.Field.Name), Is.EqualTo(new[] { "x", "y" }));
            Assert.That(stores.All(f => ReferenceEquals(f.Local, result)), Is.True);
        });

        var module = new ModuleDefinition("Lanes.dll");
        var method = EmitReturning(caller, module, vector2, callerType, vector2);
        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ret), Is.True);
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldstr), Is.EqualTo(0),
                "the rebuilt return carries no diagnostic note");
        });
    }

    private static InjectedTypeAnalysisContext FourInts()
    {
        var int32 = (TypeAnalysisContext)Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type;
        return InjectStruct("Quad", ("a", int32, 0), ("b", int32, 4), ("c", int32, 8), ("d", int32, 12));
    }

    [Test]
    public void ReturnOfACallResultWhoseFieldsStraddleTheLanesReturnsThatResult()
    {
        // bl GetQuad; ret: X0 and X1 each hold two ints, so no lane is one field, yet
        // the pair is the callee's whole result of the same type.
        var quad = FourInts();
        var callerType = CallerTypeWithField("pos", quad, 0x80);
        var getQuad = callerType.InjectMethodContext("GetQuad", quad,
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        var call = new Instruction(0x14, OpCode.Call, getQuad, Reg("X0"));
        call.ImplicitDefinitions.Add(Reg("X1"));
        var ret = new Instruction(0x18, OpCode.Return, Reg("X0"), Reg("X1"));
        var caller = DriveReturning(callerType, quad, [call, ret]);

        Assert.That(ret.Operands, Has.Count.EqualTo(1));
        Assert.That(ret.Operands[0], Is.SameAs(call.Destination));

        var module = new ModuleDefinition("Lanes.dll");
        SeedCallee(getQuad, module, quad);
        var il = EmitReturning(caller, module, quad, callerType, quad).CilMethodBody!.Instructions;
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldstr), Is.EqualTo(0));
    }

    [Test]
    public void ReturnWhoseHighLaneWasRewrittenAfterTheCallKeepsItsLanes()
    {
        var quad = FourInts();
        var callerType = CallerTypeWithField("pos", quad, 0x80);
        var getQuad = callerType.InjectMethodContext("GetQuad", quad,
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        var call = new Instruction(0x14, OpCode.Call, getQuad, Reg("X0"));
        call.ImplicitDefinitions.Add(Reg("X1"));
        var ret = new Instruction(0x1c, OpCode.Return, Reg("X0"), Reg("X1"));
        DriveReturning(callerType, quad, [call, new Instruction(0x18, OpCode.Move, Reg("X1"), new Immediate(5)), ret]);

        Assert.That(ret.Operands, Has.Count.EqualTo(2));
    }

    private static Instruction ReturnLaneZero(TypeAnalysisContext returnType)
    {
        // `float X(Transform t) => t.position.x` is `b Transform.get_position`: the caller's S0
        // is the callee's x.
        var vector3 = Vector3();
        var callerType = CallerTypeWithField("pos", vector3, 0x80);
        var getPosition = callerType.InjectMethodContext("GetPosition", vector3,
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        var call = new Instruction(0x14, OpCode.Call, getPosition, Reg("V0"));
        call.ImplicitDefinitions.AddRange([Reg("V1"), Reg("V2")]);
        var ret = new Instruction(0x18, OpCode.Return, Reg("V0"));
        DriveReturning(callerType, returnType, [call, ret]);
        return ret;
    }

    [Test]
    public void ScalarReturnOfAnAggregateCallResultReturnsItsFirstField()
    {
        var ret = ReturnLaneZero(Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemSingleType);

        Assert.That(ret.Operands[0], Is.InstanceOf<FieldReference>());
        Assert.That(((FieldReference)ret.Operands[0]).Field.Name, Is.EqualTo("x"));
    }

    [Test]
    public void ScalarReturnOfAnotherTypeKeepsTheCallResult()
    {
        var ret = ReturnLaneZero(Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type);

        Assert.That(ret.Operands[0], Is.InstanceOf<LocalVariable>());
    }

    private static (Instruction Whole, Instruction High, InjectedMethodAnalysisContext Caller, TypeAnalysisContext Quad,
        InjectedTypeAnalysisContext CallerType) StoreQuad(long highOffset)
    {
        // this.q = GetQuad(): `bl GetQuad; stp x0, x1, [x19, #0x80]`. No lane is one field of the
        // four ints, so the X1 store cannot be projected; it is the upper half of the whole store.
        var quad = FourInts();
        var callerType = CallerTypeWithField("q", quad, 0x80);
        var getQuad = callerType.InjectMethodContext("GetQuad", quad,
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        var call = new Instruction(0x14, OpCode.Call, getQuad, Reg("X0"));
        call.ImplicitDefinitions.Add(Reg("X1"));
        Instruction whole = new(0x18, OpCode.Move, new MemoryOperand(Reg("X19"), addend: 0x80, accessSize: 8), Reg("X0")) { NativeMemoryAccessSize = 8 };
        Instruction high = new(0x1c, OpCode.Move, new MemoryOperand(Reg("X19"), addend: highOffset, accessSize: 8), Reg("X1")) { NativeMemoryAccessSize = 8 };
        var caller = Drive(callerType, [
            new Instruction(0x10, OpCode.Move, Reg("X19"), Reg("X0")),
            call, whole, high, new Instruction(0x20, OpCode.Return)]);
        return (whole, high, caller, quad, callerType);
    }

    [Test]
    public void UpperLaneStoreOfAWholeStoredResultIsPartOfThatStore()
    {
        var (whole, high, caller, quad, callerType) = StoreQuad(0x88);

        Assert.That(high.OpCode, Is.EqualTo(OpCode.Nop));
        Assert.That(whole.Operands[1], Is.InstanceOf<LocalVariable>());
        Assert.That(((LocalVariable)whole.Operands[1]).Type, Is.SameAs(quad));

        var module = new ModuleDefinition("Lanes.dll");
        SeedCallee(caller.ControlFlowGraph!.Instructions.First(i => i.OpCode == OpCode.Call).Operands[0] as MethodAnalysisContext
                   ?? throw new System.InvalidOperationException(), module, quad);
        var il = Emit(caller, module, callerType, quad).CilMethodBody!.Instructions;
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldstr), Is.EqualTo(0));
    }

    [Test]
    public void UpperLaneStoredElsewhereStaysItsOwnStore()
    {
        var (_, high, _, _, _) = StoreQuad(0x90);

        Assert.That(high.OpCode, Is.EqualTo(OpCode.Move));
    }

    [Test]
    public void LateResolvedCallTakesEachArgumentFromItsAbiRegister()
    {
        // A tail or virtual call resolved after lifting carries every argument register:
        // M(Vector3 v, float f) has v in S0..S2 and f in S3, so f is V3, not the next V register,
        // and v is no integer register at all.
        var app = Cpp2IlApi.CurrentAppContext!;
        var vector3 = Vector3();
        var callerType = CallerTypeWithField("pos", vector3, 0x80);
        var callee = callerType.InjectMethodContext("Move", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, vector3, app.SystemTypes.SystemSingleType);
        var integers = new[] { "X0", "X1", "X2", "X3", "X4", "X5", "X6", "X7" };
        var floats = new[] { "V0", "V1", "V2", "V3", "V4", "V5", "V6", "V7" };
        var call = new Instruction(0x10, OpCode.CallVoid,
            [new Immediate(0x1234), .. integers.Concat(floats).Select(name => (IOperand)Reg(name))]);

        new Cpp2IL.Core.Utils.Arm64CallingConventionResolver().RemapRawArguments(call, callee);

        Assert.That(call.Operands.Skip(1).Select(o => ((Register)o).Name), Is.EqualTo(new[] { "V0", "V3", "X0" }));
    }

    [Test]
    public void UpperLaneStoredThroughARegisterCopyIsPartOfTheWholeStore()
    {
        // `bl GetQuad; mov x8, x1; stp x0, x8, [x19, #0x80]`
        var quad = FourInts();
        var callerType = CallerTypeWithField("q", quad, 0x80);
        var getQuad = callerType.InjectMethodContext("GetQuad", quad,
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        var call = new Instruction(0x14, OpCode.Call, getQuad, Reg("X0"));
        call.ImplicitDefinitions.Add(Reg("X1"));
        Instruction whole = new(0x1c, OpCode.Move, new MemoryOperand(Reg("X19"), addend: 0x80, accessSize: 8), Reg("X0")) { NativeMemoryAccessSize = 8 };
        Instruction high = new(0x1c, OpCode.Move, new MemoryOperand(Reg("X19"), addend: 0x88, accessSize: 8), Reg("X8")) { NativeMemoryAccessSize = 8 };
        Drive(callerType, [
            new Instruction(0x10, OpCode.Move, Reg("X19"), Reg("X0")),
            call, new Instruction(0x18, OpCode.Move, Reg("X8"), Reg("X1")), whole, high,
            new Instruction(0x20, OpCode.Return)]);

        Assert.That(high.OpCode, Is.EqualTo(OpCode.Nop));
    }

    private static InjectedTypeAnalysisContext TwoInts()
    {
        var int32 = (TypeAnalysisContext)Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type;
        return InjectStruct("Pair", ("a", int32, 0), ("b", int32, 4));
    }

    // `orr xD, xLo, xHi, lsl #n` as the lifter emits it: the shifted operand in a temp.
    private static Instruction[] PackPair(string destination, string low, string high, int shift) =>
    [
        new(0x10, OpCode.ShiftLeft, Reg("TEMP_LOGICAL_SHIFT"), Reg(high), new Immediate(shift)),
        new(0x10, OpCode.Or, Reg(destination), Reg(low), Reg("TEMP_LOGICAL_SHIFT")),
    ];

    [Test]
    public void ReturnPackedFromHalvesRebuildsTheStruct()
    {
        // Quad Make(int a, int b, int c, int d) => new Quad(a, b * 2, c, d):
        // `orr x8, x3(c), x4(d), lsl #32; orr x0, x1(a), x2(b), lsl #33; mov x1, x8; ret`
        // (an instance method: the ints sit in X1..X4).
        var app = Cpp2IlApi.CurrentAppContext!;
        var quad = FourInts();
        var callerType = CallerTypeWithField("q", quad, 0x80);
        var ret = new Instruction(0x20, OpCode.Return, Reg("X0"), Reg("X1"));
        var int32 = app.SystemTypes.SystemInt32Type;
        var caller = DriveReturning(callerType, quad, [
            .. PackPair("X8", "X3", "X4", 32), .. PackPair("X0", "X1", "X2", 33),
            new Instruction(0x1c, OpCode.Move, Reg("X1"), Reg("X8")), ret],
            int32, int32, int32, int32);

        var result = (LocalVariable)ret.Operands.Single();
        var stores = caller.ControlFlowGraph!.Instructions
            .Where(i => i.OpCode == OpCode.Move && i.Operands[0] is FieldReference { Local: var local } && local == result)
            .ToDictionary(i => ((FieldReference)i.Operands[0]).Field.Name, i => i.Operands[1]);
        var parameters = caller.ParameterLocals.Where(p => !p.IsThis).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(result.Type, Is.SameAs(quad));
            Assert.That(stores["a"], Is.SameAs(parameters[0]));
            Assert.That(stores["c"], Is.SameAs(parameters[2]));
            Assert.That(stores["d"], Is.SameAs(parameters[3]));
            // `b << 33` puts `b << 1` in the high half.
            var scaled = caller.ControlFlowGraph.Instructions.Single(i => ReferenceEquals(i.Destination, stores["b"]));
            Assert.That(scaled.OpCode, Is.EqualTo(OpCode.ShiftLeft));
            Assert.That(scaled.Operands[1], Is.SameAs(parameters[1]));
            Assert.That(scaled.Operands[2], Is.EqualTo(new Immediate(1)));
        });

        var module = new ModuleDefinition("Lanes.dll");
        var il = EmitReturning(caller, module, quad, callerType, quad).CilMethodBody!.Instructions;
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldstr), Is.EqualTo(0));
    }

    [Test]
    public void FieldStoreOfAPackedPairStoresTheStruct()
    {
        // this.p = new Pair(a, b): `orr x8, x1, x2, lsl #32; str x8, [x0, #0x80]`.
        var app = Cpp2IlApi.CurrentAppContext!;
        var pair = TwoInts();
        var callerType = CallerTypeWithField("p", pair, 0x80);
        Instruction store = new(0x18, OpCode.Move, new MemoryOperand(Reg("X0"), addend: 0x80, accessSize: 8), Reg("X8"))
            { NativeMemoryAccessSize = 8 };
        var caller = Drive(callerType, [.. PackPair("X8", "X1", "X2", 32), store, new Instruction(0x1c, OpCode.Return)],
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemInt32Type);

        Assert.That(store.Operands[1], Is.InstanceOf<LocalVariable>());
        var value = (LocalVariable)store.Operands[1];
        var halves = caller.ControlFlowGraph!.Instructions
            .Where(i => i.OpCode == OpCode.Move && i.Operands[0] is FieldReference { Local: var local } && local == value)
            .Select(i => (((FieldReference)i.Operands[0]).Field.Name, i.Operands[1])).ToList();
        var parameters = caller.ParameterLocals.Where(p => !p.IsThis).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(value.Type, Is.SameAs(pair));
            Assert.That(halves, Is.EqualTo(new[] { ("a", (IOperand)parameters[0]), ("b", parameters[1]) }));
        });

        var module = new ModuleDefinition("Lanes.dll");
        var il = Emit(caller, module, callerType, pair).CilMethodBody!.Instructions;
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldstr), Is.EqualTo(0));
    }

    [Test]
    public void PairWhoseLowHalfIsSixtyFourBitsWideStaysDiagnosed()
    {
        // The low operand is an eight-byte load: its upper half would land in `b`.
        var app = Cpp2IlApi.CurrentAppContext!;
        var pair = TwoInts();
        var callerType = CallerTypeWithField("p", pair, 0x80);
        Instruction store = new(0x18, OpCode.Move, new MemoryOperand(Reg("X0"), addend: 0x80, accessSize: 8), Reg("X8"))
            { NativeMemoryAccessSize = 8 };
        Drive(callerType, [
            new Instruction(0x0c, OpCode.Move, Reg("X3"), new MemoryOperand(Reg("X0"), addend: 0x10, accessSize: 8))
                { NativeMemoryAccessSize = 8 },
            .. PackPair("X8", "X3", "X2", 32), store, new Instruction(0x1c, OpCode.Return)],
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemInt32Type);

        Assert.That(((LocalVariable)store.Operands[1]).Type, Is.Not.SameAs(pair));
    }

    [Test]
    public void LaneOfTwoIntsReadsEachHalfAsItsField()
    {
        // int Sum(Quad v) => v.a + v.b + v.c + v.d reads X2 (v's upper lane) as `w2` and,
        // through a whole-register copy, as `lsr x9, x11, #32`.
        var quad = FourInts();
        var callerType = CallerTypeWithField("q", quad, 0x80);
        Instruction copy = new(0x0c, OpCode.Move, Reg("X11"), Reg("X2"));
        Instruction high = new(0x10, OpCode.ShiftRight, Reg("X9"), Reg("X11"), new Immediate(32));
        Instruction low = new(0x14, OpCode.Add, Reg("X10"), Reg("X2"), Reg("X9")) { NativeIntegerWidthBits = 32 };
        var caller = DriveReturning(callerType, Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type,
            [copy, high, low, new Instruction(0x18, OpCode.Move, Reg("X0"), Reg("X10")), new Instruction(0x1c, OpCode.Return, Reg("X0"))],
            quad);

        var v = caller.ParameterLocals.First(p => !p.IsThis);
        Assert.Multiple(() =>
        {
            // The copy keeps both halves; only its 32-bit reads take one.
            Assert.That(copy.Operands[1], Is.InstanceOf<LocalVariable>());
            Assert.That(high.OpCode, Is.EqualTo(OpCode.Move));
            Assert.That(LaneSource(high).Field.Name, Is.EqualTo("d"));
            Assert.That(LaneSource(high).Local, Is.SameAs(v));
            Assert.That(LaneSource(low).Field.Name, Is.EqualTo("c"));
            Assert.That(LaneSource(low).Local, Is.SameAs(v));
        });
    }
}
