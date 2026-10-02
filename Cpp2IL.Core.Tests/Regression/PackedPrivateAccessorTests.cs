using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.NestedFieldPathLoadTests;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: AAPCS64 composite argument reads (castle-recovery#304).
// A 9-16 B value type arrives in an X-register pair, but the Unity surface
// puts its members behind private backing fields with public accessors -
// Vector2Int's m_X/m_Y under get_x/get_y, Nullable<T>.hasValue under
// get_HasValue, a KeyValuePair's value under get_Value. The packed-register
// pass may still project the leaf because the inlined-member rewrite spells
// the read through the accessor whose own body is `return <that field>`.
// An HFA in S/V registers reads its leaf through the lane the float
// instruction's own width or literal names.
public class PackedPrivateAccessorTests
{
    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
    }

    private static (InjectedTypeAnalysisContext type, FieldAnalysisContext mX,
        FieldAnalysisContext mY) Vector2Int(ApplicationAnalysisContext app)
    {
        var type = InjectStruct(app, "Vector2Int");
        var mX = new InjectedFieldAnalysisContext("m_X", app.SystemTypes.SystemInt32Type,
            R.FieldAttributes.Private, type, 0);
        var mY = new InjectedFieldAnalysisContext("m_Y", app.SystemTypes.SystemInt32Type,
            R.FieldAttributes.Private, type, 4);
        type.Fields.Add(mX);
        type.Fields.Add(mY);
        return (type, mX, mY);
    }

    private static void GiveGetterBody(MethodAnalysisContext getter, LocalVariable thisLocal,
        FieldAnalysisContext returned, int offset)
    {
        thisLocal.IsThis = true;
        var result = new LocalVariable("result", new Register(null, "result"), getter.ReturnType);
        getter.ParameterLocals = [thisLocal];
        getter.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.Move, result, new FieldReference(returned, thisLocal, offset)),
            new Instruction(1, OpCode.Return, result),
        ]);
    }

    [Test]
    public void PackedPrivateLeafReadsThroughReturnedFieldAccessor()
    {
        // lsr w8, x1, #32 on a packed Vector2Int: the m_Y lane is private, but
        // `get_y`'s body is `return m_Y` - so the read spells `get_y(&p)`.
        var app = Cpp2IlApi.CurrentAppContext!;
        var (vector2Int, _, mY) = Vector2Int(app);
        var getY = vector2Int.InjectMethodContext("get_y", app.SystemTypes.SystemInt32Type,
            R.MethodAttributes.Public);
        GiveGetterBody(getY, Local("this", vector2Int), mY, 4);

        var module = new ModuleDefinition("Packed.dll");
        Seed(module, app, vector2Int);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType);

        var packed = new LocalVariable("packed", new Register(null, "X1"), vector2Int);
        var high = Local("high");
        var shift = new Instruction(0, OpCode.ShiftRight, high, packed, new Immediate(32));
        var (caller, method) = ForeignCaller(app, module,
            [shift, new Instruction(1, OpCode.Return)], [packed, high]);
        caller.ParameterLocals = [packed];
        caller.Parameters.Add(new InjectedParameterAnalysisContext("packed", vector2Int,
            R.ParameterAttributes.None, 0, caller));
        var packedDefinition = vector2Int.GetExtraData<TypeDefinition>("AsmResolverType")!;
        var getYDefinition = new MethodDefinition("get_y",
            MethodAttributes.Public | MethodAttributes.HideBySig | MethodAttributes.SpecialName,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Int32));
        packedDefinition.Methods.Add(getYDefinition);
        getY.PutExtraData("AsmResolverMethod", getYDefinition);
        method.Signature = MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
            [packedDefinition.ToTypeSignature()]);
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "packed", default));

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(shift.OpCode, Is.EqualTo(OpCode.Move),
                "the private lane projects when an accessor proves it");
            Assert.That(shift.Operands[1], Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)shift.Operands[1]).Field, Is.SameAs(mY));
        });

        InlinedMemberRecovery.Run(caller);

        var call = caller.ControlFlowGraph!.Blocks.SelectMany(b => b.Instructions)
            .FirstOrDefault(i => i.OpCode == OpCode.Call);
        Assert.Multiple(() =>
        {
            Assert.That(call, Is.Not.Null, "the leaf read becomes the accessor call");
            Assert.That(call!.Operands[0], Is.SameAs((IOperand)getY));
            Assert.That(call.Operands.Skip(2).OfType<AddressOf>()
                    .Any(a => ReferenceEquals(a.Target, packed)), Is.True,
                "a value-type receiver binds as &p");
            Assert.That(call.Operands[1], Is.TypeOf<LocalVariable>());
            Assert.That(shift.Operands[1], Is.SameAs(call.Operands[1]),
                "the consumer reads the accessor's produced value");
        });

        // The accessor's &receiver is the parameter itself - ldarga, never an
        // initobj'd shadow local (which would read default(Vector2Int).m_Y).
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldarga
                    && i.Operand is AsmResolver.DotNet.Collections.Parameter { Name: "packed" }),
                Is.True, () => Dump(method));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    || i.OpCode == CilOpCodes.Callvirt), Is.True, () => Dump(method));
        });
    }

    [Test]
    public void PackedPrivateLeafWithoutAccessorStaysDiagnosed()
    {
        // The same lsr on a struct with no returned-field accessor keeps the
        // native read - a private leaf the caller can never spell is not
        // silently defaulted.
        var app = Cpp2IlApi.CurrentAppContext!;
        var (vector2Int, _, _) = Vector2Int(app);
        var module = new ModuleDefinition("Packed.dll");
        Seed(module, app, vector2Int);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType);

        var packed = new LocalVariable("packed", new Register(null, "X1"), vector2Int);
        var high = Local("high");
        var shift = new Instruction(0, OpCode.ShiftRight, high, packed, new Immediate(32));
        var (caller, _) = ForeignCaller(app, module,
            [shift, new Instruction(1, OpCode.Return)], [packed, high]);
        caller.ParameterLocals = [packed];

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.That(shift.OpCode, Is.EqualTo(OpCode.ShiftRight));
    }

    [Test]
    public void FloatCompareAgainstFloatLiteralReadsLowLane()
    {
        // `fcmp s0, #0.0` lifts as `CheckLess flagC, point, 0f`: the literal's
        // own family names the float lane the compare reads - point.x.
        var app = Cpp2IlApi.CurrentAppContext!;
        var single = app.SystemTypes.SystemSingleType;
        var point = InjectStruct(app, "Point2");
        InjectField("x", single, point, 0);
        InjectField("y", single, point, 4);
        var module = new ModuleDefinition("Lanes.dll");
        Seed(module, app, point);
        SeedCorLibTypes(app, module, single, app.SystemTypes.SystemBooleanType,
            app.SystemTypes.SystemVoidType);

        var local = new LocalVariable("point", new Register(null, "V0"), point);
        var flag = Local("flag", app.SystemTypes.SystemBooleanType);
        var check = new Instruction(0, OpCode.CheckLess, flag, local, new FloatLiteral(0f));
        var (caller, _) = ForeignCaller(app, module,
            [check, new Instruction(1, OpCode.Return)], [local, flag]);
        caller.ParameterLocals = [local];

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(check.Operands[1], Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)check.Operands[1]).Field.Name, Is.EqualTo("x"));
            Assert.That(check.Operands[2], Is.TypeOf<FloatLiteral>());
        });
    }

    [Test]
    public void FloatSourceConversionReadsLowLane()
    {
        // `fcvtzs x10, s0` is `(int)point.x`: the recorded source width and
        // floatness name the lane the conversion reads.
        var app = Cpp2IlApi.CurrentAppContext!;
        var single = app.SystemTypes.SystemSingleType;
        var point = InjectStruct(app, "Point2");
        InjectField("x", single, point, 0);
        InjectField("y", single, point, 4);
        var module = new ModuleDefinition("Lanes.dll");
        Seed(module, app, point);
        SeedCorLibTypes(app, module, single, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemVoidType);

        var local = new LocalVariable("point", new Register(null, "V0"), point);
        var dst = Local("dst", app.SystemTypes.SystemInt32Type);
        var convert = new Instruction(0, OpCode.Convert, dst, local)
        {
            ConversionFromFloat = true,
            ConversionSourceWidthBits = 32,
        };
        var (caller, _) = ForeignCaller(app, module,
            [convert, new Instruction(1, OpCode.Return)], [local, dst]);
        caller.ParameterLocals = [local];

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(convert.Operands[1], Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)convert.Operands[1]).Field.Name, Is.EqualTo("x"));
        });
    }

    [Test]
    public void CompositeAgainstScalarLiteralStaysDiagnosed()
    {
        // `fcmp s_x, #+inf` arrives as `CheckEqual flag, point, 0x7F800000` when
        // the immediate reaches the compare as raw bits. Boxing point and the
        // literal then ceq'ing the boxes compares distinct objects - always
        // false - so the test must stay diagnosed, not silently wrong.
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var point = InjectStruct(app, "Point2");
        InjectField("x", int32, point, 0);
        InjectField("y", int32, point, 4);
        var module = new ModuleDefinition("Compare.dll");
        Seed(module, app, point);
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemBooleanType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemStringType);

        var local = new LocalVariable("point", new Register(null, "V0"), point);
        var flag = Local("flag", app.SystemTypes.SystemBooleanType);
        var check = new Instruction(0, OpCode.CheckEqual, flag, local, new Immediate(2139095040));
        var (caller, method) = ForeignCaller(app, module,
            [check, new Instruction(1, OpCode.Return)], [local, flag]);
        caller.ParameterLocals = [local];

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string s && s.Contains("Unrecoverable")),
                Is.True, () => Dump(method));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Box), Is.False,
                "a boxed ceq between a composite and a scalar is always false\n" + string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void DeadConditionalEmitsNoEmptyDiamond()
    {
        // `ConditionalJump @b` whose taken block emits only `br join` while the
        // fallthrough bridge already reaches join: both edges land on the same
        // instruction. Emitting the check produces `if (c) {}` - a diamond
        // with two empty arms the CIL never needed - so it emits as nops.
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var module = new ModuleDefinition("Dead.dll");
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemBooleanType,
            app.SystemTypes.SystemVoidType);

        var x = Local("x", int32);
        var flag = Local("flag", app.SystemTypes.SystemBooleanType);
        var nop = new Instruction(2, OpCode.Nop);
        var join = new Instruction(4, OpCode.Return);
        var (caller, method) = ForeignCaller(app, module,
            [
                new Instruction(0, OpCode.CheckEqual, flag, x, new Immediate(0)),
                new Instruction(1, OpCode.ConditionalJump, nop, flag),
                nop,
                new Instruction(3, OpCode.Jump, join),
                join,
            ], [x, flag]);

        LocalVariables.ResolveTypesAndFields(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Brtrue
                    || i.OpCode == CilOpCodes.Brfalse), Is.False,
                "both edges reach the join; the check is dead\n" + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ret), Is.True, () => Dump(method));
        });
    }

    [Test]
    public void IntegerSourceConversionReadsPackedLeaf()
    {
        // `scvtf s0, w1` is `(float)pair.first`: the int lane of a packed pair
        // is the leaf at the conversion's recorded source width.
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var pair = InjectStruct(app, "Pair");
        InjectField("first", int32, pair, 0);
        InjectField("second", int32, pair, 4);
        var module = new ModuleDefinition("Lanes.dll");
        Seed(module, app, pair);
        SeedCorLibTypes(app, module, int32, app.SystemTypes.SystemSingleType,
            app.SystemTypes.SystemVoidType);

        var local = new LocalVariable("pair", new Register(null, "X1"), pair);
        var dst = Local("dst", app.SystemTypes.SystemSingleType);
        var convert = new Instruction(0, OpCode.Convert, dst, local)
        {
            ConversionSourceWidthBits = 32,
        };
        var (caller, _) = ForeignCaller(app, module,
            [convert, new Instruction(1, OpCode.Return)], [local, dst]);
        caller.ParameterLocals = [local];

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.Multiple(() =>
        {
            Assert.That(convert.Operands[1], Is.TypeOf<FieldReference>());
            Assert.That(((FieldReference)convert.Operands[1]).Field.Name, Is.EqualTo("first"));
        });
    }
}
