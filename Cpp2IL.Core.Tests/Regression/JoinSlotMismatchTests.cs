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
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: typed local -> mismatched slot (castle-recovery#143). A Move
// between two differently-typed value types is a register move the lifter could
// not prove converts - it keeps the "no legal conversion" diagnostic and the
// synthetic default even when the pair happens to carry a user-defined
// conversion operator, because emitting `call op_Implicit`/`op_Explicit` there
// would fabricate a computation the binary never ran. The one honest recovery
// covered here is the SelectedFieldReference join, where the emitted type now
// mirrors the whole-container load LoadOperand actually performs.
public class JoinSlotMismatchTests
{
    // The same register defined on both arms of a diamond but never read after
    // the join used to get a phi at the join anyway - SsaForm.Remove then
    // materialized a dead edge copy whose mismatched types produced a
    // "no legal conversion" diagnostic. Pruned insertion skips the dead join
    // entirely: no copy, no diagnostic, nothing substituted.
    [Test]
    public void DeadJoinOfReusedRegisterInsertsNoPhi()
    {
        var instructions = new List<Instruction>();
        void Add(int index, OpCode opCode, params object[] operands)
            => instructions.Add(new Instruction(index, opCode, Ops(operands)));
        Add(0, OpCode.Move, new Register(null, "x"), 0);
        Add(1, OpCode.ConditionalJump, 4, new Register(null, "cond"));
        Add(2, OpCode.Move, new Register(null, "x"), 1);
        Add(3, OpCode.Jump, 5);
        Add(4, OpCode.Move, new Register(null, "x"), 2);
        Add(5, OpCode.Return);
        foreach (var instruction in instructions)
            if (instruction.OpCode is OpCode.Jump or OpCode.ConditionalJump)
                instruction.SetOperand(0, instructions[(int)((Immediate)instruction.Operands[0]).Value]);
        var graph = new ISILControlFlowGraph(instructions.ToList());

        SsaForm.Build(graph, new DominatorInfo(graph));

        Assert.That(graph.Instructions.Count(instruction => instruction.OpCode == OpCode.Phi),
            Is.EqualTo(0));
    }
    private static InjectedTypeAnalysisContext InjectStruct(ApplicationAnalysisContext app, string name) =>
        new(app.AssembliesByName["UnityEngine.CoreModule"], "Tests", name,
            app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);

    private static TypeSignature Sig(TypeAnalysisContext type, ModuleDefinition module) =>
        type.GetExtraData<TypeDefinition>("AsmResolverType")?.ToTypeSignature()
        ?? type.FullName switch
        {
            "System.Int32" => module.CorLibTypeFactory.Int32,
            _ => throw new System.InvalidOperationException(type.FullName),
        };

    private static MethodAnalysisContext InjectOperator(InjectedTypeAnalysisContext owner,
        TypeAnalysisContext from, TypeAnalysisContext to, ModuleDefinition module,
        string name = "op_Implicit")
    {
        var ownerDef = owner.GetExtraData<TypeDefinition>("AsmResolverType")!;
        var opDef = new MethodDefinition(name,
            MethodAttributes.Public | MethodAttributes.Static | MethodAttributes.SpecialName
                | MethodAttributes.HideBySig,
            MethodSignature.CreateStatic(Sig(to, module), [Sig(from, module)]));
        ownerDef.Methods.Add(opDef);
        var op = owner.InjectMethodContext(name, to,
            R.MethodAttributes.Public | R.MethodAttributes.Static | R.MethodAttributes.SpecialName
                | R.MethodAttributes.HideBySig,
            from);
        op.PutExtraData("AsmResolverMethod", opDef);
        return op;
    }

    private static System.Collections.Generic.IEnumerable<CilInstruction> GenerateMove(
        ApplicationAnalysisContext app, TypeAnalysisContext sourceType,
        TypeAnalysisContext destinationType, ModuleDefinition module)
    {
        var source = new LocalVariable("source", new Register(null, "source")) { Type = sourceType };
        var destination = new LocalVariable("destination", new Register(null, "destination"))
            { Type = destinationType };
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, destination, source),
            new(1, OpCode.Return)], [source, destination]);
        IlGenerator.GenerateIl(caller, method);
        return method.CilMethodBody!.Instructions;
    }

    // Pins the no-fabrication rule: a mismatched value-type move keeps the named
    // diagnostic and the default even when the types carry a matching
    // op_Implicit - the binary executed a register move, not the operator's
    // conversion body.
    [Test]
    public void MoveIntoOperatorConvertedSlotKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var vec2 = InjectStruct(app, "Vec2");
        var vec3 = InjectStruct(app, "Vec3");
        var module = new ModuleDefinition("Conversion.dll");
        SeedCorLibTypes(app, module, vec2, vec3);
        InjectOperator(vec2, vec2, vec3, module);

        var il = GenerateMove(app, vec2, vec3, module);

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("synthetic default")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString().Contains("op_Implicit") == true), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void MoveIntoExplicitOperatorConvertedSlotKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var vec2 = InjectStruct(app, "Vec2");
        var vec3 = InjectStruct(app, "Vec3");
        var module = new ModuleDefinition("Conversion.dll");
        SeedCorLibTypes(app, module, vec2, vec3);
        InjectOperator(vec3, vec3, vec2, module, "op_Explicit");

        var il = GenerateMove(app, vec3, vec2, module);

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("synthetic default")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString().Contains("op_Explicit") == true), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    // Same rule for a literal: a nonzero immediate in a value-type slot keeps
    // the named diagnostic and the default - it is not op_Implicit(int) of the
    // literal, whatever operators the slot's type declares.
    [Test]
    public void MoveImmediateIntoOperatorConvertedSlotKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var vec3 = InjectStruct(app, "Vec3");
        var module = new ModuleDefinition("Conversion.dll");
        SeedCorLibTypes(app, module, vec3);
        InjectOperator(vec3, app.SystemTypes.SystemInt32Type, vec3, module);

        var destination = new LocalVariable("destination", new Register(null, "destination"))
            { Type = vec3 };
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, destination, new Immediate(7L)),
            new(1, OpCode.Return)], [destination]);
        IlGenerator.GenerateIl(caller, method);
        var il = method.CilMethodBody!.Instructions;

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("synthetic default")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString().Contains("op_Implicit") == true), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    private static InjectedFieldAnalysisContext AddField(InjectedTypeAnalysisContext owner, string name,
        TypeAnalysisContext type, int offset, ModuleDefinition module)
    {
        var field = new InjectedFieldAnalysisContext(name, type, R.FieldAttributes.Public, owner, offset);
        owner.Fields.Add(field);
        var definition = new FieldDefinition(name, FieldAttributes.Public,
            new FieldSignature(Sig(type, module)));
        field.DeclaringType!.GetExtraData<TypeDefinition>("AsmResolverType")!.Fields.Add(definition);
        field.PutExtraData("AsmResolverField", definition);
        return field;
    }

    // A `select(...)` of two offset-0 leaf fields whose containers carry the
    // slot's own value type: LoadOperand swaps each leaf load for the whole
    // container, so the merged stack value already has the slot's type - a
    // conversion call computed from the leaf type feeds the operator a stack
    // it does not take (ILVerify StackUnexpected).
    [Test]
    public void SelectedLeafFieldsIntoContainerSlotEmitWholeLoads()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var mask = InjectStruct(app, "Mask");
        var holder = InjectStruct(app, "Holder");
        var module = new ModuleDefinition("Conversion.dll");
        SeedCorLibTypes(app, module, mask, holder, app.SystemTypes.SystemInt64Type);
        var leaf = AddField(mask, "m_Mask", app.SystemTypes.SystemInt32Type, 0, module);
        var fieldA = AddField(holder, "a", mask, 0, module);
        var fieldB = AddField(holder, "b", mask, 4, module);
        InjectOperator(mask, app.SystemTypes.SystemInt32Type, mask, module);

        var receiver = new LocalVariable("receiver", new Register(null, "receiver"))
            { Type = holder };
        var selector = new LocalVariable("selector", new Register(null, "selector"))
            { Type = app.SystemTypes.SystemInt64Type };
        var destination = new LocalVariable("destination", new Register(null, "destination"))
            { Type = mask };
        var select = new SelectedFieldReference(selector, [
            (0, new FieldReference(leaf, receiver, 0, [fieldA])),
            (1, new FieldReference(leaf, receiver, 0, [fieldB]))]);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, destination, select),
            new(1, OpCode.Return)], [receiver, selector, destination]);
        IlGenerator.GenerateIl(caller, method);
        var il = method.CilMethodBody!.Instructions;

        Assert.Multiple(() =>
        {
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldfld
                    && i.Operand?.ToString() is { } member
                    && (member.EndsWith("::a") || member.EndsWith("::b"))), Is.EqualTo(2),
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString().Contains("op_") == true), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("synthetic default")), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    // A `_current` read on an enumerator local is inlined as `call get_Current`
    // instantiated on the receiver's emitted instantiation. When that
    // instantiation is concrete but the field reference was bound on the erased
    // instance (reused register / erased declaration), the pushed type is the
    // concrete `Current` - here Int32 - while the erased field type says
    // object. Reporting the erased type makes the object-typed store a no-op
    // and leaves a bare `int32` where `object` belongs (ILVerify
    // StackUnexpected); reporting the getter's real return lets the coercion
    // emit `box` instead.
    [Test]
    public void InlinedEnumeratorCurrentIntoErasedSlotEmitsBox()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var list = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Collections.Generic.List`1")!;
        var enumeratorDefinition = list.NestedTypes.Single(type => type.Name == "Enumerator");
        var erased = new GenericInstanceTypeAnalysisContext(enumeratorDefinition,
            [app.SystemTypes.SystemObjectType]);
        var concrete = new GenericInstanceTypeAnalysisContext(enumeratorDefinition,
            [app.SystemTypes.SystemInt32Type]);
        var currentOnErased = new ConcreteGenericFieldAnalysisContext(
            enumeratorDefinition.Fields.Single(field => field.Name == "_current"), erased);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver")) { Type = concrete };
        var destination = new LocalVariable("destination", new Register(null, "destination"))
            { Type = app.SystemTypes.SystemObjectType };

        var module = new ModuleDefinition("EnumeratorCurrent.dll");
        var emittedEnumerator = new TypeDefinition("System.Collections.Generic", "Enumerator`1",
            TypeAttributes.Public | TypeAttributes.SequentialLayout | TypeAttributes.Sealed,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        emittedEnumerator.GenericParameters.Add(new GenericParameter("T"));
        module.TopLevelTypes.Add(emittedEnumerator);
        enumeratorDefinition.PutExtraData("AsmResolverType", emittedEnumerator);
        SeedCorLibTypes(app, module, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, destination, new FieldReference(currentOnErased, receiver, 0)),
            new(1, OpCode.Return)], [receiver, destination]);
        IlGenerator.GenerateIl(caller, method);
        var il = method.CilMethodBody!.Instructions;

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(instruction => instruction.OpCode == CilOpCodes.Call
                    && instruction.Operand?.ToString().Contains("get_Current") == true), Is.True,
                () => string.Join("\n", il.Select(instruction => instruction.ToString())));
            Assert.That(il.Any(instruction => instruction.OpCode == CilOpCodes.Box), Is.True,
                () => string.Join("\n", il.Select(instruction => instruction.ToString())));
            Assert.That(il.Any(instruction => instruction.OpCode == CilOpCodes.Ldstr
                    && instruction.Operand is string text && text.Contains("synthetic default")),
                Is.False,
                () => string.Join("\n", il.Select(instruction => instruction.ToString())));
        });
    }

    [Test]
    public void MoveWithoutConversionOperatorKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var point = InjectStruct(app, "Point");
        var vec2 = InjectStruct(app, "Vec2");
        var module = new ModuleDefinition("Conversion.dll");
        SeedCorLibTypes(app, module, point, vec2);
        InjectOperator(vec2, vec2, vec2, module); // exists but converts the wrong pair

        var il = GenerateMove(app, vec2, point, module);

        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("synthetic default")), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString().Contains("op_") == true), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }
}
