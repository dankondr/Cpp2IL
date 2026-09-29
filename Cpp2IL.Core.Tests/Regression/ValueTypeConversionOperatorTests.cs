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

// Recovery cluster: typed local -> mismatched slot (castle-recovery#143). A Move
// between two differently-typed value types used to reach EmitStackCoerce's "no
// legal conversion" fallthrough and substitute a synthetic default. When either
// type defines a user-defined conversion operator for exactly that pair, C#
// emits `call op_Implicit`/`op_Explicit` for the same operation - the recovered
// conversion call fills the slot with the correctly-typed real value. Pairs
// with no operator keep the named decompiler-issue diagnostic.
public class ValueTypeConversionOperatorTests
{
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

    [Test]
    public void MoveIntoOperatorConvertedSlotEmitsConversionCall()
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
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString().Contains("op_Implicit") == true), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("synthetic default")), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
        });
    }

    [Test]
    public void MoveIntoOperatorConvertedSlotEmitsExplicitConversionCall()
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

        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                && i.Operand?.ToString().Contains("op_Explicit") == true), Is.True,
            () => string.Join("\n", il.Select(i => i.ToString())));
    }

    // A literal into a value-type slot the literal cannot fill directly is still
    // recovered when its emitted integer form converts through a user-defined
    // operator: the literal survives and the coercion runs op_Implicit on it
    // instead of substituting a default for the slot.
    [Test]
    public void MoveImmediateThroughConversionOperatorEmitsLiteralAndCall()
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
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldc_I4
                    && i.Operand?.ToString() == "7"), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString().Contains("op_Implicit") == true), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("cannot fill")), Is.False,
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
