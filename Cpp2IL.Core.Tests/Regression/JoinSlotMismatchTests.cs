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

// Recovery cluster: typed local -> mismatched slot (castle-recovery#143). A phi
// at a join the register is dead past materializes edge copies between
// differently-typed reuse versions of the same register - bit-pattern merges no
// managed store can spell, so they always carry the "no legal conversion"
// diagnostic and its synthetic default. Pruned insertion never emits those
// copies. The remaining pins lock the no-fabrication rule: a mismatched
// value-type move keeps the named diagnostic and the default even when the pair
// carries a user-defined conversion operator, because emitting `call
// op_Implicit`/`op_Explicit` there would fabricate a computation the binary
// never ran.
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
