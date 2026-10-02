using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Collections;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// castle-recovery#289: a parameter local is read with ldarg, so a store into it must be starg -
// a stloc writes a shadow local no read sees. And a read of a local that no store reaches on some
// path from the entry (a merge the lifter could not prove) carries the Undefined local note
// instead of silently reading the zeroed slot.
public class ParameterStoreAndUndefinedReadTests
{
    [Test]
    public void AStoreIntoAParameterIsStarg()
    {
        // static int Run(int p, bool c) { if (!c) p = 7; return p; }
        var (caller, method, p, c) = Setup();
        var ret = new Instruction(3, OpCode.Return, p);
        caller.ControlFlowGraph = Graph([
            new(1, OpCode.ConditionalJump, Imm(3), c),
            new(2, OpCode.Move, p, Imm(7)),
            ret]);
        caller.Locals = [p, c];

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Starg && i.Operand is Parameter { Name: "p" }), Is.True, Dump(il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stloc && i.Operand is CilLocalVariable { VariableType.ElementType: ElementType.I4 }),
                Is.False, "no shadow local stands in for the parameter");
        });
    }

    [Test]
    public void TheAddressOfAParameterIsLdarga()
    {
        // ref int q = ref p;   a shadow local's address would point away from the argument
        var (caller, method, p, c) = Setup();
        var q = new LocalVariable("q", new Register(9, "X9", 1),
            new ByRefTypeAnalysisContext(Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type));
        caller.ControlFlowGraph = Graph([
            new(0, OpCode.Move, q, new AddressOf(p)),
            new(1, OpCode.Return, p)]);
        caller.Locals = [p, c, q];

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldarga && i.Operand is Parameter { Name: "p" }), Is.True, Dump(il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldloca), Is.False, Dump(il));
        });
    }

    [Test]
    public void AReadNoStoreReachesOnOnePathCarriesTheNote()
    {
        // if (!c) x = 5; return x;   x is unassigned when c is true
        var (caller, method, p, c) = Setup();
        var x = new LocalVariable("x", new Register(9, "X9", 1), Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type);
        caller.ControlFlowGraph = Graph([
            new(1, OpCode.ConditionalJump, Imm(3), c),
            new(2, OpCode.Move, x, Imm(5)),
            new(3, OpCode.Return, x)]);
        caller.Locals = [p, c, x];

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Count(i => i.OpCode == CilOpCodes.Ldstr && i.Operand is string text
            && text.StartsWith("Undefined local x @") && text.Contains("on some path")), Is.EqualTo(1), Dump(il));
    }

    [Test]
    public void AReadEveryPathStoresHasNoNote()
    {
        // x = c ? 5 : 6; return x;
        var (caller, method, p, c) = Setup();
        var x = new LocalVariable("x", new Register(9, "X9", 1), Cpp2IlApi.CurrentAppContext!.SystemTypes.SystemInt32Type);
        caller.ControlFlowGraph = Graph([
            new(0, OpCode.ConditionalJump, Imm(3), c),
            new(1, OpCode.Move, x, Imm(5)),
            new(2, OpCode.Jump, Imm(4)),
            new(3, OpCode.Move, x, Imm(6)),
            new(4, OpCode.Return, x)]);
        caller.Locals = [p, c, x];

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False, Dump(il));
    }

    private static (InjectedMethodAnalysisContext Caller, MethodDefinition Method, LocalVariable P, LocalVariable C) Setup()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var boolean = app.SystemTypes.SystemBooleanType;
        var callerType = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "ForeignCaller", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = new InjectedMethodAnalysisContext(callerType, "Run", int32,
            R.MethodAttributes.Public | R.MethodAttributes.Static, [int32, boolean], ["p", "c"],
            [R.ParameterAttributes.None, R.ParameterAttributes.None]);
        var p = new LocalVariable("p", new Register(0, "X0"), int32);
        var c = new LocalVariable("c", new Register(1, "X1"), boolean);
        caller.ParameterLocals = [p, c];
        caller.AnalysisWarnings = [];

        var module = new ModuleDefinition("ParameterStore.dll");
        SeedCorLibTypes(app, module, int32, boolean, app.SystemTypes.SystemVoidType);
        var owner = new TypeDefinition("Tests", "ForeignCaller", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32,
                [module.CorLibTypeFactory.Int32, module.CorLibTypeFactory.Boolean]));
        owner.Methods.Add(method);
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "p", default));
        method.ParameterDefinitions.Add(new ParameterDefinition(2, "c", default));
        return (caller, method, p, c);
    }

    private static ISILControlFlowGraph Graph(List<Instruction> instructions)
    {
        foreach (var instruction in instructions)
            if (instruction.OpCode is OpCode.Jump or OpCode.ConditionalJump && instruction.Operands[0] is Immediate target)
                instruction.SetOperand(0, instructions.Single(i => i.Index == (int)target.Value));
        return new ISILControlFlowGraph(instructions);
    }

    private static string Dump(IEnumerable<CilInstruction> il) => string.Join("\n", il.Select(i => i.ToString()));
}
