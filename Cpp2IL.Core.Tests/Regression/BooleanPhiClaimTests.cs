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

// Recovery cluster: truthiness -> Boolean no-conversion sites. A local may only
// claim System.Boolean when every definition feeding it proves a 0/1 flag or a
// same-width integer, or when a consumer needs the flag itself (a branch
// condition, a comparison, arithmetic, a typed slot). A register merely reused
// for a bool load on one path and an unrelated value on another is not a bool
// slot; claiming it manufactured truthiness conversions on disagreeing
// producers. A scalar edge into a System.Object slot is equally unproven: the
// binary moved raw bits, so `box` would fabricate a conversion it never made -
// the edge keeps a named note instead.
public class BooleanPhiClaimTests
{
    private static MethodAnalysisContext InjectStatic(InjectedTypeAnalysisContext callerType,
        ModuleDefinition module, MethodDefinition hostMethod, string name,
        TypeAnalysisContext returnType, params TypeAnalysisContext[] parameters)
    {
        var callee = callerType.InjectMethodContext(name, returnType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, parameters);
        var returnSignature = ReferenceEquals(returnType, callerType)
            ? hostMethod.DeclaringType!.ToTypeSignature()
            : returnType.ToTypeSignature();
        var definition = new MethodDefinition(name,
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(returnSignature,
                parameters.Select(p => p.ToTypeSignature()).ToArray()));
        hostMethod.DeclaringType!.Methods.Add(definition);
        callee.PutExtraData("AsmResolverMethod", definition);
        return callee;
    }

    private static void ResolveJumpTargets(List<Instruction> instructions)
    {
        foreach (var instruction in instructions)
            if (instruction.OpCode is OpCode.Jump or OpCode.ConditionalJump)
                instruction.SetOperand(0, instructions[(int)((Immediate)instruction.Operands[0]).Value]);
    }

    [Test]
    public void DeadBoolDefOverwrittenByReferenceEmitsObjectWithNoBox()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("BooleanPhi.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemBooleanType,
            app.SystemTypes.SystemStringType);
        var owner = new LocalVariable("owner", new Register(null, "owner"));
        var merged = new LocalVariable("merged", new Register(null, "merged"));
        var arg = new LocalVariable("arg", new Register(null, "arg"))
            { Type = app.SystemTypes.SystemObjectType };
        var (caller, method) = ForeignCaller(app, module, [], [owner, merged, arg]);
        var callerType = (InjectedTypeAnalysisContext)caller.DeclaringType!;
        callerType.PutExtraData("AsmResolverType", method.DeclaringType!);
        var flagField = new InjectedFieldAnalysisContext("flag", app.SystemTypes.SystemBooleanType,
            R.FieldAttributes.Public, callerType, 16);
        callerType.Fields.Add(flagField);
        var getOwner = InjectStatic(callerType, module, method, "GetOwner", callerType);
        var take = InjectStatic(callerType, module, method, "Take",
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType);
        // One register carries a flag load that is dead - overwritten by a
        // proven reference before the object consumer sees it. The consumer is
        // object-compatible, so no manufactured Boolean claim: the reference
        // edge flows without box, cast or note.
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Call, getOwner, owner),
            new(1, OpCode.Move, merged, new FieldReference(flagField, owner, 16)),
            new(2, OpCode.Move, merged, arg),
            new(3, OpCode.CallVoid, take, merged),
            new(4, OpCode.Return),
        };
        ResolveJumpTargets(instructions);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);

        LocalVariables.ResolveTypesAndFields(caller);
        LocalVariables.ResolveLateGeneratedTypes(caller);
        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        Assert.Multiple(() =>
        {
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("operand to System.Boolean")), Is.False,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Box), Is.False,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Castclass), Is.False,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Call
                    && i.Operand?.ToString().Contains("Take") == true), Is.True,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
        });
    }

    [Test]
    public void ScalarEdgeIntoObjectSlotKeepsNamedNote()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("BooleanPhiScalar.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemBooleanType,
            app.SystemTypes.SystemInt64Type);
        var owner = new LocalVariable("owner", new Register(null, "owner"));
        var merged = new LocalVariable("merged", new Register(null, "merged"));
        var count = new LocalVariable("count", new Register(null, "count"))
            { Type = app.SystemTypes.SystemInt64Type };
        var (caller, method) = ForeignCaller(app, module, [], [owner, merged, count]);
        var callerType = (InjectedTypeAnalysisContext)caller.DeclaringType!;
        callerType.PutExtraData("AsmResolverType", method.DeclaringType!);
        var flagField = new InjectedFieldAnalysisContext("flag", app.SystemTypes.SystemBooleanType,
            R.FieldAttributes.Public, callerType, 16);
        callerType.Fields.Add(flagField);
        var getOwner = InjectStatic(callerType, module, method, "GetOwner", callerType);
        var take = InjectStatic(callerType, module, method, "Take",
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType);
        // The register carries flag and wide-integer scalars on different paths;
        // both reach an object-only consumer. The binary moved raw bits, so
        // each scalar edge keeps a named note rather than a fabricated `box`.
        var instructions = new List<Instruction>
        {
            new(0, OpCode.Call, getOwner, owner),
            new(1, OpCode.Move, merged, new FieldReference(flagField, owner, 16)),
            new(2, OpCode.Move, count, new Immediate(5)),
            new(3, OpCode.Move, merged, count),
            new(4, OpCode.CallVoid, take, merged),
            new(5, OpCode.Return),
        };
        ResolveJumpTargets(instructions);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);

        LocalVariables.ResolveTypesAndFields(caller);
        LocalVariables.ResolveLateGeneratedTypes(caller);
        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        Assert.Multiple(() =>
        {
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("operand to System.Object")), Is.True,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
            Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Box), Is.False,
                () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
        });
    }

    [Test]
    public void FlagAndReferenceMergeIntoBranchKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("BooleanPhiSlot.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemObjectType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemBooleanType,
            app.SystemTypes.SystemStringType);
        var flag = new LocalVariable("flag", new Register(null, "flag"))
            { Type = app.SystemTypes.SystemBooleanType };
        var text = new LocalVariable("text", new Register(null, "text"))
            { Type = app.SystemTypes.SystemStringType };
        var merged = new LocalVariable("merged", new Register(null, "merged"));
        var cond = new LocalVariable("cond", new Register(null, "cond"))
            { Type = app.SystemTypes.SystemBooleanType };
        var (caller, method) = ForeignCaller(app, module, [], [flag, text, merged, cond]);
        // The merge feeds a branch condition: an emitted object would box the
        // flag edge into a silently always-true brtrue, so the Boolean claim is
        // kept and the disagreeing producer keeps its named note.
        var instructions = new List<Instruction>
        {
            new(0, OpCode.ConditionalJump, new Immediate(3), cond),
            new(1, OpCode.Move, flag, new Immediate(1)),
            new(2, OpCode.Jump, new Immediate(4)),
            new(3, OpCode.Move, text, new StringLiteral("s")),
            new(4, OpCode.Phi, merged, flag, text),
            new(5, OpCode.ConditionalJump, new Immediate(7), merged),
            new(6, OpCode.Jump, new Immediate(7)),
            new(7, OpCode.Return),
        };
        ResolveJumpTargets(instructions);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);

        LocalVariables.ResolveTypesAndFields(caller);
        SsaForm.Remove(caller);
        LocalVariables.ResolveLateGeneratedTypes(caller);
        IlGenerator.GenerateIl(caller, method);

        var body = method.CilMethodBody!;
        Assert.That(body.Instructions.Any(i => i.OpCode == CilOpCodes.Ldstr
                && i.Operand is string text && text.Contains("operand to System.Boolean")), Is.True,
            () => string.Join("\n", body.Instructions.Select(i => i.ToString())));
    }
}
