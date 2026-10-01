using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using MethodAttributes = AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes;
using ReflectionMethodAttributes = System.Reflection.MethodAttributes;

namespace Cpp2IL.Core.Tests.Analysis;

public class CoalesceStoreRecoveryTests
{
    // The lifter renders `merged = slot ?? (slot = t)` as a flag-checked branch
    // plus a phi-removal copy of the merged value on each edge. A C# compiler
    // emits the read once, after the join, where `dup` covers the stored path;
    // that shape is what ILSpy's cached-`??` transforms fold.
    private static (ISILControlFlowGraph cfg, FieldReference field, Instruction joinHead,
        LocalVariable merged, LocalVariable holder, LocalVariable flag, LocalVariable flag2, LocalVariable stored)
        BuildGraph(ApplicationAnalysisContext app, out InjectedTypeAnalysisContext owner,
        out InjectedFieldAnalysisContext cache)
    {
        owner = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        cache = new InjectedFieldAnalysisContext("cache", app.SystemTypes.SystemObjectType,
            System.Reflection.FieldAttributes.Public | System.Reflection.FieldAttributes.Static, owner, 0);
        owner.Fields.Add(cache);
        var holder = new LocalVariable("holder", new Register(null, "holder"), owner);
        var flag = new LocalVariable("flag", new Register(null, "flag"), app.SystemTypes.SystemBooleanType);
        var flag2 = new LocalVariable("flag2", new Register(null, "flag2"), app.SystemTypes.SystemBooleanType);
        var merged = new LocalVariable("merged", new Register(null, "merged"), app.SystemTypes.SystemObjectType);
        var stored = new LocalVariable("stored", new Register(null, "stored"), app.SystemTypes.SystemObjectType);
        var field = new FieldReference(cache, holder, 0);
        var joinHead = new Instruction(7, OpCode.Move, stored, stored);
        var cfg = new ISILControlFlowGraph([
            new Instruction(0, OpCode.CheckEqual, flag, field, new Immediate(0)),
            new Instruction(1, OpCode.Not, flag2, flag),
            new Instruction(2, OpCode.Move, merged, field),
            new Instruction(3, OpCode.ConditionalJump, joinHead, flag2),
            new Instruction(4, OpCode.Move, stored, new Immediate(1)),
            new Instruction(5, OpCode.Move, field, stored),
            new Instruction(6, OpCode.Move, merged, stored),
            joinHead,
            new Instruction(8, OpCode.Return, merged),
        ]);
        return (cfg, field, joinHead, merged, holder, flag, flag2, stored);
    }

    [Test]
    public void PairedMergesCollapseToSingleJoinHeadRead()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var (cfg, field, joinHead, merged, _, _, _, _) = BuildGraph(app, out _, out _);
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemObjectType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = cfg;
        var join = cfg.FindBlockByInstruction(joinHead)!;
        var branch = cfg.Blocks.Single(block =>
            block.Instructions.Any(instruction => instruction.OpCode == OpCode.ConditionalJump));
        var init = join.Predecessors.Single(predecessor => predecessor != branch);

        CoalesceStoreRecovery.Run(context);

        var head = join.Instructions[0];
        Assert.Multiple(() =>
        {
            Assert.That(head.OpCode, Is.EqualTo(OpCode.Move));
            Assert.That(head.Operands[0], Is.SameAs(merged));
            Assert.That(head.Operands[1], Is.SameAs((IOperand)field));
            Assert.That(branch.Instructions.Any(instruction =>
                    instruction.OpCode == OpCode.Move && ReferenceEquals(instruction.Operands[0], merged)),
                Is.False);
            Assert.That(init.Instructions.Any(instruction =>
                    instruction.OpCode == OpCode.Move && ReferenceEquals(instruction.Operands[0], merged)),
                Is.False);
        });
    }

    [Test]
    public void NullCheckedBranchReadsTheFieldInline()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var (cfg, _, _, merged, holder, flag, flag2, stored) = BuildGraph(app, out var owner,
            out var cache);
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemObjectType, ReflectionMethodAttributes.Static, []);
        context.ControlFlowGraph = cfg;
        context.Locals = [holder, flag, flag2, merged, stored];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("Coalesce.dll");
        foreach (var corlibType in new TypeAnalysisContext[]
                 {
                     app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType,
                     app.SystemTypes.SystemBooleanType,
                 })
            corlibType.PutExtraData("AsmResolverType",
                new TypeDefinition(corlibType.Namespace, corlibType.Name,
                    AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public
                    | AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Class));
        var ownerDefinition = new TypeDefinition("Tests", "Owner",
            AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(ownerDefinition);
        owner.PutExtraData("AsmResolverType", ownerDefinition);
        var fieldDefinition = new FieldDefinition("cache",
            AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Public
            | AsmResolver.PE.DotNet.Metadata.Tables.FieldAttributes.Static,
            new FieldSignature(module.CorLibTypeFactory.Object));
        ownerDefinition.Fields.Add(fieldDefinition);
        cache.PutExtraData("AsmResolverField", fieldDefinition);
        var type = new TypeDefinition("Tests", "Coalesce", AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Object));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        var instructions = method.CilMethodBody!.Instructions;
        var branchIndex = instructions.IndexOf(instructions.First(instruction =>
            instruction.OpCode.Code is CilCode.Brtrue or CilCode.Brfalse));
        Assert.Multiple(() =>
        {
            Assert.That(branchIndex, Is.GreaterThan(0));
            // The branch must read the checked slot itself: a flag temp between
            // the load and the branch is the unfolded shape ILSpy cannot fold.
            Assert.That(instructions[branchIndex - 1].OpCode.Code, Is.EqualTo(CilCode.Ldsfld));
        });
    }

    [Test]
    public void NullCheckedGenericParameterBoxesBeforeTheBranch()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var context = new InjectedMethodAnalysisContext(app.SystemTypes.SystemObjectType, "Run",
            app.SystemTypes.SystemVoidType, ReflectionMethodAttributes.Static, []);
        var parameter = new GenericParameterTypeAnalysisContext("T", 0,
            LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_MVAR, 0, context);
        context.GenericParameters.Add(parameter);
        var item = new LocalVariable("item", new Register(null, "item"), parameter);
        var flag = new LocalVariable("flag", new Register(null, "flag"), app.SystemTypes.SystemBooleanType);
        var target = new Instruction(3, OpCode.Return);
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.CheckEqual, flag, item, new Immediate(0)),
            new Instruction(1, OpCode.ConditionalJump, target, flag),
            new Instruction(2, OpCode.Return),
            target,
        ]);
        context.Locals = [item, flag];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        var module = new ModuleDefinition("CoalesceGeneric.dll");
        foreach (var corlibType in new TypeAnalysisContext[]
                 {
                     app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType,
                     app.SystemTypes.SystemBooleanType,
                 })
            corlibType.PutExtraData("AsmResolverType",
                new TypeDefinition(corlibType.Namespace, corlibType.Name,
                    AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public
                    | AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Class));
        var type = new TypeDefinition("Tests", "CoalesceGeneric",
            AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);

        var instructions = method.CilMethodBody!.Instructions;
        var branchIndex = instructions.IndexOf(instructions.First(instruction =>
            instruction.OpCode.Code is CilCode.Brtrue or CilCode.Brfalse));
        Assert.Multiple(() =>
        {
            Assert.That(branchIndex, Is.GreaterThan(0));
            // brtrue/brfalse cannot take !!T: the read must be boxed into the
            // reference slot first, the same coercion the flag computation used.
            Assert.That(instructions[branchIndex - 1].OpCode.Code, Is.EqualTo(CilCode.Box));
        });
    }
}
