using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using MethodAttributes = AsmResolver.PE.DotNet.Metadata.Tables.MethodAttributes;
using ReflectionMethodAttributes = System.Reflection.MethodAttributes;

namespace Cpp2IL.Core.Tests.Analysis;

public class SwitchLookupTableRecoveryTests
{
    private const ulong TableAddress = 0x5000;

    // u32 little-endian image bytes; the negative pattern exercises the
    // zero-extended element decode.
    private static readonly int[] Constants = [0, 10, 25, -7, 100];

    private static byte[] TableBytes()
    {
        var bytes = new byte[Constants.Length * 4];
        for (var i = 0; i < Constants.Length; i++)
            BinaryPrimitives.WriteUInt32LittleEndian(bytes.AsSpan(i * 4, 4), unchecked((uint)Constants[i]));
        return bytes;
    }

    // The LLVM SwitchToLookupTable shape lifted to ISIL: an adrp-fused table
    // base, an unsigned bounds check on the selector, then the indexed load.
    // jumpTerminator picks the `ldr; b merge` form over the `ldr; ret` form.
    private static (InjectedMethodAnalysisContext context, Instruction load) BuildGraph(
        ApplicationAnalysisContext app, bool jumpTerminator)
    {
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests", "Owner",
            app.SystemTypes.SystemObjectType, System.Reflection.TypeAttributes.Public);
        var int32 = app.SystemTypes.SystemInt32Type;
        var int64 = app.SystemTypes.SystemInt64Type;
        var boolean = app.SystemTypes.SystemBooleanType;

        var sel = new LocalVariable("sel", new Register(null, "sel"), int32);
        var res = new LocalVariable("res", new Register(null, "res"), int32);
        var tbl = new LocalVariable("tbl", new Register(null, "tbl"), int64);
        var flagC = new LocalVariable("flagC", new Register(null, "flagC"), boolean);
        var flagCRaw = new LocalVariable("flagCRaw", new Register(null, "flagCRaw"), boolean);

        var defaultHead = new Instruction(6, OpCode.Move, res, new Immediate(-1));
        var mergeHead = new Instruction(8, OpCode.Return, res);
        var load = new Instruction(4, OpCode.Move, res,
            new MemoryOperand(tbl, sel, addend: 0, scale: 4, accessSize: 4));

        var context = new InjectedMethodAnalysisContext(ownerType, "Read",
            int32, ReflectionMethodAttributes.Static, []);

        context.ControlFlowGraph = new ISILControlFlowGraph(jumpTerminator
            ?
            [
                new Instruction(0, OpCode.Move, tbl, new Immediate((long)TableAddress)),
                new Instruction(1, OpCode.CheckLess, flagCRaw, sel, new Immediate(Constants.Length)),
                new Instruction(2, OpCode.Not, flagC, flagCRaw),
                new Instruction(3, OpCode.ConditionalJump, defaultHead, flagC),
                load,
                new Instruction(5, OpCode.Jump, mergeHead),
                defaultHead,
                new Instruction(7, OpCode.Jump, mergeHead),
                mergeHead,
            ]
            :
            [
                new Instruction(0, OpCode.Move, tbl, new Immediate((long)TableAddress)),
                new Instruction(1, OpCode.CheckLess, flagCRaw, sel, new Immediate(Constants.Length)),
                new Instruction(2, OpCode.Not, flagC, flagCRaw),
                new Instruction(3, OpCode.ConditionalJump, defaultHead, flagC),
                load,
                new Instruction(5, OpCode.Return, res),
                defaultHead,
                new Instruction(7, OpCode.Return, res),
            ]);

        context.Locals = [sel, res, tbl, flagC, flagCRaw];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];

        return (context, load);
    }

    private static MethodDefinition EmitMethod(InjectedMethodAnalysisContext context,
        ApplicationAnalysisContext app, string name)
    {
        var module = new ModuleDefinition("SwitchTable.dll");
        foreach (var corlibType in new TypeAnalysisContext[]
                 {
                     app.SystemTypes.SystemObjectType, app.SystemTypes.SystemVoidType,
                     app.SystemTypes.SystemBooleanType, app.SystemTypes.SystemInt32Type,
                     app.SystemTypes.SystemInt64Type,
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
        context.DeclaringType?.PutExtraData("AsmResolverType", ownerDefinition);

        var type = new TypeDefinition("Tests", name,
            AsmResolver.PE.DotNet.Metadata.Tables.TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("Read", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32));
        type.Methods.Add(method);

        IlGenerator.GenerateIl(context, method);
        return method;
    }

    private static void AssertSwitchHoldsTable(MethodDefinition method)
    {
        var instructions = method.CilMethodBody!.Instructions;
        var switchIndex = instructions.IndexOf(instructions.First(instruction =>
            instruction.OpCode.Code == CilCode.Switch));
        Assert.Multiple(() =>
        {
            Assert.That(switchIndex, Is.GreaterThan(0));
            Assert.That(instructions.Where(i => i.Operand is string text && text.Contains("Unmanaged memory load")),
                Is.Empty);
        });

        var labels = (IReadOnlyList<ICilLabel>)instructions[switchIndex].Operand!;
        Assert.That(labels, Has.Count.EqualTo(Constants.Length));
        for (var i = 0; i < Constants.Length; i++)
        {
            var target = ((CilInstructionLabel)labels[i]).Instruction!;
            Assert.That(target.GetLdcI4Constant(), Is.EqualTo(Constants[i]));
        }
    }

    [Test]
    public void GuardedTableReadWithMergeBecomesSwitch()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var (context, load) = BuildGraph(app, jumpTerminator: true);

        var recovered = SwitchLookupTableRecovery.Run(context,
            (va, size) => va == TableAddress && size == Constants.Length * 4 ? TableBytes() : null);

        var method = EmitMethod(context, app, "SwitchTableMerge");
        Assert.Multiple(() =>
        {
            Assert.That(recovered, Is.EqualTo(1));
            // The load is gone: the dispatch block ends in the recovered switch.
            Assert.That(context.ControlFlowGraph!.Blocks.SelectMany(block => block.Instructions),
                Has.None.SameAs(load));
            Assert.That(context.ControlFlowGraph.Blocks.SelectMany(block => block.Instructions)
                .Count(instruction => instruction.OpCode.ToString() == "Switch"
                    && instruction.Operands.Count == Constants.Length + 2), Is.EqualTo(1));
        });
        AssertSwitchHoldsTable(method);
    }

    [Test]
    public void GuardedTableReadWithReturnBecomesSwitch()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var (context, _) = BuildGraph(app, jumpTerminator: false);

        var recovered = SwitchLookupTableRecovery.Run(context,
            (va, size) => va == TableAddress && size == Constants.Length * 4 ? TableBytes() : null);

        var method = EmitMethod(context, app, "SwitchTableReturn");
        Assert.That(recovered, Is.EqualTo(1));
        AssertSwitchHoldsTable(method);
    }

    [Test]
    public void UnprovenTableBytesStayDiagnosed()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var (context, load) = BuildGraph(app, jumpTerminator: true);

        // A range that cannot be proven static-and-never-patched must keep its
        // load and its diagnostic: any value read at this address is a guess.
        var recovered = SwitchLookupTableRecovery.Run(context, (_, _) => null);

        var method = EmitMethod(context, app, "SwitchTableUnproven");
        var instructions = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(recovered, Is.EqualTo(0));
            Assert.That(context.ControlFlowGraph!.Blocks.SelectMany(block => block.Instructions),
                Has.Some.SameAs(load));
            Assert.That(instructions.Any(i => i.Operand is string text && text.Contains("Unmanaged memory load")),
                Is.True);
        });
    }
}
