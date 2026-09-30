using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using LibCpp2IL.BinaryStructures;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: literal-zero span stores (castle-recovery#146).
// `new Span<T>(arr)`/`new ReadOnlySpan<T>(arr)` lowers to
// `arr == null ? default : (arr + dataOffset, len)`: the non-null arm stores
// `spanLocal := arr + 4*ptrSize` and the null arm stores `spanLocal := 0`.
// When both arms provably build the same span-of-array value, both stores
// rewrite to `Move spanLocal := arr`, which emits `newobj Span::.ctor(arr)`.
public class SpanDataPointerRecoveryTests
{
    private static InjectedTypeAnalysisContext ReadOnlySpanDefinition(ApplicationAnalysisContext app)
    {
        var spanDefinition = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "System", "ReadOnlySpan`1", app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        var t = new GenericParameterTypeAnalysisContext("T", 0, Il2CppTypeEnum.IL2CPP_TYPE_VAR,
            R.GenericParameterAttributes.None, spanDefinition);
        spanDefinition.GenericParameters.Add(t);
        spanDefinition.Fields.Add(new InjectedFieldAnalysisContext("_pointer",
            app.SystemTypes.SystemIntPtrType, R.FieldAttributes.Public, spanDefinition, 0));
        spanDefinition.Fields.Add(new InjectedFieldAnalysisContext("_length",
            app.SystemTypes.SystemIntPtrType, R.FieldAttributes.Public, spanDefinition, 8));
        spanDefinition.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.SpecialName | R.MethodAttributes.RTSpecialName,
            new SzArrayTypeAnalysisContext(t));
        return spanDefinition;
    }

    private static void AssertNoDiagnosticSubstitution(MethodDefinition method)
    {
        var il = method.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                && i.Operand is string text && text.Contains("Ref struct cannot cross")), Is.False,
            () => "the store must not be replaced by a diagnosed default:\n"
                + string.Join("\n", il.Select(i => i.ToString())));
    }

    private static void ResolveJumps(List<Instruction> instructions)
    {
        foreach (var instruction in instructions)
            if (instruction.OpCode is OpCode.Jump or OpCode.ConditionalJump
                && instruction.Operands[0] is Immediate { Value: { } immediate })
                instruction.SetOperand(0, instructions[(int)immediate]);
    }

    [Test]
    public void NullCheckedArraySpanArmsEmitSpanConstructor()
    {
        // `span = arr == null ? default : new ReadOnlySpan<byte>(arr)`: the null
        // arm stores 0 and the other stores `arr + 32`; both must emit
        // `newobj ReadOnlySpan<byte>::.ctor(byte[])`.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var byteType = app.SystemTypes.SystemByteType;
        var byteArray = new SzArrayTypeAnalysisContext(byteType);
        var spanDefinition = ReadOnlySpanDefinition(app);
        var spanType = new GenericInstanceTypeAnalysisContext(spanDefinition, [byteType]);
        var module = new ModuleDefinition("SpanRecovery.dll");
        SeedCorLibTypes(app, module, byteType, spanDefinition,
            app.SystemTypes.SystemBooleanType, app.SystemTypes.SystemVoidType);
        var array = new LocalVariable("array", new Register(null, "array"), byteArray);
        var pointer = new LocalVariable("pointer", new Register(null, "pointer"), byteArray);
        var span = new LocalVariable("span", new Register(null, "span"), spanType);
        var condition = new LocalVariable("condition", new Register(null, "condition"),
            app.SystemTypes.SystemBooleanType);
        var instructions = new List<Instruction>
        {
            new(0, OpCode.CheckEqual, condition, array, new Immediate(0)),
            new(1, OpCode.ConditionalJump, new Immediate(4), condition),
            new(2, OpCode.Move, pointer, array),
            new(3, OpCode.Add, span, pointer, new Immediate(32)),
            new(4, OpCode.Move, span, new Immediate(0)),
            new(5, OpCode.Return),
        };
        ResolveJumps(instructions);
        var (caller, method) = ForeignCaller(app, module, instructions,
            [array, pointer, span, condition]);

        LocalVariables.ResolveTypesAndFields(caller);
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph!);
        LocalVariables.ResolveLateGeneratedTypes(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Newobj), Is.True,
                () => "both span arms must emit the array constructor:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            AssertNoDiagnosticSubstitution(method);
        });
    }

    [Test]
    public void ZeroSpanStoreWithoutArrayProvenanceKeepsDiagnostic()
    {
        // A literal-zero store into a span local whose pointer source cannot be
        // proven must keep its diagnostic - no synthetic span value.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var byteType = app.SystemTypes.SystemByteType;
        var spanDefinition = ReadOnlySpanDefinition(app);
        var spanType = new GenericInstanceTypeAnalysisContext(spanDefinition, [byteType]);
        var module = new ModuleDefinition("SpanRecovery.dll");
        SeedCorLibTypes(app, module, byteType, spanDefinition, app.SystemTypes.SystemVoidType);
        var span = new LocalVariable("span", new Register(null, "span"), spanType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, span, new Immediate(0)),
            new(1, OpCode.Return)], [span]);

        LocalVariables.ResolveTypesAndFields(caller);
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph!);
        LocalVariables.ResolveLateGeneratedTypes(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Newobj), Is.False,
                () => "no array provenance - no span constructor may be emitted:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("synthetic default")), Is.True,
                () => "the diagnostic must be kept when the pointer source is unprovable:\n"
                    + string.Join("\n", il.Select(i => i.ToString())));
        });
    }
}
