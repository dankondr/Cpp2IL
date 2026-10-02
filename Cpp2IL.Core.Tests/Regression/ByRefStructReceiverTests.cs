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

// Recovery cluster: ghost call-target binding (castle-recovery#106).
// A shared native stub is not in MethodsByAddress, so ResolveCallsViaMethodInfo
// falls back to any MethodInfo* operand in the hidden-argument slot - and that
// operand can be stale (left over from a sibling call). When the receiver slot
// carries a provably unrelated type the bind must be refused, leaving the raw
// address operand. The offset-0 shape of ref structs also means an &S operand
// is a valid &F when S's first field is F: emission narrows it to &S.f0 via
// ldflda instead of substituting a diagnosed default.
public class ByRefStructReceiverTests
{
    private static InjectedTypeAnalysisContext InjectStruct(ApplicationAnalysisContext app, string name) =>
        new(app.AssembliesByName["mscorlib"], "Tests", name,
            app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);

    private static (InjectedTypeAnalysisContext container, InjectedMethodAnalysisContext target)
        ContainerWithInstanceMethod(ApplicationAnalysisContext app)
    {
        var container = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests",
            "Container", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var target = container.InjectMethodContext("Add",
            app.SystemTypes.SystemVoidType, R.MethodAttributes.Public,
            app.SystemTypes.SystemInt32Type);
        return (container, target);
    }

    private static InjectedMethodAnalysisContext Caller(List<Instruction> instructions)
    {
        var app = Cpp2IlApi.CurrentAppContext!;
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests",
            "Owner", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var caller = ownerType.InjectMethodContext("Run", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        return caller;
    }

    [Test]
    public void StaleMethodInfoReceiverMismatchStaysUnresolved()
    {
        // The stub address is unmapped, so the hidden-argument MethodInfo is the
        // only candidate source. It belongs to a different call: the operand in
        // the receiver slot is &S, not the ref type the method is declared on.
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var (container, target) = ContainerWithInstanceMethod(app);
        var ctx = new LocalVariable("ctx", new Register(null, "ctx"),
            new ByRefTypeAnalysisContext(InjectStruct(app, "ReadCursor")));
        var arg = new LocalVariable("arg", new Register(null, "arg"),
            app.SystemTypes.SystemInt32Type);
        var dest = new LocalVariable("dest", new Register(null, "dest"));
        var methodInfo = new RuntimeMethodInfoAnalysisContext(target, container.DeclaringAssembly);
        // target: instance, one int parameter -> hidden MethodInfo slot index 4.
        var call = new Instruction(1, OpCode.Call, new Immediate(0x4000), dest, ctx, arg, methodInfo);
        var caller = Caller([new(0, OpCode.Nop), call, new(2, OpCode.Return)]);

        MetadataResolver.ResolveCallsViaMethodInfo(caller);

        Assert.That(call.Operands[0], Is.TypeOf<Immediate>(),
            () => call.Operands[0]?.ToString() ?? "<null>");
    }

    [Test]
    public void FreshMethodInfoWithMatchingReceiverStillBinds()
    {
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var (container, target) = ContainerWithInstanceMethod(app);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), container);
        var arg = new LocalVariable("arg", new Register(null, "arg"),
            app.SystemTypes.SystemInt32Type);
        var dest = new LocalVariable("dest", new Register(null, "dest"));
        var methodInfo = new RuntimeMethodInfoAnalysisContext(target, container.DeclaringAssembly);
        var call = new Instruction(1, OpCode.Call, new Immediate(0x4000), dest, receiver, arg, methodInfo);
        var caller = Caller([new(0, OpCode.Nop), call, new(2, OpCode.Return)]);

        MetadataResolver.ResolveCallsViaMethodInfo(caller);

        Assert.That(call.Operands[0], Is.SameAs(target));
    }

    [Test]
    public void ArrayNewStubIgnoresAStaleMethodInfo()
    {
        // The array-new stub zeroes x2 itself (`mov x2, xzr; b NewFull`): a MethodInfo* left in x2
        // by an earlier call is not its hidden argument, however well the operands fit.
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var (container, target) = ContainerWithInstanceMethod(app);
        var receiver = new LocalVariable("receiver", new Register(null, "receiver"), container);
        var arg = new LocalVariable("arg", new Register(null, "arg"),
            app.SystemTypes.SystemInt32Type);
        var dest = new LocalVariable("dest", new Register(null, "dest"));
        var methodInfo = new RuntimeMethodInfoAnalysisContext(target, container.DeclaringAssembly);
        var call = new Instruction(1, OpCode.Call, new Immediate(0x4000), dest, receiver, arg, methodInfo);
        var caller = Caller([new(0, OpCode.Nop), call, new(2, OpCode.Return)]);
        ArrayRecovery.ArrayNewStubs.GetOrCreateValue(app)[0x4000] = true;

        MetadataResolver.ResolveCallsViaMethodInfo(caller);

        Assert.That(call.Operands[0], Is.TypeOf<Immediate>());
    }

    [Test]
    public void StructByRefNarrowsToOffsetZeroField()
    {
        // &Envelope is the address of Envelope.payload when payload sits at offset
        // 0: the operand satisfies a &Payload contract via ldflda, not a default.
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var payloadType = InjectStruct(app, "Payload");
        var envelope = InjectStruct(app, "Envelope");
        var payload = new InjectedFieldAnalysisContext("payload", payloadType,
            R.FieldAttributes.Public, envelope, 0);
        envelope.Fields.Add(payload);
        var module = new ModuleDefinition("Narrowing.dll");
        SeedCorLibTypes(app, module, envelope, payloadType, app.SystemTypes.SystemVoidType);
        var payloadDefinition = new TypeDefinition("Tests", "Payload",
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(payloadDefinition);
        var ownerDefinition = new TypeDefinition("Tests", "Envelope",
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        module.TopLevelTypes.Add(ownerDefinition);
        var payloadField = new FieldDefinition("payload", FieldAttributes.Public,
            new FieldSignature(payloadDefinition.ToTypeSignature()));
        ownerDefinition.Fields.Add(payloadField);
        payload.PutExtraData("AsmResolverField", payloadField);
        var src = new LocalVariable("src", new Register(null, "src"),
            new ByRefTypeAnalysisContext(envelope));
        var dst = new LocalVariable("dst", new Register(null, "dst"),
            new ByRefTypeAnalysisContext(payloadType));
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, dst, src),
            new(1, OpCode.Return)], [src, dst]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldflda), Is.True,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string text && text.Contains("Ref struct cannot cross")), Is.False,
                "the narrowed operand must not be replaced by a diagnosed default");
        });
    }
}
