using System;
using System.Linq;
using AsmResolver;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils.AsmResolver;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Analysis;

public class BlockMemoryImportRecoveryTests
{
    private ApplicationAnalysisContext _app = null!;
    private TypeAnalysisContext _byte = null!;
    private TypeAnalysisContext _int32 = null!;
    private TypeAnalysisContext _int64 = null!;
    private TypeAnalysisContext _intPtr = null!;
    private TypeAnalysisContext _byteArray = null!;

    [SetUp]
    public void Setup()
    {
        Cpp2IlApi.ResetInternalState();
        _app = TestGameLoader.LoadSimple2019Game();
        _byte = _app.SystemTypes.SystemByteType;
        _int32 = _app.SystemTypes.SystemInt32Type;
        _int64 = _app.SystemTypes.SystemInt64Type;
        _intPtr = _app.SystemTypes.SystemIntPtrType;
        _byteArray = _byte.MakeSzArrayType();
    }

    private static LocalVariable Reg(string registerName, TypeAnalysisContext? type = null, int version = -1) =>
        new($"v_{registerName}_{version}", new Register(null, registerName, version), type);

    // ---------- Pass-level tests ----------

    // The shape the ARM64 lifter gives an unresolved `bl`: Immediate target, X0 result
    // local, then the raw ABI argument registers X0..X7 followed by V0..V7.
    private MethodAnalysisContext CallerWithUnresolvedCall(out Instruction call,
        TypeAnalysisContext? dstType = null, TypeAnalysisContext? srcType = null,
        TypeAnalysisContext? countType = null, bool resultUsed = false)
    {
        // The fixture binary is x86-64; the pass is ARM64-only, and the raw ABI
        // operand shape below is what NewArmV8InstructionSet produces - so force the
        // ARM64 instruction set for the calling-convention check.
        _app.InstructionSet = new NewArmV8InstructionSet();
        var caller = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "F", _intPtr,
            R.MethodAttributes.Public | R.MethodAttributes.Static, [])
        {
            ParameterLocals = [],
            AnalysisWarnings = [],
        };
        var result = Reg("X0", version: 1);
        var integer = Enumerable.Range(0, 8).Select(i => Reg($"X{i}")).ToArray();
        var floatArgs = Enumerable.Range(0, 8).Select(i => Reg($"V{i}")).ToArray();
        integer[0].Type = dstType ?? new PointerTypeAnalysisContext(_byte);
        integer[1].Type = srcType ?? new PointerTypeAnalysisContext(_byte);
        integer[2].Type = countType ?? _int64;

        call = new Instruction(0, OpCode.Call,
            new Immediate(0x10000), result, integer[0], integer[1], integer[2], integer[3],
            integer[4], integer[5], integer[6], integer[7],
            floatArgs[0], floatArgs[1], floatArgs[2], floatArgs[3],
            floatArgs[4], floatArgs[5], floatArgs[6], floatArgs[7]);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            call,
            resultUsed ? new Instruction(1, OpCode.Return, result) : new Instruction(1, OpCode.Return),
        ]);
        caller.Locals = [result, .. integer, .. floatArgs];
        return caller;
    }

    [Test]
    public void MemcpyCallRewritesToMemoryCopy()
    {
        var caller = CallerWithUnresolvedCall(out var call);
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.True);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.MemoryCopy));
        Assert.That(call.Operands, Has.Count.EqualTo(3), "unused return local is dropped");
        Assert.That(call.Destination, Is.Null);
        Assert.That(call.Sources, Has.Count.EqualTo(3));
    }

    [Test]
    public void MemsetCallRewritesToMemorySet()
    {
        var caller = CallerWithUnresolvedCall(out var call, srcType: _int32);
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memset"), Is.True);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.MemorySet));
    }

    [Test]
    public void MemmoveCallRewritesToMemoryMove()
    {
        var caller = CallerWithUnresolvedCall(out var call);
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memmove"), Is.True);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.MemoryMove));
    }

    [Test]
    public void UsedResultIsKeptAsNativeInt()
    {
        var caller = CallerWithUnresolvedCall(out var call, resultUsed: true);
        var result = (LocalVariable)call.Operands[1];
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.True);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.MemoryCopy));
        Assert.That(call.Operands, Has.Count.EqualTo(4));
        Assert.That(call.Operands[3], Is.SameAs(result));
        Assert.That(call.Destination, Is.SameAs(result));
        Assert.That(result.Type, Is.SameAs(_intPtr));
    }

    [Test]
    public void NonImportNameDoesNotRewrite()
    {
        var caller = CallerWithUnresolvedCall(out var call);
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "strlen"), Is.False);
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "__memcpy_chk"), Is.False);
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, null), Is.False);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    [Test]
    public void MissingArgumentSlotsDoesNotRewrite()
    {
        var caller = CallerWithUnresolvedCall(out var call);
        call.SetOperands(call.Operands[0], call.Operands[1], call.Operands[2]);
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.False);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    // The dominant real dst shape: an integral local defined by `obj + fieldOffset`
    // arithmetic over a managed base. The write is legal only when every field the
    // immediate byte range covers is reference-free.
    private TypeAnalysisContext PodClass(params (string Name, TypeAnalysisContext Type, int Offset)[] fields)
    {
        var owner = new InjectedTypeAnalysisContext(_app.AssembliesByName["mscorlib"], "Tests", "Pod",
            _app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        foreach (var (name, type, offset) in fields)
            owner.Fields.Add(new InjectedFieldAnalysisContext(name, type,
                R.FieldAttributes.Public, owner, offset));
        return owner;
    }

    private MethodAnalysisContext CallerWithDefinedDst(out Instruction call,
        Instruction dstDef, LocalVariable dst, TypeAnalysisContext? countType = null,
        TypeAnalysisContext? srcType = null)
    {
        var caller = CallerWithUnresolvedCall(out call, dstType: _int64, countType: countType,
            srcType: srcType);
        // ControlFlowGraph.Instructions is a flattened copy - rebuild the graph so
        // the definition actually reaches the pass.
        var rest = caller.ControlFlowGraph!.Instructions.ToList();
        caller.ControlFlowGraph = new ISILControlFlowGraph([dstDef, .. rest]);
        call.SetOperand(2, dst);
        caller.Locals!.Add(dst);
        return caller;
    }

    [Test]
    public void IntegralDstFromManagedFieldOffsetRewrites()
    {
        // dst = pod + 0x10 where pod's field@0x10 is an int32 inside a POD class:
        // memcpy(podField, src, 4) writes a reference-free field region.
        var pod = PodClass(("a", _int32, 0x10), ("b", _int64, 0x18));
        var podLocal = new LocalVariable("pod", new Register(0, "X19"), pod);
        var dst = new LocalVariable("dst", new Register(0, "X0"), _int64);
        var def = new Instruction(0, OpCode.Add, dst, podLocal, new Immediate(0x10));
        var caller = CallerWithDefinedDst(out var call, def, dst);
        caller.Locals!.Add(podLocal);
        call.SetOperand(4, new Immediate(4));
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.True);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.MemoryCopy));
    }

    [Test]
    public void IntegralDstIntoReferenceFieldDoesNotRewrite()
    {
        // pod + 0x18 lands on a `string` field: the copy would write a managed
        // reference slot without a barrier.
        var pod = PodClass(("a", _int32, 0x10), ("s", _app.SystemTypes.SystemStringType, 0x18));
        var podLocal = new LocalVariable("pod", new Register(0, "X19"), pod);
        var dst = new LocalVariable("dst", new Register(0, "X0"), _int64);
        var def = new Instruction(0, OpCode.Add, dst, podLocal, new Immediate(0x18));
        var caller = CallerWithDefinedDst(out var call, def, dst);
        caller.Locals!.Add(podLocal);
        call.SetOperand(4, new Immediate(8));
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.False);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    [Test]
    public void IntegralDstSpanningIntoReferenceFieldDoesNotRewrite()
    {
        // Range [0x10, 0x20) covers the POD field @0x10 and the reference field @0x18.
        var pod = PodClass(("a", _int32, 0x10), ("s", _app.SystemTypes.SystemStringType, 0x18),
            ("b", _int64, 0x20));
        var podLocal = new LocalVariable("pod", new Register(0, "X19"), pod);
        var dst = new LocalVariable("dst", new Register(0, "X0"), _int64);
        var def = new Instruction(0, OpCode.Add, dst, podLocal, new Immediate(0x10));
        var caller = CallerWithDefinedDst(out var call, def, dst);
        caller.Locals!.Add(podLocal);
        call.SetOperand(4, new Immediate(0x10));
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.False);
    }

    [Test]
    public void IntegralDstPastKnownFieldsWithoutSizeDoesNotRewrite()
    {
        // Range ending past the last declared field with no instance-size metadata:
        // the tail bytes are unprovable, so the honest answer is to keep the call.
        var pod = PodClass(("a", _int32, 0x10));
        var podLocal = new LocalVariable("pod", new Register(0, "X19"), pod);
        var dst = new LocalVariable("dst", new Register(0, "X0"), _int64);
        var def = new Instruction(0, OpCode.Add, dst, podLocal, new Immediate(0x10));
        var caller = CallerWithDefinedDst(out var call, def, dst);
        caller.Locals!.Add(podLocal);
        call.SetOperand(4, new Immediate(0x40));
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.False);
    }

    [Test]
    public void IntegralDstFromIntPtrMoveRewrites()
    {
        var source = new LocalVariable("src", new Register(0, "X19"), _intPtr);
        var dst = new LocalVariable("dst", new Register(0, "X0"), _int64);
        var def = new Instruction(0, OpCode.Move, dst, source);
        var caller = CallerWithDefinedDst(out var call, def, dst, srcType: _int32);
        caller.Locals!.Add(source);
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memset"), Is.True);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.MemorySet));
    }

    [Test]
    public void IntegralParamWithoutDefinitionsDoesNotRewrite()
    {
        // A bare integer is a number, not a proven pointer.
        var caller = CallerWithUnresolvedCall(out var call, dstType: _int64);
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.False);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    [Test]
    public void UntypedDstFromManagedMoveRewritesWhenBounded()
    {
        // The commonest real shape: mov x0, x19 where x19 is a managed reference -
        // post-forwarding the dst local is untyped but every definition stores the
        // real object reference, and conv.u yields the object base address.
        var pod = PodClass(("a", _int32, 0x10), ("b", _int64, 0x18));
        var podLocal = new LocalVariable("pod", new Register(0, "X19"), pod);
        var dst = new LocalVariable("dst", new Register(0, "X0"), null);
        var def = new Instruction(0, OpCode.Move, dst, podLocal);
        var caller = CallerWithDefinedDst(out var call, def, dst);
        caller.Locals!.Add(podLocal);
        call.SetOperand(4, new Immediate(0x20));
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.True);
    }

    [Test]
    public void UntypedDstFromIntegralMoveDoesNotRewrite()
    {
        // The untyped local would hold a boxed integer - conv.u reads the box header,
        // not the pointer value.
        var source = new LocalVariable("src", new Register(0, "X19"), _int64);
        var dst = new LocalVariable("dst", new Register(0, "X0"), null);
        var def = new Instruction(0, OpCode.Move, dst, source);
        var caller = CallerWithDefinedDst(out var call, def, dst);
        caller.Locals!.Add(source);
        call.SetOperand(4, new Immediate(8));
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.False);
    }

    [Test]
    public void ManagedObjectDestinationWithDynamicCountDoesNotRewrite()
    {
        var pod = PodClass(("a", _int32, 0x10), ("b", _int64, 0x18));
        var caller = CallerWithUnresolvedCall(out var call, dstType: pod);
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.False);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    [Test]
    public void ManagedObjectDestinationWithinBoundsRewrites()
    {
        var pod = PodClass(("a", _int32, 0x10), ("b", _int64, 0x18));
        var caller = CallerWithUnresolvedCall(out var call, dstType: pod);
        call.SetOperand(4, new Immediate(0x20));
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.True);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.MemoryCopy));
    }

    [Test]
    public void ManagedReferenceDestinationDoesNotRewrite()
    {
        // A `string` destination over a dynamic count cannot be bounded to a proven
        // reference-free span.
        var caller = CallerWithUnresolvedCall(out var call, dstType: _app.SystemTypes.SystemStringType);
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.False);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    [Test]
    public void SzArrayElementDestinationRewrites()
    {
        var caller = CallerWithUnresolvedCall(out var call, dstType: _byteArray);
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.True);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.MemoryCopy));
    }

    [Test]
    public void ManagedSourceIsRepresentableForMemcpy()
    {
        // A managed reference as memcpy src: conv.u yields the object address and
        // reading it needs no barrier.
        var caller = CallerWithUnresolvedCall(out var call, srcType: _byteArray);
        call.SetOperand(4, new Immediate(8));
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.True);
    }

    [Test]
    public void ObjectTypedSourceDoesNotRewrite()
    {
        // An `object` operand may be a boxed integer; conv.u would read the box.
        var caller = CallerWithUnresolvedCall(out var call,
            srcType: _app.SystemTypes.SystemObjectType);
        call.SetOperand(4, new Immediate(8));
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.False);
    }

    [Test]
    public void ObjectTypedResultDoesNotRewrite()
    {
        var caller = CallerWithUnresolvedCall(out var call, resultUsed: true);
        ((LocalVariable)call.Operands[1]).Type = _app.SystemTypes.SystemObjectType;
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.False);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    [Test]
    public void IntegralResultIsKept()
    {
        var caller = CallerWithUnresolvedCall(out var call, resultUsed: true);
        ((LocalVariable)call.Operands[1]).Type = _int64;
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.True);
        Assert.That(call.Operands, Has.Count.EqualTo(4));
    }

    [Test]
    public void ReferenceElementPointerDestinationDoesNotRewrite()
    {
        // `string*` points into managed reference cells; cpblk through it would skip
        // the write barriers the copied references need.
        var caller = CallerWithUnresolvedCall(out var call,
            dstType: new PointerTypeAnalysisContext(_app.SystemTypes.SystemStringType));
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.False);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    [Test]
    public void ReferenceElementByrefDestinationDoesNotRewrite()
    {
        var caller = CallerWithUnresolvedCall(out var call,
            dstType: new ByRefTypeAnalysisContext(_app.SystemTypes.SystemStringType));
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memset"), Is.False);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    [Test]
    public void PointerFillOperandDoesNotRewriteMemset()
    {
        var caller = CallerWithUnresolvedCall(out var call, srcType: new PointerTypeAnalysisContext(_byte));
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memset"), Is.False);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    [Test]
    public void ImmediateOperandsPassThePredicates()
    {
        // Absolute addresses and literal sizes are honest unmanaged shapes.
        var caller = CallerWithUnresolvedCall(out _);
        var immediate = new Immediate(0x200000);
        Assert.That(BlockMemoryImportRecovery.IsProvablyReferenceFreeRegion(immediate,
            new Immediate(8), caller), Is.True);
        Assert.That(BlockMemoryImportRecovery.IsPointerOperandRepresentable(immediate, caller), Is.True);
        Assert.That(BlockMemoryImportRecovery.IsScalarOperand(immediate, caller), Is.True);
    }

    [Test]
    public void RunIgnoresNonElfBinary()
    {
        // The fixture binary is x86-64 PE: even with the instruction set forced to
        // ARM64 there is no relocated ELF symbol, so nothing is rewritten.
        _app.InstructionSet = new NewArmV8InstructionSet();
        var caller = CallerWithUnresolvedCall(out var call);
        BlockMemoryImportRecovery.Run(caller);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    // ---------- Emission-level tests: the generated body must load, JIT and run. ----------

    private MethodAnalysisContext RunnerMethod(string name, TypeAnalysisContext returnType,
        (TypeAnalysisContext Type, string Name)[] parameters, out LocalVariable[] locals)
    {
        var caller = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, name, returnType,
            R.MethodAttributes.Public | R.MethodAttributes.Static,
            parameters.Select(p => p.Type).ToArray(), parameters.Select(p => p.Name).ToArray());
        locals = parameters.Select((p, i) => new LocalVariable(p.Name, new Register(i, $"X{i}"), p.Type)).ToArray();
        caller.ParameterLocals = [.. locals];
        caller.Locals = [.. locals];
        caller.AnalysisWarnings = [];
        return caller;
    }

    // Placeholder TypeDefinitions so ToTypeSignature can name the corlib contexts the
    // reduced test fixture lacks AsmResolver metadata for; the rebind pass below maps
    // every emitted reference back onto the real corlib signatures.
    private ModuleDefinition EmitModule(params TypeAnalysisContext[] types)
    {
        var module = new ModuleDefinition("BlockMem.dll",
            new AssemblyReference("System.Private.CoreLib", typeof(object).Assembly.GetName().Version!));
        foreach (var context in types)
        {
            var definition = new TypeDefinition(context.Namespace, context.Name,
                TypeAttributes.Public | (context.IsValueType
                    ? TypeAttributes.Sealed | TypeAttributes.SequentialLayout
                    : TypeAttributes.Class),
                context.IsValueType
                    ? module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType")
                    : module.CorLibTypeFactory.Object.Type);
            module.TopLevelTypes.Add(definition);
            context.PutExtraData("AsmResolverType", definition);
        }
        return module;
    }

    private static TypeSignature Rebind(ModuleDefinition module, TypeSignature signature) =>
        signature switch
        {
            SzArrayTypeSignature szArray => Rebind(module, szArray.BaseType).MakeSzArrayType(),
            PointerTypeSignature pointer => Rebind(module, pointer.BaseType).MakePointerType(),
            ByReferenceTypeSignature byRef => Rebind(module, byRef.BaseType).MakeByReferenceType(),
            _ => signature.FullName switch
            {
                "System.Byte" => module.CorLibTypeFactory.Byte,
                "System.Int32" => module.CorLibTypeFactory.Int32,
                "System.Int64" => module.CorLibTypeFactory.Int64,
                "System.IntPtr" => module.CorLibTypeFactory.IntPtr,
                "System.String" => module.CorLibTypeFactory.String,
                "System.Object" => module.CorLibTypeFactory.Object,
                "System.Void" => module.CorLibTypeFactory.Void,
                _ => signature,
            },
        };

    private static void RebindPrimitives(MethodDefinition definition, ModuleDefinition module)
    {
        foreach (var local in definition.CilMethodBody!.LocalVariables)
            local.VariableType = Rebind(module, local.VariableType);
        foreach (var instruction in definition.CilMethodBody.Instructions)
            if (instruction.Operand is ITypeDefOrRef operandType
                && CorLibSig(module, operandType.FullName) is { } rebound)
                instruction.Operand = rebound.ToTypeDefOrRef();
    }

    private static TypeSignature? CorLibSig(ModuleDefinition module, string fullName) => fullName switch
    {
        "System.Byte" => module.CorLibTypeFactory.Byte,
        "System.Int32" => module.CorLibTypeFactory.Int32,
        "System.Int64" => module.CorLibTypeFactory.Int64,
        "System.IntPtr" => module.CorLibTypeFactory.IntPtr,
        "System.String" => module.CorLibTypeFactory.String,
        "System.Object" => module.CorLibTypeFactory.Object,
        _ => null,
    };

    private static TypeSignature Sig(ModuleDefinition module, TypeAnalysisContext type) =>
        type switch
        {
            SzArrayTypeAnalysisContext szArray => Sig(module, szArray.ElementType).MakeSzArrayType(),
            _ => type.FullName switch
            {
                "System.Byte" => module.CorLibTypeFactory.Byte,
                "System.Int32" => module.CorLibTypeFactory.Int32,
                "System.Int64" => module.CorLibTypeFactory.Int64,
                "System.IntPtr" => module.CorLibTypeFactory.IntPtr,
                "System.String" => module.CorLibTypeFactory.String,
                "System.Void" => module.CorLibTypeFactory.Void,
                _ => type.ToTypeSignature(),
            },
        };

    private static MethodDefinition Definition(ModuleDefinition module, string name,
        TypeAnalysisContext returnType, (TypeAnalysisContext Type, string Name)[] parameters)
    {
        var owner = new TypeDefinition("Tests", name + "Runner", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var definition = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(Sig(module, returnType),
                parameters.Select(p => Sig(module, p.Type))));
        owner.Methods.Add(definition);
        for (var i = 0; i < parameters.Length; i++)
            definition.ParameterDefinitions.Add(new ParameterDefinition((ushort)(i + 1), parameters[i].Name, default));
        return definition;
    }

    private static (R.Assembly, R.MethodInfo) EmitAssembly(
        MethodAnalysisContext context, MethodDefinition definition, ModuleDefinition module)
    {
        IlGenerator.GenerateIl(context, definition);
        RebindPrimitives(definition, module);
        var assembly = new AssemblyDefinition("BlockMem", new Version(1, 0));
        assembly.Modules.Add(module);
        using var stream = new System.IO.MemoryStream();
        module.Write(stream);
        var loaded = R.Assembly.Load(stream.ToArray());
        return (loaded, loaded.GetType($"Tests.{context.Name}Runner")!.GetMethod("Run")!);
    }

    private ModuleDefinition NewModule(params TypeAnalysisContext[] types) => EmitModule(types);

    private static AddressOf ElementAddress(LocalVariable array, int offset) =>
        new(new ArrayAccess(array, new Immediate(offset)));

    [TestCase(0)]
    [TestCase(1)]
    [TestCase(7)]
    [TestCase(13)]
    public void MemoryCopyEmitsCpblkAndCopiesBytes(int count)
    {
        var parameters = new[] { (_byteArray, "dst"), (_byteArray, "src") };
        var caller = RunnerMethod("Copy", _app.SystemTypes.SystemVoidType, parameters, out var locals);
        // &dst[1] <- &src[0]: deliberately unaligned destination.
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.MemoryCopy, ElementAddress(locals[0], 1), ElementAddress(locals[1], 0),
                new Immediate(count)),
            new Instruction(1, OpCode.Return),
        ]);

        var module = NewModule(_byte);
        var definition = Definition(module, "Copy", _app.SystemTypes.SystemVoidType, parameters);
        var (_, method) = EmitAssembly(caller, definition, module);

        // A one-byte copy between byte& operands is Byte's typed assignment
        // (ldobj/stobj); larger extents keep cpblk.
        if (count == 1)
        {
            Assert.That(definition.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Ldobj), Is.True);
            Assert.That(definition.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Stobj), Is.True);
        }
        else
            Assert.That(definition.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Cpblk), Is.True);

        var dst = Enumerable.Repeat((byte)0xEE, 16).ToArray();
        var src = Enumerable.Range(0, 16).Select(i => (byte)i).ToArray();
        method.Invoke(null, [dst, src]);
        for (var i = 0; i < count; i++)
            Assert.That(dst[i + 1], Is.EqualTo(src[i]), $"byte {i + 1}");
        Assert.That(dst[0], Is.EqualTo(0xEE), "preceding byte must be untouched");
        Assert.That(dst[1 + count], Is.EqualTo(0xEE), "trailing byte must be untouched");
    }

    [TestCase(0)]
    [TestCase(1)]
    [TestCase(7)]
    public void MemorySetEmitsInitblkAndFillsBytes(int count)
    {
        var parameters = new[] { (_byteArray, "dst"), (_int32, "value") };
        var caller = RunnerMethod("Fill", _app.SystemTypes.SystemVoidType, parameters, out var locals);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.MemorySet, ElementAddress(locals[0], 0), locals[1], new Immediate(count)),
            new Instruction(1, OpCode.Return),
        ]);

        var module = NewModule(_byte, _int32);
        var definition = Definition(module, "Fill", _app.SystemTypes.SystemVoidType, parameters);
        var (_, method) = EmitAssembly(caller, definition, module);

        Assert.That(definition.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Initblk), Is.True);

        var dst = Enumerable.Repeat((byte)0xCC, 16).ToArray();
        method.Invoke(null, [dst, 0x1A5]); // only the low byte may be used
        for (var i = 0; i < count; i++)
            Assert.That(dst[i], Is.EqualTo(0xA5), $"byte {i}");
        Assert.That(dst[count], Is.EqualTo(0xCC), "trailing byte must be untouched");
    }

    // memmove lowers to the recovered corlib's own Buffer.MemoryCopy MethodDef.
    // The 2019 fixture's corlib does not declare it, so this fixture models a
    // metadata-carried member: an injected context method bound to a runnable
    // def that forwards to the real corlib member.
    private MethodDefinition BindBufferMemoryCopy(ModuleDefinition module)
    {
        var buffer = _app.SystemTypes.SystemObjectType.DeclaringAssembly
            .GetTypeByFullName("System.Buffer")!;
        var voidPtr = new PointerTypeAnalysisContext(_app.SystemTypes.SystemVoidType);
        var memoryCopy = buffer.Methods.FirstOrDefault(m => m is { IsStatic: true }
            && m.Name == "MemoryCopy" && m.Parameters.Count == 4);
        if (memoryCopy == null)
        {
            memoryCopy = new InjectedMethodAnalysisContext(buffer, "MemoryCopy",
                _app.SystemTypes.SystemVoidType,
                R.MethodAttributes.Public | R.MethodAttributes.Static,
                [voidPtr, voidPtr, _int64, _int64]);
            buffer.Methods.Add(memoryCopy);
        }
        var bufferDef = new TypeDefinition("System", "Buffer",
            TypeAttributes.Public | TypeAttributes.Class, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(bufferDef);
        var definition = new MethodDefinition("MemoryCopy",
            MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Void,
                memoryCopy.Parameters.Select(p => (TypeSignature)(p.ParameterType is PointerTypeAnalysisContext
                    ? module.CorLibTypeFactory.Void.MakePointerType()
                    : Sig(module, p.ParameterType))).ToArray()));
        bufferDef.Methods.Add(definition);
        memoryCopy.PutExtraData("AsmResolverMethod", definition);

        // Trampoline body: forward every argument to the real corlib member.
        definition.CilMethodBody = new CilMethodBody();
        for (ushort i = 0; i < 4; i++)
            definition.CilMethodBody.Instructions.Add(new CilInstruction(CilOpCodes.Ldarg, i));
        var real = module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "Buffer")
            .CreateMemberReference("MemoryCopy", MethodSignature.CreateStatic(
                module.CorLibTypeFactory.Void,
                [module.CorLibTypeFactory.Void.MakePointerType(),
                    module.CorLibTypeFactory.Void.MakePointerType(),
                    module.CorLibTypeFactory.Int64, module.CorLibTypeFactory.Int64]));
        definition.CilMethodBody.Instructions.Add(CilOpCodes.Call, real);
        definition.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        return definition;
    }

    [Test]
    public void MemoryMoveEmitsOverlapSafeCopy()
    {
        var parameters = new[] { (_byteArray, "buf"), (_int32, "srcOff"), (_int32, "dstOff"), (_int32, "n") };
        var caller = RunnerMethod("Move", _app.SystemTypes.SystemVoidType, parameters, out var locals);
        var move = new Instruction(0, OpCode.MemoryMove,
            new AddressOf(new ArrayAccess(locals[0], locals[2])),
            new AddressOf(new ArrayAccess(locals[0], locals[1])),
            locals[3]);
        caller.ControlFlowGraph = new ISILControlFlowGraph([move, new Instruction(1, OpCode.Return)]);

        var module = NewModule(_byte, _int32);
        var copyDef = BindBufferMemoryCopy(module);
        var definition = Definition(module, "Move", _app.SystemTypes.SystemVoidType, parameters);
        var (_, method) = EmitAssembly(caller, definition, module);

        Assert.That(definition.CilMethodBody!.Instructions.Any(i =>
            i.OpCode == CilOpCodes.Call && i.Operand == (IMethodDescriptor)copyDef), Is.True,
            "memmove must call the corlib's own Buffer.MemoryCopy MethodDef");

        // Forward-overlapping move: dst > src, 5 bytes of "abcde" over [4..9).
        var buf = "abcdefghij".Select(c => (byte)c).ToArray();
        method.Invoke(null, [buf, 0, 4, 5]);
        Assert.That(buf, Is.EqualTo("abcdabcdej".Select(c => (byte)c).ToArray()));
    }

    [Test]
    public void MemoryCopyPreservesReturnedDestinationWhenResultIsRead()
    {
        var parameters = new[] { (_byteArray, "dst"), (_byteArray, "src") };
        var caller = RunnerMethod("CopyRet", _intPtr, parameters, out var locals);
        var result = new LocalVariable("res", new Register(0, "X0", 1), _intPtr);
        caller.Locals = [.. locals, result];
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.MemoryCopy, ElementAddress(locals[0], 0), ElementAddress(locals[1], 0),
                new Immediate(4), result),
            new Instruction(1, OpCode.Return, result),
        ]);

        var module = NewModule(_byte, _intPtr);
        var definition = Definition(module, "CopyRet", _intPtr, parameters);
        var (_, method) = EmitAssembly(caller, definition, module);

        var dst = Enumerable.Repeat((byte)0xEE, 16).ToArray();
        var src = Enumerable.Range(0, 16).Select(i => (byte)i).ToArray();
        var returned = (IntPtr)method.Invoke(null, [dst, src])!;
        Assert.That(returned, Is.Not.EqualTo(IntPtr.Zero),
            "memcpy's returned dst must reach the result local");
        Assert.That(dst.Take(4), Is.EqualTo(src.Take(4)));
    }

    [Test]
    public void ManagedReferenceArrayDestinationFailsHonestly()
    {
        var stringArray = _app.SystemTypes.SystemStringType.MakeSzArrayType();
        var parameters = new (TypeAnalysisContext Type, string Name)[] { (stringArray, "dst"), (stringArray, "src") };
        var caller = RunnerMethod("CopyRefs", _app.SystemTypes.SystemVoidType, parameters, out var locals);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.MemoryCopy, ElementAddress(locals[0], 0), ElementAddress(locals[1], 0),
                new Immediate(8)),
            new Instruction(1, OpCode.Return),
        ]);

        var module = NewModule(_app.SystemTypes.SystemStringType);
        var definition = Definition(module, "CopyRefs", _app.SystemTypes.SystemVoidType, parameters);
        IlGenerator.GenerateIl(caller, definition);
        RebindPrimitives(definition, module);

        Assert.That(definition.CilMethodBody!.Instructions.Any(i => i.OpCode == CilOpCodes.Cpblk), Is.False,
            "cpblk must not be emitted over a managed-reference region");
        Assert.That(definition.CilMethodBody.Instructions.Any(i =>
            i.OpCode == CilOpCodes.Ldstr && i.Operand is string text
            && text.Contains("Unproven block memory operand")), Is.True);

        var assembly = new AssemblyDefinition("BlockMem", new Version(1, 0));
        assembly.Modules.Add(module);
        using var stream = new System.IO.MemoryStream();
        module.Write(stream);
        var loaded = R.Assembly.Load(stream.ToArray());
        var method = loaded.GetType("Tests.CopyRefsRunner")!.GetMethod("Run")!;
        var dst = new[] { "a", "b" };
        var src = new[] { "c", "d" };
        Assert.That(() => method.Invoke(null, [dst, src]),
            Throws.TypeOf<R.TargetInvocationException>(), "the body must throw, not silently copy");
        Assert.That(dst, Is.EqualTo(new[] { "a", "b" }), "destination must be untouched");
    }

    // A block write covering exactly a proven value type's bytes is the type's
    // assignment: ldobj/stobj when both addresses hold that type, initobj for a
    // zeroing - verifiable IL where cpblk/initblk are not.
    private TypeAnalysisContext FixtureDecimal() =>
        _app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Decimal")
        ?? throw new InvalidOperationException("fixture mscorlib lacks System.Decimal");

    // EmitModule's placeholder carries no layout; four int fields give the test
    // struct the 16 bytes the metadata type declares.
    private static TypeDefinition DecimalDef(ModuleDefinition module, TypeAnalysisContext decimal_)
    {
        var def = decimal_.GetExtraData<TypeDefinition>("AsmResolverType")!;
        for (var i = 0; i < 4; i++)
            def.Fields.Add(new FieldDefinition($"f{i}", FieldAttributes.Public,
                module.CorLibTypeFactory.Int32));
        return def;
    }

    [Test]
    public void MemoryCopyWholeValueTypeEmitsLdobjStobj()
    {
        var decimal_ = FixtureDecimal();
        Assert.That(decimal_.IsValueType && decimal_.Definition?.Size == 16, Is.True,
            "the fixture must give System.Decimal its metadata size");

        var byref = new ByRefTypeAnalysisContext(decimal_);
        var parameters = new (TypeAnalysisContext Type, string Name)[] { (byref, "dst"), (byref, "src") };
        var caller = RunnerMethod("TypedCopy", _app.SystemTypes.SystemVoidType, parameters, out var locals);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.MemoryCopy, locals[0], locals[1], new Immediate(16)),
            new Instruction(1, OpCode.Return),
        ]);

        var module = NewModule(decimal_);
        DecimalDef(module, decimal_);
        var definition = Definition(module, "TypedCopy", _app.SystemTypes.SystemVoidType, parameters);
        var (loaded, method) = EmitAssembly(caller, definition, module);

        var il = definition.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldobj), Is.True,
            "a whole-struct copy between same-typed pointers emits ldobj");
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stobj), Is.True);
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Cpblk), Is.False,
            "a proven same-type copy must not degrade to cpblk");

        var runtimeDecimal = loaded.GetType("System.Decimal")!;
        var fields = runtimeDecimal.GetFields();
        var dst = Activator.CreateInstance(runtimeDecimal)!;
        var src = Activator.CreateInstance(runtimeDecimal)!;
        for (var i = 0; i < fields.Length; i++)
            fields[i].SetValue(src, 0x11 * (i + 1));
        object[] args = [dst, src];
        method.Invoke(null, args);
        foreach (var field in fields)
            Assert.That(field.GetValue(args[0]), Is.EqualTo(field.GetValue(args[1])),
                $"field {field.Name} must copy");
    }

    [Test]
    public void MemorySetZeroOnWholeValueTypeEmitsInitobj()
    {
        var decimal_ = FixtureDecimal();
        var byref = new ByRefTypeAnalysisContext(decimal_);
        var parameters = new (TypeAnalysisContext Type, string Name)[] { (byref, "dst") };
        var caller = RunnerMethod("TypedInit", _app.SystemTypes.SystemVoidType, parameters, out var locals);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.MemorySet, locals[0], new Immediate(0), new Immediate(16)),
            new Instruction(1, OpCode.Return),
        ]);

        var module = NewModule(decimal_);
        DecimalDef(module, decimal_);
        var definition = Definition(module, "TypedInit", _app.SystemTypes.SystemVoidType, parameters);
        var (loaded, method) = EmitAssembly(caller, definition, module);

        var il = definition.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initobj), Is.True,
            "zeroing a whole struct emits initobj");
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Initblk), Is.False);

        var runtimeDecimal = loaded.GetType("System.Decimal")!;
        var dst = Activator.CreateInstance(runtimeDecimal)!;
        foreach (var field in runtimeDecimal.GetFields())
            field.SetValue(dst, 0x77);
        object[] args = [dst];
        method.Invoke(null, args);
        foreach (var field in runtimeDecimal.GetFields())
            Assert.That(field.GetValue(args[0]), Is.EqualTo(0), $"field {field.Name} must be zeroed");
    }

    [Test]
    public void MemoryCopyValueTypeWithWrongSizeStaysRaw()
    {
        var decimal_ = FixtureDecimal();
        var byref = new ByRefTypeAnalysisContext(decimal_);
        var parameters = new (TypeAnalysisContext Type, string Name)[] { (byref, "dst"), (byref, "src") };
        var caller = RunnerMethod("PartialCopy", _app.SystemTypes.SystemVoidType, parameters, out var locals);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.MemoryCopy, locals[0], locals[1], new Immediate(8)),
            new Instruction(1, OpCode.Return),
        ]);

        var module = NewModule(decimal_);
        DecimalDef(module, decimal_);
        var definition = Definition(module, "PartialCopy", _app.SystemTypes.SystemVoidType, parameters);
        var (loaded, method) = EmitAssembly(caller, definition, module);

        var il = definition.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldobj), Is.False,
            "a count that is not exactly the type's size is not a typed assignment");
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Cpblk), Is.True);

        var runtimeDecimal = loaded.GetType("System.Decimal")!;
        var fields = runtimeDecimal.GetFields();
        var dst = Activator.CreateInstance(runtimeDecimal)!;
        var src = Activator.CreateInstance(runtimeDecimal)!;
        for (var i = 0; i < fields.Length; i++)
        {
            fields[i].SetValue(dst, 0x99 * (i + 1));
            fields[i].SetValue(src, 0x11 * (i + 1));
        }
        object[] args = [dst, src];
        method.Invoke(null, args);
        Assert.That(fields[0].GetValue(args[0]), Is.EqualTo(0x11), "first half copies");
        Assert.That(fields[1].GetValue(args[0]), Is.EqualTo(0x22), "first half copies");
        Assert.That(fields[2].GetValue(args[0]), Is.EqualTo(0x99 * 3), "second half untouched");
        Assert.That(fields[3].GetValue(args[0]), Is.EqualTo(0x99 * 4), "second half untouched");
    }

    [Test]
    public void MemoryCopyValueTypeWithDifferentSourceTypeStaysRaw()
    {
        var decimal_ = FixtureDecimal();
        var parameters = new (TypeAnalysisContext Type, string Name)[]
        {
            (new ByRefTypeAnalysisContext(decimal_), "dst"),
            (new ByRefTypeAnalysisContext(_int64), "src"),
        };
        var caller = RunnerMethod("MixedCopy", _app.SystemTypes.SystemVoidType, parameters, out var locals);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.MemoryCopy, locals[0], locals[1], new Immediate(16)),
            new Instruction(1, OpCode.Return),
        ]);

        var module = NewModule(decimal_, _int64);
        DecimalDef(module, decimal_);
        var definition = Definition(module, "MixedCopy", _app.SystemTypes.SystemVoidType, parameters);
        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldobj), Is.False,
            "source and destination of different types cannot spell a typed assignment");
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Cpblk), Is.True);
    }

    // ---------- Import naming and scalar out-parameter imports ----------

    // Any import the resolver names gets a StringLiteral target, so an unproven
    // use stays diagnosed as `Unknown call target operand: "name"` instead of an
    // anonymous address.
    [Test]
    public void ResolvedButUnhandledImportGetsNamedTarget()
    {
        var caller = CallerWithUnresolvedCall(out var call);
        BlockMemoryImportRecovery.Run(caller, va => va == 0x10000 ? "qsort" : null);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
        Assert.That(call.Operands[0], Is.TypeOf<StringLiteral>());
        Assert.That(((StringLiteral)call.Operands[0]).Value, Is.EqualTo("qsort"));
    }

    [Test]
    public void UnresolvedCallTargetStaysUnnamed()
    {
        var caller = CallerWithUnresolvedCall(out var call);
        BlockMemoryImportRecovery.Run(caller, _ => null);
        Assert.That(call.Operands[0], Is.TypeOf<Immediate>());
    }

    // A call already carrying a name (e.g. named by an earlier run) is still
    // eligible for a rewrite.
    [Test]
    public void AlreadyNamedImportStillRewrites()
    {
        var caller = CallerWithUnresolvedCall(out var call);
        call.SetOperand(0, new StringLiteral("memset"));
        call.SetOperand(3, new Immediate(0));
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memset"), Is.True);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.MemorySet));
    }

    // Inject a System.Math member into the fixture corlib (the test game's
    // mscorlib is minimal and lacks Truncate/Sin/Cos). Returns the member.
    private MethodAnalysisContext InjectMathMember(string name, TypeAnalysisContext type,
        params TypeAnalysisContext[] paramTypes)
    {
        var math = _app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Math")!;
        var member = new InjectedMethodAnalysisContext(math, name, type,
            R.MethodAttributes.Public | R.MethodAttributes.Static, paramTypes);
        math.Methods.Add(member);
        return member;
    }

    // modf(x, *iptr): the managed shape is `Math.Truncate(x)` stored through the
    // out pointer, and the result is `x - trunc(x)`.
    [Test]
    public void ModfRewritesToTruncateAndSubtract()
    {
        InjectMathMember("Truncate", _app.SystemTypes.SystemDoubleType, _app.SystemTypes.SystemDoubleType);
        var caller = CallerWithUnresolvedCall(out var call);
        var slot = new LocalVariable("iptr", new Register(null, "stack"), _app.SystemTypes.SystemDoubleType);
        caller.Locals!.Add(slot);
        call.SetOperand(2, new AddressOf(slot));

        BlockMemoryImportRecovery.Run(caller, _ => "modf");

        var instructions = caller.ControlFlowGraph!.Instructions;
        var truncate = instructions.FirstOrDefault(i =>
            i.OpCode == OpCode.Call && i.Operands[0] is MethodAnalysisContext);
        Assert.That(truncate, Is.Not.Null, "a Math.Truncate call must be inserted");
        Assert.That(((MethodAnalysisContext)truncate!.Operands[0]).Name, Is.EqualTo("Truncate"));
        Assert.That(truncate.Operands[2], Is.SameAs(call.Operands[1]),
            "Truncate's argument is the Subtract's left-hand side (x)");
        var store = instructions.FirstOrDefault(i =>
            i.OpCode == OpCode.Move && ReferenceEquals(i.Destination, slot));
        Assert.That(store, Is.Not.Null, "the out pointer's store must be inserted");
        Assert.That(store!.Operands[1], Is.SameAs(truncate.Operands[1]),
            "the stored value is Truncate's result");
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Subtract));
        Assert.That(call.Operands[2], Is.SameAs(truncate.Operands[1]));
    }

    // sincos(x, *s, *c): two managed calls and two stores; the void import's
    // own result slot drops away with the call.
    [Test]
    public void SincosRewritesToSinAndCos()
    {
        InjectMathMember("Sin", _app.SystemTypes.SystemDoubleType, _app.SystemTypes.SystemDoubleType);
        InjectMathMember("Cos", _app.SystemTypes.SystemDoubleType, _app.SystemTypes.SystemDoubleType);
        var caller = CallerWithUnresolvedCall(out var call);
        var sin = new LocalVariable("s", new Register(null, "stack"), _app.SystemTypes.SystemDoubleType);
        var cos = new LocalVariable("c", new Register(null, "stack"), _app.SystemTypes.SystemDoubleType);
        caller.Locals!.Add(sin);
        caller.Locals!.Add(cos);
        call.SetOperand(2, new AddressOf(sin));
        call.SetOperand(3, new AddressOf(cos));

        BlockMemoryImportRecovery.Run(caller, _ => "sincos");

        var instructions = caller.ControlFlowGraph!.Instructions;
        var names = instructions.Where(i => i.OpCode == OpCode.Call && i.Operands[0] is MethodAnalysisContext)
            .Select(i => ((MethodAnalysisContext)i.Operands[0]).Name).ToList();
        Assert.That(names, Is.EqualTo(new[] { "Sin", "Cos" }));
        Assert.That(instructions.Any(i => i.OpCode == OpCode.Move && ReferenceEquals(i.Destination, sin)), Is.True);
        Assert.That(instructions.Any(i => i.OpCode == OpCode.Move && ReferenceEquals(i.Destination, cos)), Is.True);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Nop));
    }

    // An out pointer that cannot be proven - an opaque integer local here -
    // keeps the call as a named diagnostic rather than emitting a raw store.
    [Test]
    public void UnprovenModfOutPointerStaysNamedCall()
    {
        var caller = CallerWithUnresolvedCall(out var call);
        call.SetOperand(2, Reg("X0", _int64)); // opaque pointer value, no provenance

        BlockMemoryImportRecovery.Run(caller, _ => "modf");

        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
        Assert.That(call.Operands[0], Is.TypeOf<StringLiteral>());
        Assert.That(((StringLiteral)call.Operands[0]).Value, Is.EqualTo("modf"));
        Assert.That(caller.ControlFlowGraph!.Instructions.Any(i =>
            i.OpCode == OpCode.Call && i.Operands[0] is MethodAnalysisContext), Is.False,
            "no managed math call may be emitted when the out pointer is unproven");
    }

    // ---------- Whole-value block ops (castle-recovery#292) ----------

    private TypeAnalysisContext ValueType(string name, params (string Name, TypeAnalysisContext Type, int Offset)[] fields)
    {
        var type = new InjectedTypeAnalysisContext(_app.AssembliesByName["mscorlib"], "Tests", name,
            _app.SystemTypes.SystemValueTypeType, R.TypeAttributes.Public | R.TypeAttributes.SequentialLayout);
        foreach (var (fieldName, fieldType, offset) in fields)
            type.Fields.Add(new InjectedFieldAnalysisContext(fieldName, fieldType, R.FieldAttributes.Public, type, offset));
        return type;
    }

    // Something in the method writes the struct temporary a copy reads (a call's
    // hidden return, here a plain move), as every real copy source has.
    private static void ProduceFirst(MethodAnalysisContext caller, LocalVariable temporary) =>
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(-1, OpCode.Move, temporary,
                new LocalVariable("produced", new Register(null, "X0", 99), temporary.Type)),
            .. caller.ControlFlowGraph!.Instructions]);

    // A class holding a 16-byte struct at 0x10 and an int right after it - the
    // PoseRecorder shape: `Last = new Pose(); Frames = 0;` is one memset over both.
    private (TypeAnalysisContext Holder, TypeAnalysisContext Pose, FieldAnalysisContext Last,
        FieldAnalysisContext First, FieldAnalysisContext Frames) Recorder()
    {
        var pose = ValueType("Pose", ("A", _int64, 0), ("B", _int64, 8));
        var holder = PodClass(("Last", pose, 0x10), ("Frames", _int32, 0x20));
        EmitModule(pose, holder);
        return (holder, pose, holder.Fields[0], pose.Fields[0], holder.Fields[1]);
    }

    [Test]
    public void MemsetOverStructAndScalarFieldsSplitsIntoTheirDefaults()
    {
        var (holder, _, last, first, frames) = Recorder();
        var caller = CallerWithUnresolvedCall(out var call);
        var owner = Reg("X19", holder, 1);
        caller.Locals!.Add(owner);
        // The resolver spells `owner + 0x10` as the first leaf there.
        call.SetOperand(2, new AddressOf(new FieldReference(first, owner, 0x10, [last])));
        call.SetOperand(3, new Immediate(0));
        call.SetOperand(4, new Immediate(0x14));

        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memset"), Is.True);

        Assert.That(call.OpCode, Is.EqualTo(OpCode.MemorySet));
        Assert.That(call.Operands[0], Is.TypeOf<AddressOf>());
        var zeroed = (FieldReference)((AddressOf)call.Operands[0]).Target;
        Assert.That(zeroed.Field, Is.SameAs(last), "the struct field is zeroed whole, not from its first leaf");
        Assert.That(zeroed.Containers, Is.Empty);
        Assert.That(call.Operands[2], Is.EqualTo(new Immediate(16)));
        var block = caller.ControlFlowGraph!.Blocks.First(b => b.Instructions.Contains(call));
        var next = block.Instructions[block.Instructions.IndexOf(call) + 1];
        Assert.That(next.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(((FieldReference)next.Operands[0]).Field, Is.SameAs(frames));
        Assert.That(next.Operands[1], Is.EqualTo(new Immediate(0)));
    }

    [Test]
    public void MemsetCuttingAFieldInHalfStaysACall()
    {
        var (holder, _, last, first, _) = Recorder();
        var caller = CallerWithUnresolvedCall(out var call);
        var owner = Reg("X19", holder, 1);
        caller.Locals!.Add(owner);
        call.SetOperand(2, new AddressOf(new FieldReference(first, owner, 0x10, [last])));
        call.SetOperand(3, new Immediate(0));
        call.SetOperand(4, new Immediate(0x12));

        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memset"), Is.False);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    [Test]
    public void MemmoveOfOneStructFieldAddressesTheWholeField()
    {
        var (holder, pose, last, first, _) = Recorder();
        var caller = CallerWithUnresolvedCall(out var call, srcType: new ByRefTypeAnalysisContext(pose));
        var owner = Reg("X19", holder, 1);
        caller.Locals!.Add(owner);
        call.SetOperand(2, new AddressOf(new FieldReference(first, owner, 0x10, [last])));
        call.SetOperand(4, new Immediate(16));

        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memmove"), Is.True);

        Assert.That(call.OpCode, Is.EqualTo(OpCode.MemoryMove));
        var copied = (FieldReference)((AddressOf)call.Operands[0]).Target;
        Assert.That(copied.Field, Is.SameAs(last));
        Assert.That(copied.Containers, Is.Empty);
    }

    // A struct holding a reference is never reference-free, but assigning it whole
    // through managed pointers to it is a typed copy, which keeps the barriers.
    [Test]
    public void WholeCopyOfStructWithReferenceRewrites()
    {
        var tagged = ValueType("Tagged", ("Name", _app.SystemTypes.SystemStringType, 0), ("Id", _int64, 8));
        EmitModule(tagged);
        var byRef = new ByRefTypeAnalysisContext(tagged);
        var caller = CallerWithUnresolvedCall(out var call, dstType: byRef, srcType: byRef);
        call.SetOperand(4, new Immediate(16));

        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.True);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.MemoryCopy));
    }

    [Test]
    public void PartialCopyOfStructWithReferenceStaysACall()
    {
        var tagged = ValueType("Tagged", ("Name", _app.SystemTypes.SystemStringType, 0), ("Id", _int64, 8));
        EmitModule(tagged);
        var byRef = new ByRefTypeAnalysisContext(tagged);
        var caller = CallerWithUnresolvedCall(out var call, dstType: byRef, srcType: byRef);
        call.SetOperand(4, new Immediate(8));

        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.False);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    [Test]
    public void WholeCopyOfStructWithReferenceEmitsLdobjStobj()
    {
        var tagged = ValueType("Tagged", ("Name", _app.SystemTypes.SystemStringType, 0), ("Id", _int64, 8));
        var byRef = new ByRefTypeAnalysisContext(tagged);
        var parameters = new (TypeAnalysisContext Type, string Name)[] { (byRef, "dst"), (byRef, "src") };
        var caller = RunnerMethod("TaggedCopy", _app.SystemTypes.SystemVoidType, parameters, out var locals);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.MemoryCopy, locals[0], locals[1], new Immediate(16)),
            new Instruction(1, OpCode.Return),
        ]);

        var module = NewModule(tagged);
        var def = tagged.GetExtraData<TypeDefinition>("AsmResolverType")!;
        def.Fields.Add(new FieldDefinition("Name", FieldAttributes.Public, module.CorLibTypeFactory.String));
        def.Fields.Add(new FieldDefinition("Id", FieldAttributes.Public, module.CorLibTypeFactory.Int64));
        var definition = Definition(module, "TaggedCopy", _app.SystemTypes.SystemVoidType, parameters);
        var (loaded, method) = EmitAssembly(caller, definition, module);

        var il = definition.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Stobj), Is.True,
            "a whole copy of a reference-holding struct is a typed assignment");
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False, "no unproven-operand diagnostic");

        var runtimeTagged = loaded.GetType("Tests.Tagged")!;
        var dst = Activator.CreateInstance(runtimeTagged)!;
        var src = Activator.CreateInstance(runtimeTagged)!;
        runtimeTagged.GetField("Name")!.SetValue(src, "castle");
        runtimeTagged.GetField("Id")!.SetValue(src, 42L);
        object[] args = [dst, src];
        method.Invoke(null, args);
        Assert.That(runtimeTagged.GetField("Name")!.GetValue(args[0]), Is.EqualTo("castle"));
        Assert.That(runtimeTagged.GetField("Id")!.GetValue(args[0]), Is.EqualTo(42L));
    }

    // `memcpy(x8, &tmp, sizeof(T))` in a method returning T through the hidden
    // buffer writes the returned value; the returned dst is that value.
    [Test]
    public void CopyIntoReturnBufferAssignsTheReturnedValue()
    {
        var wide = ValueType("Wide", ("A", _int64, 0), ("B", _int64, 8), ("C", _int64, 16));
        EmitModule(wide);
        _app.InstructionSet = new NewArmV8InstructionSet();
        var caller = new InjectedMethodAnalysisContext(_app.SystemTypes.SystemObjectType, "F", wide,
            R.MethodAttributes.Public | R.MethodAttributes.Static, [])
        {
            ParameterLocals = [],
            AnalysisWarnings = [],
        };
        var buffer = new LocalVariable("returnBuffer", new Register(null, "X8"), wide);
        var temporary = Reg("HRET_1", wide, 1);
        var result = Reg("X0", wide, 3);
        var call = new Instruction(0, OpCode.Call, new StringLiteral("memcpy"), result, buffer,
            new AddressOf(temporary), new Immediate(24), Reg("X3"), Reg("X4"));
        caller.ControlFlowGraph = new ISILControlFlowGraph([call, new Instruction(1, OpCode.Return, result)]);
        caller.Locals = [buffer, temporary, result];
        ProduceFirst(caller, temporary);

        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.True);

        Assert.That(call.OpCode, Is.EqualTo(OpCode.MemoryCopy));
        Assert.That(call.Operands[0], Is.TypeOf<AddressOf>());
        Assert.That(((AddressOf)call.Operands[0]).Target, Is.SameAs(buffer));
        var block = caller.ControlFlowGraph!.Blocks.First(b => b.Instructions.Contains(call));
        var next = block.Instructions[block.Instructions.IndexOf(call) + 1];
        Assert.That(next.OpCode, Is.EqualTo(OpCode.Move));
        Assert.That(next.Operands[0], Is.SameAs(result));
        Assert.That(next.Operands[1], Is.SameAs(buffer));
    }

    [Test]
    public void UntypedFrameSlotTakesTheCopiedStructType()
    {
        var wide = ValueType("Wide", ("A", _int64, 0), ("B", _int64, 8), ("C", _int64, 16));
        EmitModule(wide);
        var caller = CallerWithUnresolvedCall(out var call);
        var slot = new LocalVariable("slot", new Register(null, "stack_-108"), null);
        var temporary = Reg("HRET_1", wide, 1);
        caller.Locals!.AddRange([slot, temporary]);
        call.SetOperand(2, new AddressOf(slot));
        call.SetOperand(3, new AddressOf(temporary));
        call.SetOperand(4, new Immediate(24));
        ProduceFirst(caller, temporary);

        BlockMemoryImportRecovery.Run(caller, _ => "memcpy");

        Assert.That(call.OpCode, Is.EqualTo(OpCode.MemoryCopy));
        Assert.That(slot.Type, Is.SameAs(wide));
    }

    // A by-reference struct argument mapped to the wrong frame slot leaves the
    // copy reading a local nothing writes: spelling it would read unassigned bytes.
    [Test]
    public void CopyFromAnUnwrittenLocalStaysACall()
    {
        var wide = ValueType("Wide", ("A", _int64, 0), ("B", _int64, 8), ("C", _int64, 16));
        EmitModule(wide);
        var caller = CallerWithUnresolvedCall(out var call);
        var destination = Reg("HRET_2", wide, 1);
        var unwritten = new LocalVariable("unwritten", new Register(null, "stack_-150"), wide);
        caller.Locals!.AddRange([destination, unwritten]);
        call.SetOperand(2, new AddressOf(destination));
        call.SetOperand(3, new AddressOf(unwritten));
        call.SetOperand(4, new Immediate(24));

        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memcpy"), Is.False);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
    }

    // Struct temporaries copied slot to slot type from the one slot whose type is
    // known, whichever order the copies come in.
    [Test]
    public void ChainOfFrameSlotCopiesTypesFromOneAnchor()
    {
        var wide = ValueType("Wide", ("A", _int64, 0), ("B", _int64, 8), ("C", _int64, 16));
        EmitModule(wide);
        var caller = CallerWithUnresolvedCall(out var first);
        var outer = new LocalVariable("outer", new Register(null, "stack_-200"), null);
        var inner = new LocalVariable("inner", new Register(null, "stack_-100"), null);
        var temporary = Reg("HRET_1", wide, 1);
        caller.Locals!.AddRange([outer, inner, temporary]);
        first.SetOperand(2, new AddressOf(outer));
        first.SetOperand(3, new AddressOf(inner));
        first.SetOperand(4, new Immediate(24));
        var second = new Instruction(1, OpCode.Call, new Immediate(0x10000), Reg("X0", version: 2),
            new AddressOf(inner), new AddressOf(temporary), new Immediate(24), Reg("X3"), Reg("X4"));
        var rest = caller.ControlFlowGraph!.Instructions.ToList();
        caller.ControlFlowGraph = new ISILControlFlowGraph([rest[0], second, .. rest.Skip(1)]);
        ProduceFirst(caller, temporary);

        BlockMemoryImportRecovery.Run(caller, _ => "memcpy");

        Assert.That(inner.Type, Is.SameAs(wide));
        Assert.That(outer.Type, Is.SameAs(wide));
        Assert.That(first.OpCode, Is.EqualTo(OpCode.MemoryCopy));
        Assert.That(second.OpCode, Is.EqualTo(OpCode.MemoryCopy));
    }

    [Test]
    public void FrameSlotOverlappingAnotherLocalIsNotRetyped()
    {
        var wide = ValueType("Wide", ("A", _int64, 0), ("B", _int64, 8), ("C", _int64, 16));
        EmitModule(wide);
        var caller = CallerWithUnresolvedCall(out var call);
        var slot = new LocalVariable("slot", new Register(null, "stack_-108"), null);
        var inside = new LocalVariable("inside", new Register(null, "stack_-100"), _int64);
        var temporary = Reg("HRET_1", wide, 1);
        caller.Locals!.AddRange([slot, inside, temporary]);
        call.SetOperand(2, new AddressOf(slot));
        call.SetOperand(3, new AddressOf(temporary));
        call.SetOperand(4, new Immediate(24));
        ProduceFirst(caller, temporary);

        BlockMemoryImportRecovery.Run(caller, _ => "memcpy");

        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));
        Assert.That(slot.Type, Is.Null, "a slot whose bytes have a second name stays untyped");
    }

    // A frame slot typed by its first field (an int here) is not the whole struct
    // the native copy writes: initblk/cpblk over it would run past the local.
    [Test]
    public void BlockOpLongerThanTheLocalStaysACall()
    {
        var caller = CallerWithUnresolvedCall(out var call);
        var slot = new LocalVariable("slot", new Register(null, "stack_-48"), _int32);
        caller.Locals!.Add(slot);
        call.SetOperand(2, new AddressOf(slot));
        call.SetOperand(3, new Immediate(0));
        call.SetOperand(4, new Immediate(72));

        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memset"), Is.False);
        Assert.That(call.OpCode, Is.EqualTo(OpCode.Call));

        call.SetOperand(4, new Immediate(4));
        Assert.That(BlockMemoryImportRecovery.TryRewriteCall(caller, call, "memset"), Is.True,
            "a fill inside the local's own bytes is still a block op");
    }

    // In SSA a memcpy result nothing reads is dead; it gets its own local so later
    // copy coalescing cannot merge it into a live register's local.
    [Test]
    public void NameImportsNamesTheImportAndDetachesADeadResult()
    {
        var caller = CallerWithUnresolvedCall(out var call);
        var result = call.Operands[1];

        BlockMemoryImportRecovery.NameImports(caller, va => va == 0x10000 ? "memcpy" : null);

        Assert.That(call.Operands[0], Is.EqualTo(new StringLiteral("memcpy")));
        Assert.That(call.Operands[1], Is.Not.SameAs(result));
        Assert.That(caller.Locals, Does.Contain(call.Operands[1]));
    }

    [Test]
    public void NameImportsKeepsAReadResult()
    {
        var caller = CallerWithUnresolvedCall(out var call, resultUsed: true);
        var result = call.Operands[1];

        BlockMemoryImportRecovery.NameImports(caller, va => va == 0x10000 ? "memcpy" : null);

        Assert.That(call.Operands[0], Is.EqualTo(new StringLiteral("memcpy")));
        Assert.That(call.Operands[1], Is.SameAs(result));
    }

    // castle-recovery#306: a by-value struct wider than 16 bytes arrives as the
    // address of the caller's copy, so the parameter's register is a pointer; as a
    // block-op operand it is the parameter's own storage.
    [Test]
    public void WideStructParameterIsItsOwnStorageInABlockCopy()
    {
        var wide = ValueType("Wide", ("A", _int64, 0), ("B", _int64, 8), ("C", _int64, 16));
        EmitModule(wide);
        var caller = CallerWithUnresolvedCall(out var call);
        var parameter = new LocalVariable("adInfo", new Register(null, "X1"), wide);
        var copy = Reg("HRET_2", wide, 1);
        caller.Locals!.AddRange([parameter, copy]);
        caller.ParameterLocals = [parameter];
        call.SetOperand(2, new AddressOf(copy));
        call.SetOperand(3, parameter);
        call.SetOperand(4, new Immediate(24));

        BlockMemoryImportRecovery.Run(caller, _ => "memcpy");

        Assert.That(call.OpCode, Is.EqualTo(OpCode.MemoryCopy));
        Assert.That(call.Operands[1], Is.TypeOf<AddressOf>());
        Assert.That(((AddressOf)call.Operands[1]).Target, Is.SameAs(parameter));
    }

    // The address of a parameter is its argument slot (ldarga), not the shadow
    // local every ISIL local also gets.
    [Test]
    public void AddressOfParameterEmitsLdarga()
    {
        var decimal_ = FixtureDecimal();
        var parameters = new (TypeAnalysisContext Type, string Name)[] { (decimal_, "value") };
        var caller = RunnerMethod("ZeroParam", _app.SystemTypes.SystemVoidType, parameters, out var locals);
        caller.ControlFlowGraph = new ISILControlFlowGraph([
            new Instruction(0, OpCode.MemorySet, new AddressOf(locals[0]), new Immediate(0), new Immediate(16)),
            new Instruction(1, OpCode.Return),
        ]);

        var module = NewModule(decimal_);
        DecimalDef(module, decimal_);
        var definition = Definition(module, "ZeroParam", _app.SystemTypes.SystemVoidType, parameters);
        IlGenerator.GenerateIl(caller, definition);

        var il = definition.CilMethodBody!.Instructions;
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldarga || i.OpCode == CilOpCodes.Ldarga_S), Is.True,
            () => string.Join("\n", il.Select(i => i.ToString())));
        Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldloca || i.OpCode == CilOpCodes.Ldloca_S), Is.False);
    }
}
