using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: IL emission — awaiter provenance (castle-recovery#174).
// An erased awaiter local (`TaskAwaiter<object>`) is re-emitted at the
// instantiation the binary's own call metadata proves: an `&local` receiver on
// an instance call demands the callee's declaring type, and an `&local` under
// a byref parameter demands the parameter's element type. A pass-inserted
// (Index < 0) move carries the one register it covers: a literal zero into a
// register-sized value-type local is its all-zero default, emitted with no
// diagnostic; the same literal into a wider value type, or in a real lifted
// store, keeps a named note.
public class AwaiterProvenanceTests
{
    private static GenericInstanceTypeAnalysisContext Awaiter(ApplicationAnalysisContext app,
        TypeAnalysisContext argument)
    {
        var taskAwaiter = app.AssembliesByName["mscorlib"]
            .GetTypeByFullName("System.Runtime.CompilerServices.TaskAwaiter`1")!;
        return new GenericInstanceTypeAnalysisContext(taskAwaiter, [argument]);
    }

    private static TypeDefinition SeedAwaiterDefinition(TypeAnalysisContext taskAwaiter)
    {
        var definition = new TypeDefinition("System.Runtime.CompilerServices", "TaskAwaiter`1",
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            null);
        definition.GenericParameters.Add(new GenericParameter("T"));
        taskAwaiter.PutExtraData("AsmResolverType", definition);
        return definition;
    }

    [Test]
    public void ErasedAwaiterLocalEmitsAtByrefReceiverInstantiation()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var erased = Awaiter(app, app.SystemTypes.SystemObjectType);
        var getResult = erased.GenericType.Methods.Single(method =>
            method.Name == "GetResult" && !method.IsStatic);
        var concreteCall = new ConcreteGenericMethodAnalysisContext(getResult,
            [app.SystemTypes.SystemStringType], []);
        var awaiter = new LocalVariable("awaiter", new Register(null, "awaiter")) { Type = erased };
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemStringType };
        var (caller, method) = ForeignCaller(app, new ModuleDefinition("AwaiterProvenance.dll"), [
            new(0, OpCode.Call, concreteCall, result, new AddressOf(awaiter)),
            new(1, OpCode.Return)], [awaiter, result]);
        SeedCorLibTypes(app, method.DeclaringModule!, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemStringType,
            app.SystemTypes.SystemValueTypeType);
        method.DeclaringModule!.TopLevelTypes.Add(SeedAwaiterDefinition(erased.GenericType));

        IlGenerator.GenerateIl(caller, method);

        Assert.Multiple(() =>
        {
            Assert.That(method.CilMethodBody!.LocalVariables.Any(local =>
                    local.VariableType?.FullName?.Contains("TaskAwaiter`1<System.String>") == true),
                Is.True, () => string.Join("\n", method.CilMethodBody!.LocalVariables));
            Assert.That(method.CilMethodBody!.LocalVariables.All(local =>
                    local.VariableType?.FullName?.Contains("TaskAwaiter`1<System.Object>") != true),
                Is.True, () => string.Join("\n", method.CilMethodBody!.LocalVariables));
        });
    }

    [Test]
    public void ErasedAwaiterLocalEmitsAtByrefParameterInstantiation()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var erased = Awaiter(app, app.SystemTypes.SystemObjectType);
        var interlocked = app.AssembliesByName["mscorlib"]
            .GetTypeByFullName("System.Threading.Interlocked")!;
        var compareExchange = interlocked.Methods.Single(candidate =>
            candidate.Name == "CompareExchange" && candidate.GenericParameters.Count == 1
            && candidate.Parameters.Count == 3);
        var concrete = Awaiter(app, app.SystemTypes.SystemStringType);
        var concreteCall = new ConcreteGenericMethodAnalysisContext(compareExchange, [], [concrete]);
        var awaiter = new LocalVariable("awaiter", new Register(null, "awaiter")) { Type = erased };
        var result = new LocalVariable("result", new Register(null, "result")) { Type = concrete };
        var (caller, method) = ForeignCaller(app, new ModuleDefinition("AwaiterProvenance.dll"), [
            new(0, OpCode.Call, concreteCall, result, new AddressOf(awaiter), awaiter, awaiter),
            new(1, OpCode.Return)], [awaiter, result]);
        SeedCorLibTypes(app, method.DeclaringModule!, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemStringType,
            app.SystemTypes.SystemValueTypeType);
        method.DeclaringModule!.TopLevelTypes.Add(SeedAwaiterDefinition(erased.GenericType));

        IlGenerator.GenerateIl(caller, method);

        Assert.Multiple(() =>
        {
            Assert.That(method.CilMethodBody!.LocalVariables.Any(local =>
                    local.VariableType?.FullName?.Contains("TaskAwaiter`1<System.String>") == true),
                Is.True, () => string.Join("\n", method.CilMethodBody!.LocalVariables));
            Assert.That(method.CilMethodBody!.LocalVariables.All(local =>
                    local.VariableType?.FullName?.Contains("TaskAwaiter`1<System.Object>") != true),
                Is.True, () => string.Join("\n", method.CilMethodBody!.LocalVariables));
        });
    }

    // A call lifted with its generic argument already erased
    // (`Probe<TaskAwaiter<object>>`) re-instantiates at the awaiter's proven
    // type once binary evidence sharpens the `&awaiter` operand - the erased
    // argument is a placeholder, not a contract.
    [Test]
    public void ErasedCallInstantiationResolvesFromProvenAwaiterArgument()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var erased = Awaiter(app, app.SystemTypes.SystemObjectType);
        var getResult = erased.GenericType.Methods.Single(method =>
            method.Name == "GetResult" && !method.IsStatic);
        var concreteGetResult = new ConcreteGenericMethodAnalysisContext(getResult,
            [app.SystemTypes.SystemStringType], []);
        var empty = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Array")!
            .Methods.Single(method => method.Name == "Empty" && method.GenericParameters.Count == 1);
        var byRefParameter = new ByRefTypeAnalysisContext(empty.GenericParameters[0]);
        empty.Parameters.Add(new InjectedParameterAnalysisContext("awaiter", byRefParameter,
            System.Reflection.ParameterAttributes.None, 0, empty));
        var erasedCall = new ConcreteGenericMethodAnalysisContext(empty, [], [erased]);
        var awaiter = new LocalVariable("awaiter", new Register(null, "awaiter")) { Type = erased };
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemStringType };
        var array = new LocalVariable("array", new Register(null, "array"))
            { Type = app.SystemTypes.SystemObjectType };
        var (caller, method) = ForeignCaller(app, new ModuleDefinition("AwaiterProvenance.dll"), [
            new(0, OpCode.Call, concreteGetResult, result, new AddressOf(awaiter)),
            new(1, OpCode.Call, erasedCall, array, new AddressOf(awaiter)),
            new(2, OpCode.Return)], [awaiter, result, array]);
        SeedCorLibTypes(app, method.DeclaringModule!, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemStringType,
            app.SystemTypes.SystemValueTypeType);
        method.DeclaringModule!.TopLevelTypes.Add(SeedAwaiterDefinition(erased.GenericType));
        var arrayDefinition = new TypeDefinition("System", "Array",
            TypeAttributes.Public | TypeAttributes.Class, null);
        empty.DeclaringType!.PutExtraData("AsmResolverType", arrayDefinition);
        method.DeclaringModule!.TopLevelTypes.Add(arrayDefinition);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(instruction =>
                    instruction.Operand?.ToString()?.Contains("Empty") == true
                    && instruction.Operand.ToString()!.Contains("TaskAwaiter`1<System.String>")),
                Is.True, () => string.Join("\n", il));
            Assert.That(il.All(instruction =>
                    instruction.Operand?.ToString()?.Contains("Empty") != true
                    || instruction.Operand.ToString()!.Contains("TaskAwaiter`1<System.Object>") != true),
                Is.True, () => string.Join("\n", il));
            Assert.That(il.All(instruction =>
                    instruction.Operand?.ToString()?.Contains("No legal conversion") != true),
                Is.True, () => string.Join("\n", il));
        });
    }

    // A pass-inserted phi-edge Move carries one register's all-zero value: for a
    // slot whose unboxed size fits that register (DateTime, 8 bytes) the edge
    // proves default(T) - initobj with no diagnostic.
    [Test]
    public void PassInsertedMoveZeroIntoRegisterSizedValueTypeEmitsDefaultWithoutNote()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var dateTimeType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.DateTime")!;
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = dateTimeType };
        var (caller, method) = ForeignCaller(app, new ModuleDefinition("AwaiterProvenance.dll"), [
            new(-1, OpCode.Move, slot, new Immediate(0)),
            new(1, OpCode.Return)], [slot]);
        SeedCorLibTypes(app, method.DeclaringModule!, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemValueTypeType, dateTimeType);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(instruction => instruction.OpCode == CilOpCodes.Initobj),
                Is.True, () => string.Join("\n", il));
            Assert.That(il.All(instruction =>
                    instruction.Operand?.ToString()?.Contains("No legal conversion") != true
                    && instruction.Operand?.ToString()?.Contains("NoteDecompilerIssue") != true),
                Is.True, () => string.Join("\n", il));
        });
    }

    // The coverage is the named register's storage, not a flat pointer width:
    // a phi-edge zero on a V register covers all 128 bits, so the same
    // 16-byte Decimal that stays diagnosed on an X register is proven on V.
    [Test]
    public void PassInsertedMoveZeroIntoVectorRegisterCoversWholeStruct()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var decimalType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Decimal")!;
        var slot = new LocalVariable("slot", new Register(null, "V8")) { Type = decimalType };
        var (caller, method) = ForeignCaller(app, new ModuleDefinition("AwaiterProvenance.dll"), [
            new(-1, OpCode.Move, slot, new Immediate(0)),
            new(1, OpCode.Return)], [slot]);
        SeedCorLibTypes(app, method.DeclaringModule!, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemValueTypeType, decimalType);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(instruction => instruction.OpCode == CilOpCodes.Initobj),
                Is.True, () => string.Join("\n", il));
            Assert.That(il.All(instruction =>
                    instruction.Operand?.ToString()?.Contains("covers one register") != true
                    && instruction.Operand?.ToString()?.Contains("NoteDecompilerIssue") != true),
                Is.True, () => string.Join("\n", il));
        });
    }

    // The same pass-inserted zero into a wider value type (Decimal, 16 bytes)
    // proves only the register it covers: default(T) is still the best value,
    // but it is an implicit fill and stays diagnosed.
    [Test]
    public void PassInsertedMoveZeroIntoWideValueTypeKeepsDecompilerNote()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var decimalType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Decimal")!;
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = decimalType };
        var (caller, method) = ForeignCaller(app, new ModuleDefinition("AwaiterProvenance.dll"), [
            new(-1, OpCode.Move, slot, new Immediate(0)),
            new(1, OpCode.Return)], [slot]);
        SeedCorLibTypes(app, method.DeclaringModule!, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemValueTypeType, decimalType);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(instruction => instruction.OpCode == CilOpCodes.Initobj),
                Is.True, () => string.Join("\n", il));
            Assert.That(il.Any(instruction =>
                    instruction.Operand?.ToString()?.Contains("covers one register") == true),
                Is.True, () => string.Join("\n", il));
        });
    }

    // An awaitable local moved into an awaiter-typed slot is the source's own
    // awaiter-producing call inlined to a bit copy: where the awaitable type
    // declares a usable instance producer (GetAwaiter, or DisposeAsync for an
    // `await using` disposable) returning exactly the nested slot type, the
    // emitted IL is the real call - `ldloca awaitable; call Producer` - not a
    // synthetic default (castle-recovery#191).
    [TestCase("GetAwaiter")]
    [TestCase("DisposeAsync")]
    public void AwaitableLocalIntoAwaiterSlotEmitsAwaiterProducerCall(string producerName)
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var awaitable = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Awaitable", app.SystemTypes.SystemValueTypeType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Sealed
                | System.Reflection.TypeAttributes.SequentialLayout);
        var contract = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Awaitable+Awaiter", app.SystemTypes.SystemValueTypeType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Sealed
                | System.Reflection.TypeAttributes.SequentialLayout)
            { DeclaringType = awaitable };
        var getAwaiter = awaitable.InjectMethodContext(producerName, contract,
            System.Reflection.MethodAttributes.Public);
        var producerThis = new LocalVariable("this", new Register(null, "X0"), awaitable) { IsThis = true };
        var producerOut = new LocalVariable("returnBuffer", new Register(null, "X8"), contract);
        getAwaiter.ConvertedIsil =
        [
            new Instruction(0, OpCode.Move, new MemoryOperand(producerOut), producerThis),
            new Instruction(1, OpCode.Return, producerOut),
        ];
        var source = new LocalVariable("awaitable", new Register(null, "awaitable")) { Type = awaitable };
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = contract };
        var (caller, method) = ForeignCaller(app, new ModuleDefinition("AwaiterProvenance.dll"), [
            new(0, OpCode.Move, slot, source),
            new(1, OpCode.Return)], [source, slot]);
        var module = method.DeclaringModule!;
        SeedCorLibTypes(app, module, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemStringType,
            app.SystemTypes.SystemValueTypeType);
        var awaitableDefinition = new TypeDefinition("Tests", "Awaitable",
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        var awaiterDefinition = new TypeDefinition("Tests", "Awaiter",
            TypeAttributes.NestedPublic | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        awaitableDefinition.NestedTypes.Add(awaiterDefinition);
        var getAwaiterDefinition = new MethodDefinition(producerName, MethodAttributes.Public,
            MethodSignature.CreateInstance(awaiterDefinition.ToTypeSignature()));
        awaitableDefinition.Methods.Add(getAwaiterDefinition);
        awaitable.PutExtraData("AsmResolverType", awaitableDefinition);
        contract.PutExtraData("AsmResolverType", awaiterDefinition);
        getAwaiter.PutExtraData("AsmResolverMethod", getAwaiterDefinition);
        module.TopLevelTypes.Add(awaitableDefinition);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(instruction =>
                    instruction.OpCode == CilOpCodes.Call
                    && instruction.Operand?.ToString()?.Contains(producerName) == true),
                Is.True, () => string.Join("\n", il));
            Assert.That(il.Any(instruction => instruction.OpCode == CilOpCodes.Ldloca
                    || instruction.OpCode == CilOpCodes.Ldloca_S),
                Is.True, () => string.Join("\n", il));
            Assert.That(il.All(instruction =>
                    instruction.Operand?.ToString()?.Contains("No legal conversion") != true
                    && instruction.Operand?.ToString()?.Contains("NoteDecompilerIssue") != true),
                Is.True, () => string.Join("\n", il));
        });
    }

    // A producer whose lifted body is not the bit copy - it calls out - does
    // not prove the conversion: a bit move reproduces none of that side
    // effect, so the site keeps its named default.
    [Test]
    public void AwaitableLocalIntoAwaiterSlotKeepsNoteWhenProducerBodyHasCall()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var awaitable = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Awaitable", app.SystemTypes.SystemValueTypeType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Sealed
                | System.Reflection.TypeAttributes.SequentialLayout);
        var contract = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Awaitable+Awaiter", app.SystemTypes.SystemValueTypeType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Sealed
                | System.Reflection.TypeAttributes.SequentialLayout)
            { DeclaringType = awaitable };
        var getAwaiter = awaitable.InjectMethodContext("GetAwaiter", contract,
            System.Reflection.MethodAttributes.Public);
        var producerOut = new LocalVariable("returnBuffer", new Register(null, "X8"), contract);
        getAwaiter.ConvertedIsil =
        [
            new Instruction(0, OpCode.Call, new LocalVariable("target", new Register(null, "X0"))),
            new Instruction(1, OpCode.Return, producerOut),
        ];
        var source = new LocalVariable("awaitable", new Register(null, "awaitable")) { Type = awaitable };
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = contract };
        var (caller, method) = ForeignCaller(app, new ModuleDefinition("AwaiterProvenance.dll"), [
            new(0, OpCode.Move, slot, source),
            new(1, OpCode.Return)], [source, slot]);
        var module = method.DeclaringModule!;
        SeedCorLibTypes(app, module, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemStringType,
            app.SystemTypes.SystemValueTypeType);
        var awaitableDefinition = new TypeDefinition("Tests", "Awaitable",
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        var awaiterDefinition = new TypeDefinition("Tests", "Awaiter",
            TypeAttributes.NestedPublic | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        awaitableDefinition.NestedTypes.Add(awaiterDefinition);
        var getAwaiterDefinition = new MethodDefinition("GetAwaiter", MethodAttributes.Public,
            MethodSignature.CreateInstance(awaiterDefinition.ToTypeSignature()));
        awaitableDefinition.Methods.Add(getAwaiterDefinition);
        awaitable.PutExtraData("AsmResolverType", awaitableDefinition);
        contract.PutExtraData("AsmResolverType", awaiterDefinition);
        getAwaiter.PutExtraData("AsmResolverMethod", getAwaiterDefinition);
        module.TopLevelTypes.Add(awaitableDefinition);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(instruction =>
                    instruction.Operand?.ToString()?.Contains("No legal conversion") == true),
                Is.True, () => string.Join("\n", il));
            Assert.That(il.Any(instruction => instruction.OpCode == CilOpCodes.Initobj),
                Is.True, () => string.Join("\n", il));
        });
    }

    // The same move stays diagnosed when no producer on the operand's type
    // returns the slot's awaiter type: the binary proves nothing about how the
    // awaiter value was formed, so the slot keeps its named default.
    [Test]
    public void AwaitableLocalIntoForeignAwaiterSlotKeepsDecompilerNote()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var awaitable = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Awaitable", app.SystemTypes.SystemValueTypeType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Sealed
                | System.Reflection.TypeAttributes.SequentialLayout);
        var contract = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Awaitable+Awaiter", app.SystemTypes.SystemValueTypeType,
            System.Reflection.TypeAttributes.Public | System.Reflection.TypeAttributes.Sealed
                | System.Reflection.TypeAttributes.SequentialLayout)
            { DeclaringType = awaitable };
        awaitable.InjectMethodContext("GetAwaiter", Awaiter(app, app.SystemTypes.SystemStringType),
            System.Reflection.MethodAttributes.Public);
        var source = new LocalVariable("awaitable", new Register(null, "awaitable")) { Type = awaitable };
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = contract };
        var (caller, method) = ForeignCaller(app, new ModuleDefinition("AwaiterProvenance.dll"), [
            new(0, OpCode.Move, slot, source),
            new(1, OpCode.Return)], [source, slot]);
        var module = method.DeclaringModule!;
        SeedCorLibTypes(app, module, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemObjectType, app.SystemTypes.SystemStringType,
            app.SystemTypes.SystemValueTypeType);
        var awaitableDefinition = new TypeDefinition("Tests", "Awaitable",
            TypeAttributes.Public | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        var awaiterDefinition = new TypeDefinition("Tests", "Awaiter",
            TypeAttributes.NestedPublic | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            module.CorLibTypeFactory.CorLibScope.CreateTypeReference("System", "ValueType"));
        awaitableDefinition.NestedTypes.Add(awaiterDefinition);
        awaitable.PutExtraData("AsmResolverType", awaitableDefinition);
        contract.PutExtraData("AsmResolverType", awaiterDefinition);
        module.TopLevelTypes.Add(awaitableDefinition);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(instruction =>
                    instruction.Operand?.ToString()?.Contains("No legal conversion") == true),
                Is.True, () => string.Join("\n", il));
            Assert.That(il.Any(instruction => instruction.OpCode == CilOpCodes.Initobj),
                Is.True, () => string.Join("\n", il));
        });
    }

    // An unproven zero keeps its named diagnostic: a real lifted store of
    // literal 0 covers less than the slot's width, so nothing in the binary
    // proves the rest of the value was cleared.
    [Test]
    public void LiftedMoveZeroIntoWideValueTypeKeepsDecompilerNote()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2022Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var decimalType = app.AssembliesByName["mscorlib"].GetTypeByFullName("System.Decimal")!;
        var slot = new LocalVariable("slot", new Register(null, "slot")) { Type = decimalType };
        var (caller, method) = ForeignCaller(app, new ModuleDefinition("AwaiterProvenance.dll"), [
            new(0, OpCode.Move, slot, new Immediate(0)),
            new(1, OpCode.Return)], [slot]);
        SeedCorLibTypes(app, method.DeclaringModule!, app.SystemTypes.SystemVoidType,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemValueTypeType, decimalType);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(instruction =>
                    instruction.Operand?.ToString()?.Contains("No legal conversion") == true),
                Is.True, () => string.Join("\n", il));
            Assert.That(il.Any(instruction => instruction.OpCode == CilOpCodes.Initobj),
                Is.True, () => string.Join("\n", il));
        });
    }
}
