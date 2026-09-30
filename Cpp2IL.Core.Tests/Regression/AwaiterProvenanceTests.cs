using System.Linq;
using AsmResolver.DotNet;
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
// (Index < 0) move writes a whole SSA variable, so a literal zero into a
// value-type local is its all-zero default, emitted with no diagnostic; the
// same literal in a real lifted store keeps its named note.
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

    [Test]
    public void SyntheticMoveZeroIntoWideValueTypeEmitsDefaultWithoutNote()
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
            Assert.That(il.All(instruction =>
                    instruction.Operand?.ToString()?.Contains("No legal conversion") != true
                    && instruction.Operand?.ToString()?.Contains("NoteDecompilerIssue") != true),
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
