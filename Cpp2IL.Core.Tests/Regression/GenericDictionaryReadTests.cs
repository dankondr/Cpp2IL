using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: stale hidden-slot methodinfo binding (castle-recovery#262).
// A shared stub that is not in MethodsByAddress falls back to the MethodInfo*
// operand in the hidden-argument slot. When that operand is a stale leftover
// from a sibling call, the locals sitting in the callee's argument slots carry
// the wrong types: a value-type key slot holding a proven reference-type local
// cannot be TryGetValue's key, so the bind is refused and the raw target
// address stays unresolved. When the slot shapes match, the bind is what lets
// the dictionary's TValue seed the out cell — the value a later typed use sees.
public class GenericDictionaryReadTests
{
    private static (TypeAnalysisContext key, TypeAnalysisContext value,
        GenericInstanceTypeAnalysisContext dict, MethodAnalysisContext concrete)
        DictionaryFixture(ApplicationAnalysisContext app)
    {
        var key = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "Tests", "GridPos", app.SystemTypes.SystemValueTypeType,
            R.TypeAttributes.Public | R.TypeAttributes.Sealed | R.TypeAttributes.SequentialLayout);
        var value = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"],
            "Tests", "Shield", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var dictDefinition = app.AssembliesByName["mscorlib"]
            .GetTypeByFullName("System.Collections.Generic.Dictionary`2")!;
        var tryGetValue = dictDefinition.Methods.Single(m => m.Name == "TryGetValue");
        var dict = new GenericInstanceTypeAnalysisContext(dictDefinition, [key, value]);
        var concrete = new ConcreteGenericMethodAnalysisContext(tryGetValue, [key, value], []);
        return (key, value, dict, concrete);
    }

    private static InjectedMethodAnalysisContext Caller(ApplicationAnalysisContext app,
        List<Instruction> instructions, List<LocalVariable> locals)
    {
        var ownerType = new InjectedTypeAnalysisContext(app.AssembliesByName["mscorlib"], "Tests",
            "Owner", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var caller = ownerType.InjectMethodContext("Run", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.Static);
        caller.ControlFlowGraph = new ISILControlFlowGraph(instructions);
        caller.Locals = locals;
        caller.ParameterLocals = [];
        caller.AnalysisWarnings = [];
        return caller;
    }

    // Lifted bl shape for an instance callee with two parameters:
    // [target, dest, receiver, key, &out, hidden MethodInfo*].
    private static (Instruction call, List<LocalVariable> locals, LocalVariable outCell)
        LiftedTryGetCall(ApplicationAnalysisContext app, MethodAnalysisContext concrete,
            TypeAnalysisContext dictType, TypeAnalysisContext keyOperandType)
    {
        var dest = new LocalVariable("dest", new Register(null, "dest"));
        var receiver = new LocalVariable("recv", new Register(null, "recv")) { Type = dictType };
        var key = new LocalVariable("key", new Register(null, "key")) { Type = keyOperandType };
        var outCell = new LocalVariable("cell", new Register(null, "cell"));
        var methodInfo = new RuntimeMethodInfoAnalysisContext(concrete,
            concrete.DeclaringType!.DeclaringAssembly!);
        var call = new Instruction(1, OpCode.Call, new Immediate(0x4000), dest,
            receiver, key, new AddressOf(outCell), methodInfo);
        return (call, [dest, receiver, key, outCell], outCell);
    }

    [Test]
    public void StaleMethodInfoArgumentTypeMismatchStaysUnresolved()
    {
        // The methodinfo says Dictionary<GridPos, Shield>.TryGetValue but the
        // key slot holds a proven string local: the register carried a stale
        // methodinfo and the bind is refused, keeping the target diagnosed.
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var (_, _, dict, concrete) = DictionaryFixture(app);
        var (call, locals, _) = LiftedTryGetCall(app, concrete, dict,
            app.SystemTypes.SystemStringType);
        var caller = Caller(app, [new(0, OpCode.Nop), call, new(2, OpCode.Return)], locals);

        MetadataResolver.ResolveCallsViaMethodInfo(caller);

        Assert.That(call.Operands[0], Is.TypeOf<Immediate>(),
            () => call.Operands[0]?.ToString() ?? "<null>");
    }

    [Test]
    public void GenericDictionaryOutValueSeedsTheAddressedCell()
    {
        // A consistent shape binds, and the bound concrete instantiation is
        // what lets the out cell take TValue: the read value is typed for the
        // consumer instead of staying an unknown object.
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2019Game();
        var (key, value, dict, concrete) = DictionaryFixture(app);
        var (call, locals, outCell) = LiftedTryGetCall(app, concrete, dict, key);
        var caller = Caller(app, [new(0, OpCode.Nop), call, new(2, OpCode.Return)], locals);

        MetadataResolver.ResolveCallsViaMethodInfo(caller);
        Assert.That(call.Operands[0], Is.SameAs(concrete),
            () => call.Operands[0]?.ToString() ?? "<null>");

        LocalVariables.ResolveTypesAndFields(caller);

        Assert.That(outCell.Type, Is.SameAs(value),
            () => $"out cell took {outCell.Type?.FullName ?? "<null>"} instead of the TValue");
    }
}
