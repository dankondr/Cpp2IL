using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Metadata.Tables;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// castle-recovery#289: `box V; castclass C` and `unbox.any V` from a reference
// typed C throw InvalidCastException on every execution when C can never hold a
// boxed V (any class but Object/ValueType, Enum for a non-enum, an interface V
// does not implement). Such a coercion is refused and the slot takes the
// diagnosed default; legal boxing (Object, implemented interface, enum -> Enum,
// Nullable) and unboxing keep their emission.
public class ImpossibleBoxCoercionTests
{
    private const string Refused = "No legal conversion from";

    [TestCase("System.Int32", "System.String", true)]
    [TestCase("System.Int32", "System.Enum", true)]
    [TestCase("System.IntPtr", "System.Enum", true)]
    [TestCase("System.Int32", "System.IDisposable", true)]
    [TestCase("System.String", "System.Int32", true)]
    [TestCase("System.Int32", "System.Object", false)]
    [TestCase("System.Int32", "System.ValueType", false)]
    [TestCase("System.Int32", "System.IComparable", false)]
    [TestCase("System.DayOfWeek", "System.Enum", false)]
    [TestCase("System.Object", "System.Int32", false)]
    [TestCase("System.IComparable", "System.Int32", false)]
    [TestCase("System.Nullable`1", "System.String", false)]
    public void MoveAcrossBoxBoundary(string source, string destination, bool refused)
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var mscorlib = app.AssembliesByName["mscorlib"];
        TypeAnalysisContext Resolve(string name) => name == "System.Nullable`1"
            ? mscorlib.GetTypeByFullName(name)!.MakeGenericInstanceType([app.SystemTypes.SystemInt32Type])
            : mscorlib.GetTypeByFullName(name)!;
        var sourceType = Resolve(source);
        var destinationType = Resolve(destination);
        var from = new LocalVariable("from", new Register(null, "from")) { Type = sourceType };
        var module = new ModuleDefinition("ImpossibleBox.dll");
        var sourceDefinition = sourceType is GenericInstanceTypeAnalysisContext generic ? generic.GenericType : sourceType;
        SeedCorLibTypes(app, module, sourceDefinition, app.SystemTypes.SystemInt32Type,
            destinationType, app.SystemTypes.SystemVoidType);
        // `return from;` in a method returning `destination`: the return slot's
        // contract is the coercion target.
        var callerType = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "BoxCaller", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public | R.TypeAttributes.Class);
        var caller = new InjectedMethodAnalysisContext(callerType, "Run", destinationType,
            R.MethodAttributes.Public | R.MethodAttributes.Static, [sourceType], ["from"]);
        caller.ControlFlowGraph = new ISILControlFlowGraph([new(0, OpCode.Return, from)]);
        caller.Locals = [from];
        caller.ParameterLocals = [from];
        caller.AnalysisWarnings = [];
        var owner = new TypeDefinition("Tests", "BoxCaller", TypeAttributes.Public | TypeAttributes.Class,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(owner);
        var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(module.CorLibTypeFactory.Object, [module.CorLibTypeFactory.Object]));
        method.ParameterDefinitions.Add(new ParameterDefinition(1, "from", 0));
        owner.Methods.Add(method);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var listing = string.Join("\n", il.Select(i => i.ToString()));
        var crossed = il.Any(i => i.OpCode == CilOpCodes.Box || i.OpCode == CilOpCodes.Unbox_Any);
        var notes = il.Where(i => i.OpCode == CilOpCodes.Ldstr).Select(i => (string)i.Operand!).ToList();
        Assert.Multiple(() =>
        {
            Assert.That(crossed, Is.EqualTo(!refused), listing);
            Assert.That(notes.Any(n => n.Contains(Refused)), Is.EqualTo(refused), listing);
            if (refused)
                Assert.That(il.Any(i => i.OpCode == CilOpCodes.Castclass), Is.False, listing);
        });
    }
    // The ISIL Box op (il2cpp_value_box) casts the boxed value to its store
    // contract; a contract that can never hold it is refused the same way.
    [TestCase("System.String", true)]
    [TestCase("System.IComparable", false)]
    [TestCase("System.Object", false)]
    public void BoxOpIntoSlot(string destination, bool refused)
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var int32 = app.SystemTypes.SystemInt32Type;
        var destinationType = app.AssembliesByName["mscorlib"].GetTypeByFullName(destination)!;
        var source = new LocalVariable("source", new Register(null, "source")) { Type = int32 };
        var boxed = new LocalVariable("boxed", new Register(null, "boxed")) { Type = destinationType };
        var module = new ModuleDefinition("BoxOp.dll");
        SeedCorLibTypes(app, module, int32, destinationType, app.SystemTypes.SystemVoidType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, source, new Immediate(3)),
            new(1, OpCode.Box, boxed, int32, source),
            new(2, OpCode.Return)], [source, boxed]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        var listing = string.Join("\n", il.Select(i => i.ToString()));
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Box), Is.True, listing);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Castclass), Is.False, listing);
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr && ((string)i.Operand!).Contains(Refused)),
                Is.EqualTo(refused), listing);
        });
    }
}
