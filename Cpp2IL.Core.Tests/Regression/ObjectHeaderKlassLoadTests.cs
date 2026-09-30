using System.Collections.Generic;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Analysis;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: unmanaged loads of the object header's klass word (+0)
// whose only consumers are exact-type tests. `Move v, [obj]` reads the klass
// pointer; when it reaches only `CheckEqual`/`CheckNotEqual` against a provable
// type value (a `typeof(T)` operand, a `Move v, typeof(T)` local, or another
// object's klass load), the compare is `obj.GetType() == typeof(T)` /
// `a.GetType() == b.GetType()` and the load folds into it. Every other
// consumer keeps the unmanaged-load diagnostic.
public class ObjectHeaderKlassLoadTests
{
    private static string Emit(IEnumerable<CilInstruction> il) => string.Join("\n", il.Select(i => i.ToString()));

    private static (MethodAnalysisContext caller, MethodDefinition method) Setup(
        ApplicationAnalysisContext app, ModuleDefinition module,
        List<Instruction> instructions, List<LocalVariable> locals, List<LocalVariable> parameters,
        TypeAnalysisContext? returnType = null)
    {
        var (caller, method) = ForeignCaller(app, module, instructions, locals, returnType);
        caller.ParameterLocals = parameters;
        caller.DominatorInfo = new DominatorInfo(caller.ControlFlowGraph!);
        return (caller, method);
    }

    [Test]
    public void KlassLoadComparedToTypeEmitsGetTypeCheck()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("KlassTypeTest.dll");
        var boolean = app.SystemTypes.SystemBooleanType;
        var stringType = app.SystemTypes.SystemStringType;
        SeedCorLibTypes(app, module, stringType, boolean, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemIntPtrType);

        // klass = [obj]; cond = klass == typeof(string) - the klass load's only
        // use is the exact-type test, so the compare is obj.GetType() == typeof(string).
        var obj = new LocalVariable("obj", new Register(null, "obj")) { Type = app.SystemTypes.SystemObjectType };
        var klass = new LocalVariable("klass", new Register(null, "klass"))
            { Type = new RuntimeClassTypeAnalysisContext(stringType, stringType.DeclaringAssembly) };
        var cond = new LocalVariable("cond", new Register(null, "cond")) { Type = boolean };
        var (caller, method) = Setup(app, module, [
            new(0, OpCode.Move, klass, new MemoryOperand(obj)),
            new(1, OpCode.CheckEqual, cond, klass, stringType),
            new(2, OpCode.Return, cond)], [obj, klass, cond], [obj], boolean);

        KlassLoadTypeTestRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Callvirt
                    && i.Operand is IMethodDescriptor m && m.Name == "GetType"), Is.EqualTo(1),
                () => Emit(il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldtoken), Is.True, () => Emit(il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ceq), Is.True, () => Emit(il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False, () => Emit(il));
        });
    }

    [Test]
    public void KlassLoadComparedToKlassLoadEmitsGetTypePair()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("KlassIdentity.dll");
        var boolean = app.SystemTypes.SystemBooleanType;
        var stringType = app.SystemTypes.SystemStringType;
        SeedCorLibTypes(app, module, stringType, boolean, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemIntPtrType);

        // ka = [a]; kb = [b]; cond = ka == kb - both sides are klass reads, so
        // the compare is a.GetType() == b.GetType().
        var a = new LocalVariable("a", new Register(null, "a")) { Type = app.SystemTypes.SystemObjectType };
        var b = new LocalVariable("b", new Register(null, "b")) { Type = app.SystemTypes.SystemObjectType };
        var klassA = new LocalVariable("klassA", new Register(null, "klassA"))
            { Type = new RuntimeClassTypeAnalysisContext(stringType, stringType.DeclaringAssembly) };
        var klassB = new LocalVariable("klassB", new Register(null, "klassB"))
            { Type = new RuntimeClassTypeAnalysisContext(stringType, stringType.DeclaringAssembly) };
        var cond = new LocalVariable("cond", new Register(null, "cond")) { Type = boolean };
        var (caller, method) = Setup(app, module, [
            new(0, OpCode.Move, klassA, new MemoryOperand(a)),
            new(1, OpCode.Move, klassB, new MemoryOperand(b)),
            new(2, OpCode.CheckEqual, cond, klassA, klassB),
            new(3, OpCode.Return, cond)], [a, b, klassA, klassB, cond], [a, b], boolean);

        KlassLoadTypeTestRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Count(i => i.OpCode == CilOpCodes.Callvirt
                    && i.Operand is IMethodDescriptor m && m.Name == "GetType"), Is.EqualTo(2),
                () => Emit(il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ceq), Is.True, () => Emit(il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr), Is.False, () => Emit(il));
        });
    }

    [Test]
    public void KlassLoadWithNonTypeTestUseKeepsDiagnostic()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var module = new ModuleDefinition("KlassUnproven.dll");
        var boolean = app.SystemTypes.SystemBooleanType;
        var stringType = app.SystemTypes.SystemStringType;
        SeedCorLibTypes(app, module, stringType, boolean, app.SystemTypes.SystemInt32Type,
            app.SystemTypes.SystemIntPtrType);

        // klass = [obj]; cond = klass == 0 - comparing the klass pointer to a
        // literal is not a managed type test, so the load keeps its diagnostic.
        var obj = new LocalVariable("obj", new Register(null, "obj")) { Type = app.SystemTypes.SystemObjectType };
        var klass = new LocalVariable("klass", new Register(null, "klass"))
            { Type = new RuntimeClassTypeAnalysisContext(stringType, stringType.DeclaringAssembly) };
        var cond = new LocalVariable("cond", new Register(null, "cond")) { Type = boolean };
        var (caller, method) = Setup(app, module, [
            new(0, OpCode.Move, klass, new MemoryOperand(obj)),
            new(1, OpCode.CheckEqual, cond, klass, new Immediate(0)),
            new(2, OpCode.Return, cond)], [obj, klass, cond], [obj], boolean);

        KlassLoadTypeTestRecovery.Run(caller);
        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldstr
                    && i.Operand is string s && s.StartsWith("Unmanaged memory load")), Is.True,
                () => Emit(il));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Callvirt
                    && i.Operand is IMethodDescriptor m && m.Name == "GetType"), Is.False,
                () => Emit(il));
        });
    }
}
