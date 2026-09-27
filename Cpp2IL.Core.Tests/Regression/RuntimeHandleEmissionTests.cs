using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using R = System.Reflection;
using static Cpp2IL.Core.Tests.Regression.SyntheticFixture;

namespace Cpp2IL.Core.Tests.Regression;

// Recovery cluster: IL emission — handle-typed destinations and function pointers
// (#40, 5b117115). A RuntimeMethodInfo on a .ctor is a delegate-ctor target, which
// is a native pointer slot, but ldftn cannot name a .ctor — the honest emission is
// the native-int zero placeholder. Handle contexts (RuntimeClass/RuntimeMethodInfo/
// friends) lower to System.IntPtr slots, never to handle-typed locals.
public class RuntimeHandleEmissionTests
{
    [Test]
    public void ConstructorMethodInfoDoesNotEmitLdftn()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var allocatedType = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Widget", app.SystemTypes.SystemObjectType,
            R.TypeAttributes.Public | R.TypeAttributes.Class);
        var ctor = allocatedType.InjectMethodContext(".ctor", app.SystemTypes.SystemVoidType,
            R.MethodAttributes.Public | R.MethodAttributes.HideBySig
                | R.MethodAttributes.SpecialName | R.MethodAttributes.RTSpecialName);
        var methodInfo = new RuntimeMethodInfoAnalysisContext(ctor, allocatedType.DeclaringAssembly);
        var slot = new LocalVariable("slot", new Register(null, "slot"))
            { Type = app.SystemTypes.SystemIntPtrType };
        var module = new ModuleDefinition("CtorHandle.dll");
        SeedCorLibTypes(app, module, app.SystemTypes.SystemIntPtrType,
            app.SystemTypes.SystemVoidType, app.SystemTypes.SystemObjectType);
        var (caller, method) = ForeignCaller(app, module, [
            new(0, OpCode.Move, slot, methodInfo),
            new(1, OpCode.Return)], [slot]);

        IlGenerator.GenerateIl(caller, method);

        var il = method.CilMethodBody!.Instructions;
        Assert.Multiple(() =>
        {
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Ldftn), Is.False,
                () => string.Join("\n", il.Select(i => i.ToString())));
            Assert.That(il.Any(i => i.OpCode == CilOpCodes.Conv_I), Is.True,
                "the .ctor handle slot keeps its native-int zero placeholder");
        });
    }

    [Test]
    public void HandleTypedLocalReportsIntPtrContract()
    {
        Cpp2IlApi.ResetInternalState();
        TestGameLoader.LoadSimple2019Game();
        var app = Cpp2IlApi.CurrentAppContext!;
        var runtimeClass = new RuntimeClassTypeAnalysisContext(app.SystemTypes.SystemStringType,
            app.AssembliesByName["UnityEngine.CoreModule"]);
        var methodInfo = new RuntimeMethodInfoAnalysisContext(
            new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
                "Tests", "Widget", app.SystemTypes.SystemObjectType,
                R.TypeAttributes.Public | R.TypeAttributes.Class)
                .InjectMethodContext("Run", app.SystemTypes.SystemVoidType,
                    R.MethodAttributes.Public | R.MethodAttributes.Static),
            app.AssembliesByName["UnityEngine.CoreModule"]);
        var module = new ModuleDefinition("HandleLocal.dll");
        var (caller, _) = ForeignCaller(app, module, [new(0, OpCode.Return)], [
            new LocalVariable("klass", new Register(null, "klass")) { Type = runtimeClass },
            new LocalVariable("fn", new Register(null, "fn")) { Type = methodInfo }]);
        var klass = caller.Locals[0];
        var fn = caller.Locals[1];

        Assert.Multiple(() =>
        {
            // Handle-typed locals must report the emitted native-int contract to every
            // consumer of the slot (moves, call results, stores) — not the analysis type.
            Assert.That(IlGenerator.EmittedOperandType(klass, caller)?.FullName,
                Is.EqualTo("System.IntPtr"));
            Assert.That(IlGenerator.EmittedOperandType(fn, caller)?.FullName,
                Is.EqualTo("System.IntPtr"));
        });
    }
}
