using System;
using System.IO;
using System.Linq;
using System.Text.Json;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.OutputFormats;
using Cpp2IL.Core.Utils.AsmResolver;
using NUnit.Framework;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// Fixtures for the open r241 recovery clusters pinned in docs/RECOVERY_CLUSTERS.md
// ("Open clusters (pinned)"). Each test asserts the explicit diagnostic the
// pipeline emits today; when the cluster is fixed the named assertion flips and
// the test must be updated with the new expectation.
public class OpenClusterPinningTests
{
    // Reaches the output format's protected body-fill seam so a test can observe
    // the same recovery sidecar entry (`<dll>.recovery.json`) the r241 baselines
    // aggregate into `stub:*` / `lifter:*` cluster keys.
    private sealed class RecoveryStatusProbe : AsmResolverDllOutputFormatIlRecovery
    {
        public JsonElement EmitAndReadEvidence(ModuleDefinition module, MethodDefinition method,
            MethodAnalysisContext context)
        {
            var path = Path.Combine(Path.GetTempPath(), Guid.NewGuid() + ".dll");
            try
            {
                FillMethodBody(method, context);
                module.Write(path);
                OnAssemblyWritten(context.AppContext, path);
                var doc = JsonDocument.Parse(File.ReadAllText(path + ".recovery.json"));
                return doc.RootElement.GetProperty("Methods").EnumerateArray()
                    .Single(e => e.GetProperty("Signature").GetString() == method.FullName).Clone();
            }
            finally
            {
                File.Delete(path);
                if (File.Exists(path + ".recovery.json"))
                    File.Delete(path + ".recovery.json");
            }
        }
    }

    private static (ModuleDefinition module, TypeDefinition type) NewSyntheticModule(string name)
    {
        var module = new ModuleDefinition(name);
        var assembly = new AssemblyDefinition(name[..^".dll".Length], new Version(1, 0));
        assembly.Modules.Add(module);
        var type = new TypeDefinition("Tests", "Fixture", TypeAttributes.Public,
            module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(type);
        return (module, type);
    }

    private static MethodDefinition NewMethod(TypeDefinition type, ModuleDefinition module,
        string name, TypeSignature returnType)
    {
        var method = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static,
            MethodSignature.CreateStatic(returnType));
        type.Methods.Add(method);
        return method;
    }

    [Test]
    public void FrameworkModuleMethodIsMarkedIntentionalStub()
    {
        // Cluster stub:intentional-stub (99,048 r241 methods): a method context
        // emitted into a framework-named module is diagnosed "intentional-stub"
        // and receives the declared minimal stub, never silently rewritten into
        // recovered-looking IL. This assertion flips when the cluster is fixed.
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();

        var (module, type) = NewSyntheticModule("UnityEngine.FixtureModule.dll");
        var method = NewMethod(type, module, "FixtureMethod", module.CorLibTypeFactory.Int32);
        var parent = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Holder", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var context = new MethodAnalysisContext(null, parent);

        var entry = new RecoveryStatusProbe().EmitAndReadEvidence(module, method, context);

        Assert.That(entry.GetProperty("Native").GetProperty("Status").GetString(),
            Is.EqualTo("intentional-stub"));
        var opcodes = method.CilMethodBody!.Instructions.Select(i => i.OpCode.Code).ToArray();
        Assert.That(opcodes, Is.EqualTo(new[] { CilCode.Ldc_I4_0, CilCode.Ret }),
            "intentional stubs must stay the declared default body, not fabricated IL");
    }

    [Test]
    public void InjectedMethodIsMarkedInjectedStub()
    {
        // Cluster stub:injected-stub (732 r241 methods): an injected method context
        // is diagnosed "injected-stub" instead of being filled with a fabricated
        // body. This assertion flips when the cluster is fixed.
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();

        var (module, type) = NewSyntheticModule("FixtureGame.dll");
        var method = NewMethod(type, module, "InjectedMethod", module.CorLibTypeFactory.Void);
        var parent = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Holder", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var context = new InjectedMethodAnalysisContext(parent, "InjectedMethod",
            app.SystemTypes.SystemVoidType, R.MethodAttributes.Static, []);

        var entry = new RecoveryStatusProbe().EmitAndReadEvidence(module, method, context);

        Assert.That(entry.GetProperty("Native").GetProperty("Status").GetString(),
            Is.EqualTo("injected-stub"));
        var opcodes = method.CilMethodBody!.Instructions.Select(i => i.OpCode.Code).ToArray();
        Assert.That(opcodes, Is.EqualTo(new[] { CilCode.Ret }),
            "injected stubs must stay the declared minimal body, not fabricated IL");
    }

    [Test]
    public void ReturnValueDroppedByVoidSignatureLeavesStackInvalidDiagnosed()
    {
        // Cluster ilverify:StackUnexpected (885 r241 methods): the recovered
        // context produced a return value but the emitted signature is void, so
        // `ret` is reached with a value still on the stack. The body stays
        // stack-invalid and is explicitly diagnosed, never swapped for a clean
        // default body. These assertions flip when the cluster is fixed.
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();

        var (module, type) = NewSyntheticModule("FixtureGame.dll");
        var method = NewMethod(type, module, "DivergentReturn", module.CorLibTypeFactory.Void);
        var parent = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Holder", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var context = new InjectedMethodAnalysisContext(parent, "DivergentReturn",
            app.SystemTypes.SystemInt32Type, R.MethodAttributes.Static, []);
        var result = new LocalVariable("result", new Register(null, "result"))
            { Type = app.SystemTypes.SystemInt32Type };
        context.ControlFlowGraph = new ISILControlFlowGraph([
            new(0, OpCode.Move, result, new Immediate(7)),
            new(1, OpCode.Return, null, result),
        ]);
        context.Locals = [result];
        context.ParameterLocals = [];
        context.AnalysisWarnings = [];
        SyntheticFixture.SeedCorLibTypes(app, module,
            app.SystemTypes.SystemInt32Type, app.SystemTypes.SystemVoidType);

        IlGenerator.GenerateIl(context, method);

        Assert.That(context.AnalysisWarnings.Any(w => w.Contains("Invalid reconstructed IL stack")),
            Is.True, "a body the stack verifier rejects must be marked, not silently emitted");
        Assert.That(method.CilMethodBody!.Instructions[^1].OpCode, Is.EqualTo(CilOpCodes.Throw),
            "the invalid body is preserved under an explicit diagnostic trailer");
        Assert.That(method.CilMethodBody.Instructions.Select(i => i.OpCode.Code),
            Is.Not.EqualTo(new[] { CilCode.Ldc_I4, CilCode.Ret }),
            "never a silent default body");
    }
}
