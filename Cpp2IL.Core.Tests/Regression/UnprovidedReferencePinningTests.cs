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
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.OutputFormats;
using NUnit.Framework;
using R = System.Reflection;

namespace Cpp2IL.Core.Tests.Regression;

// castle-recovery#195: the IL-recovery output format must not special-case a
// game. Two pins: no member on the type may fabricate an AsmResolver
// AssemblyReference - a hard-coded assembly name ends up as a real AssemblyRef
// row in every emitted module, and the compile pipeline reports CS0246 for a
// binary no provider ships - and a method the lifter cannot recover keeps its
// named "unresolved" note plus the declared minimal stub, never a hand-written
// fill.
public class UnprovidedReferencePinningTests
{
    // Reaches the output format's protected body-fill seam so a test can observe
    // the same recovery sidecar entry (`<dll>.recovery.json`) the r241 baselines
    // aggregate into status counts.
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

    // A context with a declared name/signature but no native bytes - the shape
    // an unliftable method presents to FillMethodBody.
    private sealed class NamedMethodAnalysisContext(
        TypeAnalysisContext parent, string name, TypeAnalysisContext returnType)
        : MethodAnalysisContext(null, parent)
    {
        public override string DefaultName => name;
        public override R.MethodAttributes DefaultAttributes => R.MethodAttributes.Static;
        public override TypeAnalysisContext DefaultReturnType => returnType;
        public override ulong UnderlyingPointer => 0;
    }

    [Test]
    public void RecoveryFormatConstructsNoAssemblyReference()
    {
        // Any helper that builds an AsmResolver AssemblyReference injects a
        // name into the emitted module's reference table with no assembly
        // providing it - the failure mode this test pins against returning.
        // Fails while any member on the type constructs one.
        var offenders = typeof(AsmResolverDllOutputFormatIlRecovery)
            .GetMethods(R.BindingFlags.Static | R.BindingFlags.Instance
                | R.BindingFlags.Public | R.BindingFlags.NonPublic)
            .Where(ConstructsAssemblyReference)
            .Select(method => method.Name)
            .ToList();

        Assert.That(offenders, Is.Empty,
            "the recovery format must not fabricate assembly references: " +
            "every AssemblyRef row must name an assembly a provider ships");
    }

    private static bool ConstructsAssemblyReference(R.MethodInfo method)
    {
        var il = method.GetMethodBody()?.GetILAsByteArray();
        if (il == null)
            return false;
        for (var i = 0; i + 4 < il.Length; i++)
            if (il[i] == 0x73 // newobj
                && ResolveToken(method, BitConverter.ToInt32(il, i + 1)) is R.ConstructorInfo ctor
                && ctor.DeclaringType == typeof(AssemblyReference))
                return true;
        return false;
    }

    private static R.MemberInfo? ResolveToken(R.MethodInfo method, int token)
    {
        try
        {
            return method.Module.ResolveMember(token);
        }
        catch (Exception)
        {
            return null;
        }
    }

    [Test]
    public void UnliftedMethodKeepsUnresolvedNoteAndDeclaredStub()
    {
        // A method whose analysis lifts no instructions is diagnosed
        // "unresolved" and keeps the declared minimal stub - the named note the
        // pipeline counts - instead of a fabricated body.
        Cpp2IlApi.ResetInternalState();
        var app = TestGameLoader.LoadSimple2022Game();

        var (module, type) = NewSyntheticModule("FixtureGame.dll");
        var method = NewMethod(type, module, "UnliftedMethod", module.CorLibTypeFactory.Int32);
        var parent = new InjectedTypeAnalysisContext(app.AssembliesByName["UnityEngine.CoreModule"],
            "Tests", "Holder", app.SystemTypes.SystemObjectType, R.TypeAttributes.Public);
        var context = new NamedMethodAnalysisContext(parent, "UnliftedMethod",
            app.SystemTypes.SystemInt32Type);

        var entry = new RecoveryStatusProbe().EmitAndReadEvidence(module, method, context);
        TestContext.Out.WriteLine($"status={entry.GetProperty("Native").GetProperty("Status").GetString()} " +
            $"body0={method.CilMethodBody!.Instructions[0].Operand}");

        Assert.Multiple(() =>
        {
            Assert.That(entry.GetProperty("Native").GetProperty("Status").GetString(),
                Is.EqualTo("unresolved"));
            var opcodes = method.CilMethodBody!.Instructions.Select(i => i.OpCode.Code).ToArray();
            Assert.That(opcodes, Is.EqualTo(new[] { CilCode.Ldc_I4_0, CilCode.Ret }),
                "an unlifted method keeps the declared minimal stub under its named note");

            var provided = app.AssembliesByName.Keys
                .Append(module.Assembly!.Name!.ToString())
                .ToHashSet();
            var unprovided = module.AssemblyReferences
                .Select(reference => reference.Name?.ToString())
                .Where(name => name != null && !provided.Contains(name))
                .ToList();
            Assert.That(unprovided, Is.Empty,
                "filling a body must not add an assembly reference nothing provides");
        });
    }
}
