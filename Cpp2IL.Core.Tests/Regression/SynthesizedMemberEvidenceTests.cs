using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.OutputFormats;

namespace Cpp2IL.Core.Tests.Regression;

// castle-recovery#76 — a method emitted without an il2cpp method context
// (bare-allocation constructors, restored attribute accessors, framework-
// surface helpers) has no native body, so the sidecar must record an explicit
// reason instead of a missing Native row.
public class SynthesizedMemberEvidenceTests
{
    [Test]
    public void NestedTypeMethodWithoutLiftEvidenceGetsExplicitReasonRow()
    {
        var module = new ModuleDefinition("SynthesizedFixture.dll");
        var assembly = new AssemblyDefinition("SynthesizedFixture", new Version(1, 0));
        assembly.Modules.Add(module);
        var outer = new TypeDefinition("Tests", "Outer", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type);
        module.TopLevelTypes.Add(outer);
        var nested = new TypeDefinition("Tests", "Inner", TypeAttributes.NestedPublic, module.CorLibTypeFactory.Object.Type);
        outer.NestedTypes.Add(nested);

        // A nested-type member backed by a real method context keeps its lift row.
        var lifted = new MethodDefinition("Lifted", MethodAttributes.Public, MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        lifted.CilMethodBody = new CilMethodBody();
        lifted.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        nested.Methods.Add(lifted);

        // A member synthesized at emit time (no analysis context) must still get
        // a row - one that says there is no native body.
        var synthesized = new MethodDefinition(".ctor", MethodAttributes.Public | MethodAttributes.SpecialName | MethodAttributes.RuntimeSpecialName,
            MethodSignature.CreateInstance(module.CorLibTypeFactory.Void));
        synthesized.CilMethodBody = new CilMethodBody();
        synthesized.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        nested.Methods.Add(synthesized);

        var path = Path.Combine(Path.GetTempPath(), Guid.NewGuid() + ".dll");
        module.Write(path);
        try
        {
            var evidence = new Dictionary<string, RecoveryNativeInfo>
            {
                [module.Name + ":" + lifted.FullName] = new("0x1234", "fixture-hash", "lifted-unverified"),
            };
            var manifest = RecoveryManifest.Inspect(path, evidence);

            var liftedRow = manifest.Methods.Single(m => m.Signature == lifted.FullName);
            Assert.That(liftedRow.Native!.Address, Is.EqualTo("0x1234"),
                "a nested type's method with a native body must keep its lift row and address");
            Assert.That(liftedRow.Native.Status, Is.EqualTo("lifted-unverified"));

            var synthesizedRow = manifest.Methods.Single(m => m.Signature == synthesized.FullName);
            Assert.That(synthesizedRow.Native, Is.Not.Null,
                "an emitted method without a native body must carry an explicit reason row");
            Assert.That(synthesizedRow.Native!.Status, Is.EqualTo("injected-stub"));
            Assert.That(synthesizedRow.Native.Address, Is.Null);
            Assert.That(synthesizedRow.Native.Sha256, Is.Null);
        }
        finally
        {
            File.Delete(path);
        }
    }
}
