using System;
using System.Collections.Generic;
using System.IO;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using Cpp2IL.Core.OutputFormats;

namespace Cpp2IL.Core.Tests;

public class RecoveryManifestTests
{
    [Test]
    public void ManifestIsDeterministicBoundToBytesAndDoesNotRewriteIl()
    {
        var module = new ModuleDefinition("ManifestFixture.dll");
        var assembly = new AssemblyDefinition("ManifestFixture", new Version(1,0)); assembly.Modules.Add(module);
        var type = new TypeDefinition("Tests", "Fixture", TypeAttributes.Public, module.CorLibTypeFactory.Object.Type); module.TopLevelTypes.Add(type);
        var method = new MethodDefinition("One", MethodAttributes.Public | MethodAttributes.Static, MethodSignature.CreateStatic(module.CorLibTypeFactory.Int32)); type.Methods.Add(method);
        method.CilMethodBody = new CilMethodBody();
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldsfld, new MemberReference(module.CorLibTypeFactory.Int32.Type, "FixtureField", new FieldSignature(module.CorLibTypeFactory.Int32)));
        method.CilMethodBody.Instructions.Add(CilOpCodes.Pop);
        method.CilMethodBody.Instructions.Add(CilOpCodes.Ldc_I4_1); method.CilMethodBody.Instructions.Add(CilOpCodes.Ret);
        var path = Path.Combine(Path.GetTempPath(), Guid.NewGuid()+".dll"); module.Write(path);
        try
        {
            var before = File.ReadAllBytes(path);
            var evidence = new Dictionary<string, RecoveryNativeInfo> { [module.Name+":"+method.FullName] = new("0x1234", "fixture-hash", "lifted-unverified") };
            var manifest = RecoveryManifest.Inspect(path,evidence);
            Assert.That(manifest.Methods[0].ComputedMaxStack, Is.EqualTo(1));
            Assert.That(manifest.Methods[0].Native!.Address, Is.EqualTo("0x1234"));
            Assert.That(manifest.Methods[0].VerificationStatus, Is.EqualTo("unverified"));
            Assert.That(manifest.Methods[0].Calls, Is.Empty, "field MemberReferences are not method calls");
            Assert.That(RecoveryManifest.Serialize(manifest), Is.EqualTo(RecoveryManifest.Serialize(RecoveryManifest.Inspect(path,evidence))));
            Assert.That(File.ReadAllBytes(path), Is.EqualTo(before));
        }
        finally { File.Delete(path); }
    }
}
