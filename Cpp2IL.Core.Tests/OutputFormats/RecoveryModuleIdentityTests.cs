using System.IO;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Builder;
using AsmResolver.PE.Builder;
using Cpp2IL.Core.OutputFormats;

namespace Cpp2IL.Core.Tests.OutputFormats;

public class RecoveryModuleIdentityTests
{
    [Test]
    public void InputFingerprintIncludesBothBinaryAndMetadata()
    {
        var original = RecoveryModuleIdentity.CaptureInputs([1, 2], [3, 4]);
        Assert.That(original, Is.EqualTo(RecoveryModuleIdentity.CaptureInputs([1, 2], [3, 4])));
        Assert.That(original, Is.Not.EqualTo(RecoveryModuleIdentity.CaptureInputs([1, 5], [3, 4])));
        Assert.That(original, Is.Not.EqualTo(RecoveryModuleIdentity.CaptureInputs([1, 2], [3, 5])));
        Assert.That(original, Is.Not.EqualTo(RecoveryModuleIdentity.CaptureInputs([1], [2, 3, 4])));
    }

    private static byte[] Emit(string input, string assembly)
    {
        var module = new ModuleDefinition(assembly);
        RecoveryModuleIdentity.Assign(module, input);
        using var stream = new MemoryStream();
        new ManagedPEFileBuilder().CreateFile(module.ToPEImage(new ManagedPEImageBuilder())).Write(stream);
        return stream.ToArray();
    }

    [Test]
    public void SameImmutableIdentityProducesIdenticalPeBytes()
    {
        var first = Emit("input-a", "a.dll");
        var second = Emit("input-a", "a.dll");
        Assert.That(first, Is.EqualTo(second));
    }

    [Test]
    public void ChangedInputCannotReuseModuleIdentity()
    {
        var a = new ModuleDefinition("a.dll"); var b = new ModuleDefinition("a.dll");
        RecoveryModuleIdentity.Assign(a, "input-a"); RecoveryModuleIdentity.Assign(b, "input-b");
        Assert.That(a.Mvid, Is.Not.EqualTo(b.Mvid));
    }

    [Test]
    public void ChangedAssemblyCannotReuseModuleIdentity()
    {
        var a = new ModuleDefinition("a.dll"); var b = new ModuleDefinition("b.dll");
        RecoveryModuleIdentity.Assign(a, "input-a"); RecoveryModuleIdentity.Assign(b, "input-a");
        Assert.That(a.Mvid, Is.Not.EqualTo(b.Mvid));
    }
}
