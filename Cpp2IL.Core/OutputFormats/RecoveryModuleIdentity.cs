using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Text;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Builder;
using Cpp2IL.Core.Model.Contexts;
using LibCpp2IL;

namespace Cpp2IL.Core.OutputFormats;

internal static class RecoveryModuleIdentity
{
    internal static void Assign(ModuleDefinition module, string buildIdentity)
    {
        var bytes = Digest(["cpp2il-recovery-mvid-v1", buildIdentity, module.Name?.ToString() ?? "",
            module.Assembly?.FullName ?? ""]);
        var guid = new byte[16];
        Array.Copy(bytes, guid, guid.Length);
        module.Mvid = new Guid(guid);
    }

    internal static string CaptureInputs(byte[] binary, byte[] metadata)
    {
        using var sha = SHA256.Create();
        return Convert.ToBase64String(Digest([Convert.ToBase64String(sha.ComputeHash(binary)),
            Convert.ToBase64String(sha.ComputeHash(metadata))]));
    }

    internal static string ForBuild(ApplicationAnalysisContext context, AsmResolverDllOutputFormatIlRecovery format)
    {
        var options = Cpp2IlApi.RuntimeOptions;
        var parts = new List<string> { "cpp2il-recovery-inputs-v1", context.RecoveryInputIdentity,
            context.UnityVersion.ToString(), format.OutputFormatId, BuildId(typeof(RecoveryModuleIdentity)), BuildId(format.GetType()),
            BuildId(typeof(Il2CppBinary)), BuildId(context.InstructionSet.GetType()),
            BuildId(typeof(ManagedPEImageBuilder)), BuildId(typeof(ModuleDefinition)),
            options?.LowMemoryMode.ToString() ?? "unspecified" };
        // Preserve processor order; dictionary insertion order is not an option.
        if (options != null)
        {
            parts.Add("processors"); parts.Add(options.ProcessingLayersToRun.Count.ToString(System.Globalization.CultureInfo.InvariantCulture));
            foreach (var layer in options.ProcessingLayersToRun)
            {
                parts.Add(layer.Id); parts.Add(BuildId(layer.GetType()));
            }
            parts.Add("configuration"); parts.Add(options.ProcessingLayerConfigurationOptions.Count.ToString(System.Globalization.CultureInfo.InvariantCulture));
            foreach (var option in options.ProcessingLayerConfigurationOptions.OrderBy(x => x.Key, StringComparer.Ordinal))
            {
                parts.Add(option.Key); parts.Add(option.Value);
            }
            if (options.WasmFrameworkJsFile is { } wasm)
            {
                using var sha = SHA256.Create();
                parts.Add("wasm-framework");
                parts.Add(Convert.ToBase64String(sha.ComputeHash(File.ReadAllBytes(wasm))));
            }
        }
        return Convert.ToBase64String(Digest(parts));
    }

    private static string BuildId(Type type)
        => type.FullName + ":" + type.Assembly.FullName + ":" + type.Module.ModuleVersionId;

    private static byte[] Digest(IEnumerable<string> parts)
    {
        using var stream = new MemoryStream();
        using (var writer = new BinaryWriter(stream, Encoding.UTF8, true))
            foreach (var part in parts) writer.Write(part); // Length-prefixed; no concatenation ambiguity.
        using var sha = SHA256.Create();
        return sha.ComputeHash(stream.ToArray());
    }
}
