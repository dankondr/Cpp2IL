using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Text.Json;
using System.Text.Json.Serialization;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;

namespace Cpp2IL.Core.OutputFormats;

internal record RecoveryNativeInfo(string? Address, string? Sha256, string Status);
internal record RecoveryMethodInfo(string Token, string Signature, RecoveryNativeInfo? Native, string[] Diagnostics,
    string[] Calls, int? DeclaredMaxStack, int? ComputedMaxStack, string? StackFailure, string VerificationStatus);
internal record RecoveryAssemblyManifest(int SchemaVersion, string Assembly, string AssemblySha256, string ToolVersion, RecoveryMethodInfo[] Methods);

[JsonSerializable(typeof(RecoveryAssemblyManifest))]
[JsonSourceGenerationOptions(WriteIndented = true)]
internal partial class RecoveryJsonContext : JsonSerializerContext { }

internal static class RecoveryManifest
{
    internal static string Hash(byte[] bytes)
    {
        using var sha = SHA256.Create();
        return BitConverter.ToString(sha.ComputeHash(bytes)).Replace("-", "").ToLowerInvariant();
    }

    internal static RecoveryAssemblyManifest Inspect(string path, IReadOnlyDictionary<string, RecoveryNativeInfo> evidence)
    {
        var module = ModuleDefinition.FromFile(path);
        var methods = module.GetAllTypes().SelectMany(t => t.Methods).OrderBy(m => m.MetadataToken.ToUInt32()).Select(m =>
        {
            var body = m.CilMethodBody;
            int? computed = null;
            string? failure = null;
            if (body != null)
            {
                try { computed = body.ComputeMaxStack(); }
                catch (Exception e) { failure = e.GetType().Name + ": " + e.Message; }
            }
            var diagnostics = body?.Instructions.Select((i, n) => (i, n))
                .Where(p => p.i.Operand is IMethodDescriptor target && target.DeclaringType?.FullName == "Cpp2ILInjected.Cpp2ILHelpers" && target.Name == "NoteDecompilerIssue")
                .Select(p => p.n > 0 && body.Instructions[p.n - 1].OpCode == CilOpCodes.Ldstr ? (string)body.Instructions[p.n - 1].Operand! : "NoteDecompilerIssue without literal")
                .ToArray() ?? [];
            var calls = body?.Instructions.Where(i => i.OpCode.Code is CilCode.Call or CilCode.Callvirt or CilCode.Newobj or CilCode.Ldftn or CilCode.Ldvirtftn or CilCode.Jmp)
                .Select(i => i.Operand).OfType<IMethodDescriptor>().Select(c => c.FullName).Distinct().OrderBy(s => s, StringComparer.Ordinal).ToArray() ?? [];
            evidence.TryGetValue(module.Name + ":" + m.FullName, out var native);
            return new RecoveryMethodInfo("0x" + m.MetadataToken.ToUInt32().ToString("x8"), m.FullName, native,
                diagnostics, calls, body?.MaxStack, computed, failure, "unverified");
        }).ToArray();
        return new RecoveryAssemblyManifest(1, module.Assembly!.Name!, Hash(File.ReadAllBytes(path)),
            typeof(RecoveryManifest).Assembly.GetName().Version!.ToString(), methods);
    }

    internal static string Serialize(RecoveryAssemblyManifest manifest) => JsonSerializer.Serialize(manifest, RecoveryJsonContext.Default.RecoveryAssemblyManifest);
    internal static void Write(string dllPath, IReadOnlyDictionary<string, RecoveryNativeInfo> evidence)
        => File.WriteAllText(dllPath + ".recovery.json", Serialize(Inspect(dllPath, evidence)) + "\n");
}
