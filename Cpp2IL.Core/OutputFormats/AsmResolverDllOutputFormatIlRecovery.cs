using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;
using AsmResolver;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using AssetRipper.CIL;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Logging;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.OutputFormats;

public class AsmResolverDllOutputFormatIlRecovery : AsmResolverDllOutputFormat
{
    private readonly ConcurrentDictionary<string, RecoveryNativeInfo> _recoveryEvidence = new();

    protected override void OnAssemblyWritten(ApplicationAnalysisContext context, string dllPath)
        => RecoveryManifest.Write(dllPath, _recoveryEvidence);
    public override string OutputFormatId => "dll_il_recovery";

    public override string OutputFormatName => "DLL files with IL Recovery";

    public override List<AssemblyDefinition> BuildAssemblies(ApplicationAnalysisContext context)
    {
        var buildIdentity = RecoveryModuleIdentity.ForBuild(context, this);
        //We're going to need key function addresses, so grab them. This way the logging is more consistent
        Logger.InfoNewline("Finding key function addresses...");
        var start = DateTime.Now;
        _ = context.GetOrCreateKeyFunctionAddresses();
        Logger.InfoNewline($"Key function addresses found in {DateTime.Now.Subtract(start).TotalMilliseconds}ms");

        IlGenerator.InjectHelpersType(context);

        var assemblies = base.BuildAssemblies(context);
        foreach (var assembly in assemblies)
            foreach (var module in assembly.Modules)
            {
                RecoveryModuleIdentity.Assign(module, buildIdentity);
                RelocateLargeStrings(module);
            }
        return assemblies;
    }

    private const int StringHeapSoftLimit = 14 * 1024 * 1024;

    // The #US heap is addressed with 24-bit offsets: a single assembly can exceed
    // 16MB of unique strings (protobuf descriptors in HotFix.dll) and offsets past
    // the limit produce unresolvable tokens. Move the largest strings into an RVA
    // blob read through Encoding.UTF8.GetString until the projected heap fits.
    private static void RelocateLargeStrings(ModuleDefinition module)
    {
        var unique = new Dictionary<string, int>();
        var bodies = new List<AsmResolver.DotNet.Code.Cil.CilMethodBody>();
        foreach (var type in module.GetAllTypes())
        foreach (var method in type.Methods)
        {
            if (method.CilMethodBody is not { } body)
                continue;
            bodies.Add(body);
            foreach (var instruction in body.Instructions)
                if (instruction.OpCode == CilOpCodes.Ldstr && instruction.Operand is string s)
                    unique[s] = s.Length;
        }

        //Entries are stored as UTF-16 bytes plus a trailing flag byte and a
        //compressed-length prefix, so each string costs roughly 2*chars+3.
        var heap = 1L;
        foreach (var n in unique.Values) heap += 2L * n + 3;
        if (heap <= StringHeapSoftLimit) return;

        var helpers = module.GetAllTypes().FirstOrDefault(t => t.FullName == "Cpp2ILInjected.Cpp2ILHelpers");
        if (helpers == null) return;

        var moved = new Dictionary<string, (int Offset, int Length)>();
        var blob = new List<byte>();
        foreach (var kv in unique.OrderByDescending(kv => kv.Value))
        {
            if (heap <= StringHeapSoftLimit) break;
            moved[kv.Key] = (blob.Count, Encoding.UTF8.GetByteCount(kv.Key));
            blob.AddRange(Encoding.UTF8.GetBytes(kv.Key));
            heap -= 2L * kv.Value + 3;
        }

        var factory = module.CorLibTypeFactory;
        var byteArray = new SzArrayTypeSignature(factory.Byte);

        var blobType = new TypeDefinition(null, "__StringBlob",
            TypeAttributes.NestedPrivate | TypeAttributes.Sealed | TypeAttributes.SequentialLayout,
            factory.CorLibScope.CreateTypeReference("System", "ValueType"));
        blobType.ClassLayout = new ClassLayout(1, (uint)blob.Count);
        helpers.NestedTypes.Add(blobType);

        var dataField = new FieldDefinition("__StringData",
            FieldAttributes.Assembly | FieldAttributes.Static | FieldAttributes.HasFieldRva,
            new FieldSignature(blobType.ToTypeSignature()));
        dataField.FieldRva = new DataSegment(blob.ToArray());
        helpers.Fields.Add(dataField);

        var stringsField = new FieldDefinition("__Strings", FieldAttributes.Assembly | FieldAttributes.Static,
            new FieldSignature(byteArray));
        helpers.Fields.Add(stringsField);

        var arrayType = factory.CorLibScope.CreateTypeReference("System", "Array");
        var handleType = factory.CorLibScope.CreateTypeReference("System", "RuntimeFieldHandle");
        var initArray = factory.CorLibScope
            .CreateTypeReference("System.Runtime.CompilerServices", "RuntimeHelpers")
            .CreateMemberReference("InitializeArray",
                MethodSignature.CreateStatic(factory.Void, [arrayType.ToTypeSignature(true), handleType.ToTypeSignature(true)]));

        var cctor = new MethodDefinition(".cctor",
            MethodAttributes.Private | MethodAttributes.Static | MethodAttributes.SpecialName | MethodAttributes.RuntimeSpecialName,
            MethodSignature.CreateStatic(factory.Void, []));
        var cctorBody = new AsmResolver.DotNet.Code.Cil.CilMethodBody();
        var ci = cctorBody.Instructions;
        ci.Add(CilOpCodes.Ldc_I4, blob.Count);
        ci.Add(CilOpCodes.Newarr, factory.Byte.ToTypeDefOrRef());
        ci.Add(CilOpCodes.Dup);
        ci.Add(CilOpCodes.Ldtoken, dataField);
        ci.Add(CilOpCodes.Call, initArray);
        ci.Add(CilOpCodes.Stsfld, stringsField);
        ci.Add(CilOpCodes.Ret);
        cctor.CilMethodBody = cctorBody;
        helpers.Methods.Add(cctor);

        var encodingType = factory.CorLibScope.CreateTypeReference("System.Text", "Encoding");
        var getUtf8 = encodingType.CreateMemberReference("get_UTF8",
            MethodSignature.CreateStatic(encodingType.ToTypeSignature(true), []));
        var getString = encodingType.CreateMemberReference("GetString",
            MethodSignature.CreateInstance(factory.String, [byteArray, factory.Int32, factory.Int32]));

        foreach (var body in bodies)
        {
            var rewritten = false;
            var instructions = body.Instructions;
            for (var i = 0; i < instructions.Count; i++)
            {
                var instruction = instructions[i];
                if (instruction.OpCode != CilOpCodes.Ldstr || instruction.Operand is not string s ||
                    !moved.TryGetValue(s, out var entry))
                    continue;
                //Rewrite in place so existing branch labels stay anchored.
                instruction.OpCode = CilOpCodes.Call;
                instruction.Operand = getUtf8;
                instructions.Insert(i + 1, new CilInstruction(CilOpCodes.Ldsfld, stringsField));
                instructions.Insert(i + 2, new CilInstruction(CilOpCodes.Ldc_I4, entry.Offset));
                instructions.Insert(i + 3, new CilInstruction(CilOpCodes.Ldc_I4, entry.Length));
                instructions.Insert(i + 4, new CilInstruction(CilOpCodes.Callvirt, getString));
                rewritten = true;
                i += 4;
            }

            //The replacement sequence is deeper than ldstr; give the verifier a true peak.
            if (rewritten)
            {
                try { body.MaxStack = Math.Max(body.MaxStack, body.ComputeMaxStack()); }
                catch { body.MaxStack += 4; }
            }
        }

        Logger.VerboseNewline($"Relocated {moved.Count} large strings ({blob.Count} bytes) to RVA blob in {module.Name}", "DllOutput");
    }

    protected override void FillMethodBody(MethodDefinition methodDefinition, MethodAnalysisContext methodContext)
    {
        var status = "lifted-unverified";
        try { FillRecoveryBody(methodDefinition, methodContext, ref status); }
        finally
        {
            _recoveryEvidence[methodDefinition.DeclaringModule!.Name + ":" + methodDefinition.FullName] = new RecoveryNativeInfo(
                methodContext.Definition == null ? null : "0x" + methodContext.UnderlyingPointer.ToString("x"),
                methodContext.RawBytes.Length == 0 ? null : RecoveryManifest.Hash(methodContext.RawBytes.ToArray()), status);
            methodContext.ReleaseAnalysisData();
        }
    }

    private void FillRecoveryBody(MethodDefinition methodDefinition, MethodAnalysisContext methodContext, ref string status)
    {
        var module = methodDefinition.DeclaringModule!;
        var moduleName = module.Name!.ToString();
        var shouldSkip = moduleName.StartsWith("UnityEngine.") || moduleName.StartsWith("Unity.") ||
                         moduleName.StartsWith("System.") || moduleName == "System" ||
                         moduleName.StartsWith("mscorlib");

        if (!methodDefinition.IsManagedMethodWithBody())
        {
            status = "external-or-abstract";
            return;
        }

        methodDefinition.CilMethodBody = new();
        var instructions = methodDefinition.CilMethodBody.Instructions;

        if (shouldSkip)
        {
            status = "intentional-stub";
            FillMethodBodyWithStub(methodDefinition, methodContext);
            return;
        }

        try
        {
            Interlocked.Increment(ref TotalMethodCount);

            methodContext.Analyze();

            if (methodContext.ConvertedIsil.Count == 0)
            {
                status = "unresolved";
                FillMethodBodyWithStub(methodDefinition, methodContext);
            }
            else
                IlGenerator.GenerateIl(methodContext, methodDefinition);

            //WriteControlFlowGraph(methodContext, Path.Combine(Environment.CurrentDirectory, "Cpp2IL", "bin", "Debug", "net9.0", "cpp2il_out", "cfg"));

            Interlocked.Increment(ref SuccessfulMethodCount);
        }
        catch (Exception e)
        {
            status = "analysis-failed";
            // Known analysis limitations (DecompilerException) get a one-line warning; anything
            // else is an unexpected bug and keeps its (collapsed) stack trace.
            var detail = e is DecompilerException ? e.Message : e.ToCollapsedString();

            if (detail.Length > 1000) // unbounded ldstrs can overflow the 24 bit #US heap offset space
                detail = detail[..1000] + "…";

            if (e is DecompilerException)
                Logger.WarnNewline($"Skipping {methodContext.FullName}: {e.Message}");
            else
                Logger.ErrorNewline($"Decompiling {methodContext.FullName} failed: {detail}");
            
            methodDefinition.CilMethodBody = new();
            instructions = methodDefinition.CilMethodBody.Instructions;

            var factory = module.CorLibTypeFactory;
            var exceptionCtor = factory.CorLibScope
                .CreateTypeReference("System", "Exception")
                .CreateMemberReference(".ctor", MethodSignature.CreateInstance(factory.Void, [factory.String]));

            instructions.Add(CilOpCodes.Ldstr, detail);
            instructions.Add(CilOpCodes.Newobj, exceptionCtor);
            instructions.Add(CilOpCodes.Throw);
        }

    }

    public static void WriteControlFlowGraph(MethodAnalysisContext method, string outputPath)
    {
        var graph = method.ControlFlowGraph;

        var sb = new StringBuilder();
        var edges = new List<(int, int)>();

        sb.AppendLine("digraph ControlFlowGraph {");
        sb.AppendLine("    \"label\"=\"Control flow graph\"");

        // no instructions
        graph ??= new ISILControlFlowGraph([]);

        var methodText = $@"{CsFileUtils.GetKeyWordsForMethod(method)} {method.FullNameWithSignature}
parameter locals: {string.Join(", ", method.ParameterLocals)}
parameter operands: {string.Join(", ", method.ParameterOperands)}";

        foreach (var block in graph.Blocks)
        {
            if (block == graph.EntryBlock || block == graph.ExitBlock)
            {
                var isEntry = block == graph.EntryBlock;
                sb.AppendLine($"""
                               	{block.ID} [
                               		"color"="{(isEntry ? "green" : "red")}"
                               		"label"="{(isEntry ? $"Entry ({block.ID})\n{methodText}" : $"Exit ({block.ID})")}"
                               	]
                               """);
            }
            else
            {
                sb.AppendLine($"""
                               	{block.ID} [
                               		"shape"="box"
                               		"label"="{block.ToString().EscapeString().Replace("\\r", "")}"
                               	]
                               """);
            }

            edges.AddRange(block.Successors.Select(b => (block.ID, b.ID)));
        }

        foreach (var edge in edges)
            sb.AppendLine($"    {edge.Item1} -> {edge.Item2}");

        sb.AppendLine("}");

        var type = method.DeclaringType!;
        var assemblyName = MiscUtils.CleanPathElement(type.DeclaringAssembly.CleanAssemblyName);
        var typePath = Path.Combine(type.FullName.Split('.').Select(MiscUtils.CleanPathElement).ToArray());
        var directoryPath = Path.Combine(outputPath, assemblyName, typePath);

        var methodName = MiscUtils.CleanPathElement(method.Name + "_" + string.Join("_",
            method.Parameters.Select(p => MiscUtils.CleanPathElement(p.ParameterType.Name))));
        var path = Path.Combine(directoryPath, methodName) + ".dot";

        if (path.Length > 260)
        {
            path = path[..250];
            path += ".dot";
        }

        var directory = Path.GetDirectoryName(path)!;
        if (!Directory.Exists(directory))
            Directory.CreateDirectory(directory);

        File.WriteAllText(path, sb.ToString());
    }
}
