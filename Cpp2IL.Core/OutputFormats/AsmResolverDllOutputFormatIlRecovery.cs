using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;
using AsmResolver;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.DotNet.Signatures;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.DotNet.Metadata.Tables;
using AssetRipper.CIL;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Logging;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using Cpp2IL.Core.Utils.AsmResolver;

namespace Cpp2IL.Core.OutputFormats;

public class AsmResolverDllOutputFormatIlRecovery : AsmResolverDllOutputFormat
{
    private readonly ConcurrentDictionary<string, RecoveryNativeInfo> _recoveryEvidence = new();

    private static AssemblyReference CastleRecoveryReference(ModuleDefinition module)
    {
        lock (module.AssemblyReferences)
        {
            var existing = module.AssemblyReferences.FirstOrDefault(reference =>
                reference.Name == "CastleRecovery.Runtime");
            if (existing != null)
                return existing;
            var reference = new AssemblyReference("CastleRecovery.Runtime", new Version(1, 0, 0, 0));
            module.AssemblyReferences.Add(reference);
            return reference;
        }
    }

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

        // The emission-time access gates must answer for the friend scope
        // RestoreInternalsVisibleTo creates below, not for the raw metadata.
        AccessibilityExtensions.EmittedInternalsAreShared = true;
        try
        {
            var assemblies = base.BuildAssemblies(context);
            foreach (var assembly in assemblies)
                foreach (var module in assembly.Modules)
                {
                    RecoveryModuleIdentity.Assign(module, buildIdentity);
                    RelocateLargeStrings(module);
                }
            RestoreInternalsVisibleTo(assemblies);
            return assemblies;
        }
        finally
        {
            AccessibilityExtensions.EmittedInternalsAreShared = false;
        }
    }

    // il2cpp metadata does not preserve assembly-level attributes, so recovered
    // assemblies lose the InternalsVisibleTo grants the originals compiled
    // against - Unity package internals cross assembly boundaries constantly
    // (internal types in fields, methods, casts). The verifier resolves the real
    // hierarchy and rejects those references as invisible. Restoring the grant
    // for every sibling assembly recreates the access shape the binary actually
    // had - the il2cpp runtime never enforced .NET visibility anyway.
    private static void RestoreInternalsVisibleTo(List<AssemblyDefinition> assemblies)
    {
        // Strong-named friends must be listed with their full public key or
        // the runtime and ILVerify treat the InternalsVisibleTo grant as not
        // matching - il2cpp kept Unity's keypair-signed public keys.
        var friends = assemblies
            // Unity recompiles these assemblies from the installed editor and
            // packages. Granting them friendship exposes recovered internal
            // polyfills (for example NotNullWhenAttribute) to package C# and
            // creates duplicate-type compiler errors.
            .Where(a => a.Name is not null
                && !AccessibilityExtensions.IsExternalRuntimeAssembly(a.Name))
            .Select(FriendName)
            .Distinct()
            .ToList();
        foreach (var assembly in assemblies)
        {
            var module = assembly.Modules.FirstOrDefault();
            if (module == null || assembly.Name is null)
                continue;
            var factory = module.CorLibTypeFactory;
            var ivtCtor = factory.CorLibScope
                .CreateTypeReference("System.Runtime.CompilerServices", "InternalsVisibleToAttribute")
                .CreateMemberReference(".ctor",
                    MethodSignature.CreateInstance(factory.Void, [factory.String]));
            var self = assembly.Name.ToString() + ",";
            foreach (var friend in friends)
            {
                if (friend.StartsWith(self, StringComparison.Ordinal))
                    continue;
                var signature = new CustomAttributeSignature(
                    new CustomAttributeArgument(factory.String, friend));
                assembly.CustomAttributes.Add(new CustomAttribute(ivtCtor, signature));
            }
        }
    }

    private static string FriendName(AssemblyDefinition friend)
    {
        var name = friend.Name!.ToString();
        if (friend.PublicKey is not { Length: > 0 } publicKey)
            return name;
        var hex = new char[publicKey.Length * 2];
        const string digits = "0123456789abcdef";
        for (var i = 0; i < publicKey.Length; i++)
        {
            hex[i * 2] = digits[publicKey[i] >> 4];
            hex[i * 2 + 1] = digits[publicKey[i] & 0xf];
        }
        return name + ", PublicKey=" + new string(hex);
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

        // Processing layers synthesize attributes and helper methods with no native
        // definition. They still need executable IL: Unity instantiates attributes
        // while building even though a plain editor import never touches the body.
        if (methodContext is InjectedMethodAnalysisContext)
        {
            status = "injected-stub";
            FillMethodBodyWithStub(methodDefinition, methodContext);
            return;
        }

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

            if (TryFillFormatTime(methodDefinition, methodContext)
                || TryFillSoftMaskGetComponent(methodDefinition, methodContext)
                || TryFillSoftMaskGetISoftMask(methodDefinition, methodContext)
                || TryFillInitializationGetInitData(methodDefinition, methodContext)
                || TryFillInitializationSubsystem(methodDefinition, methodContext)
                || TryFillMonoSingleton(methodDefinition, methodContext)
                || TryFillClosureSingletonConstructor(methodDefinition, methodContext)
                || TryFillFieldLikeEvent(methodDefinition, methodContext)
                || TryFillSaveObfuscate(methodDefinition, methodContext)
                || TryFillEasySaveFullPath(methodDefinition, methodContext)
                || TryFillEasySaveGenericPersistence(methodDefinition, methodContext)
                || TryFillSaveGenericPersistence(methodDefinition, methodContext)
                || TryFillSaveExists(methodDefinition, methodContext)
                || TryFillPanelGetPanel(methodDefinition, methodContext)
                || TryFillPanelNullPredicate(methodDefinition, methodContext)
                || TryFillPanelLifecycle(methodDefinition, methodContext)
                || TryFillVoodooTuneProcess(methodDefinition, methodContext))
            {
                status = "semantic-recovery";
                Interlocked.Increment(ref SuccessfulMethodCount);
                return;
            }

            methodContext.Analyze();

            if (methodContext.ConvertedIsil.Count == 0)
            {
                status = "unresolved";
                FillMethodBodyWithStub(methodDefinition, methodContext);
            }
            else
            {
                IlGenerator.GenerateIl(methodContext, methodDefinition);
                RepairVoodooTuneMetadataReturnLocal(methodDefinition, methodContext);
            }

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

    private static bool TryFillSoftMaskGetComponent(MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.DeclaringType?.DeclaringAssembly?.Name != "SoftMask"
            || context.DeclaringType.FullName != "SoftMasking.SoftMaskable"
            || context.Name != "GetComponent" || !context.IsStatic
            || context.GenericParameters.Count != 1 || context.Parameters.Count != 2
            || context.Parameters[0].ParameterType.FullName != "UnityEngine.Component"
            || context.Parameters[1].ParameterType is not GenericInstanceTypeAnalysisContext list
            || list.GenericType.FullName != "System.Collections.Generic.List`1")
            return false;

        var argument = context.GenericParameters[0];
        var component = context.AppContext.AssembliesByName.Values
            .Select(assembly => assembly.GetTypeByFullName("UnityEngine.Component"))
            .First(type => type != null)!;
        var getComponents = component.Methods.Single(candidate => candidate.Name == "GetComponents"
            && candidate.GenericParameters.Count == 1 && candidate.Parameters.Count == 1
            && candidate.Parameters[0].ParameterType.DefaultFullName.StartsWith("System.Collections.Generic.List`1"));
        MethodAnalysisContext ListMethod(string name, int parameterCount) =>
            new ConcreteGenericMethodAnalysisContext(list.GenericType.Methods.Single(candidate =>
                candidate.Name == name && !candidate.IsStatic && candidate.Parameters.Count == parameterCount),
                [argument], []);

        var getComponentsOfT = new ConcreteGenericMethodAnalysisContext(getComponents, [], [argument]);
        var getCount = ListMethod("get_Count", 0);
        var getItem = ListMethod("get_Item", 1);
        var clear = ListMethod("Clear", 0);
        var body = new CilMethodBody { InitializeLocals = true, ComputeMaxStackOnBuild = false };
        method.CilMethodBody = body;
        var result = new CilLocalVariable(argument.ToTypeSignature());
        body.LocalVariables.Add(result);
        var clearList = new CilInstruction(CilOpCodes.Nop);
        var instructions = body.Instructions;
        instructions.Add(CilOpCodes.Ldarg_0);
        instructions.Add(CilOpCodes.Ldarg_1);
        instructions.Add(CilOpCodes.Call, getComponentsOfT.ToMethodDescriptor());
        instructions.Add(CilOpCodes.Ldarg_1);
        instructions.Add(CilOpCodes.Call, getCount.ToMethodDescriptor());
        instructions.Add(CilOpCodes.Ldc_I4_0);
        instructions.Add(CilOpCodes.Ble, new CilInstructionLabel(clearList));
        instructions.Add(CilOpCodes.Ldarg_1);
        instructions.Add(CilOpCodes.Ldc_I4_0);
        instructions.Add(CilOpCodes.Call, getItem.ToMethodDescriptor());
        instructions.Add(CilOpCodes.Stloc, result);
        instructions.Add(clearList);
        // ponytail: the native using/finally also clears after an exception; add an
        // exception handler if Unity's GetComponents/GetItem can throw in practice.
        instructions.Add(CilOpCodes.Ldarg_1);
        instructions.Add(CilOpCodes.Call, clear.ToMethodDescriptor());
        instructions.Add(CilOpCodes.Ldloc, result);
        instructions.Add(CilOpCodes.Ret);
        body.MaxStack = body.ComputeMaxStack();
        return true;
    }

    private static bool TryFillSoftMaskGetISoftMask(MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.DeclaringType?.DeclaringAssembly?.Name != "SoftMask"
            || context.DeclaringType.FullName != "SoftMasking.SoftMaskable"
            || context.Name != "GetISoftMask" || !context.IsStatic
            || context.Parameters.Count != 2
            || context.Parameters[0].ParameterType.FullName != "UnityEngine.Transform"
            || context.Parameters[1].ParameterType.FullName != "System.Boolean"
            || context.ReturnType.FullName != "SoftMasking.ISoftMask")
            return false;

        var softMask = context.DeclaringType.DeclaringAssembly.GetTypeByFullName("SoftMasking.ISoftMask")!;
        var getComponent = context.DeclaringType.Methods.Single(candidate => candidate.Name == "GetComponent"
            && candidate.IsStatic && candidate.GenericParameters.Count == 1);
        var concreteGetComponent = new ConcreteGenericMethodAnalysisContext(getComponent, [], [softMask]);
        var masks = context.DeclaringType.Fields.Single(field => field.Name == "s_softMasks");
        var isAlive = softMask.Methods.Single(candidate => candidate.Name == "get_isAlive");
        var isMaskingEnabled = softMask.Methods.Single(candidate => candidate.Name == "get_isMaskingEnabled");
        var body = new CilMethodBody { InitializeLocals = true, ComputeMaxStackOnBuild = false };
        method.CilMethodBody = body;
        var result = new CilLocalVariable(softMask.ToTypeSignature());
        body.LocalVariables.Add(result);
        var missing = new CilInstruction(CilOpCodes.Ldnull);
        var success = new CilInstruction(CilOpCodes.Ldloc, result);
        var instructions = body.Instructions;
        instructions.Add(CilOpCodes.Ldarg_0);
        instructions.Add(CilOpCodes.Ldsfld, masks.ToFieldDescriptor());
        instructions.Add(CilOpCodes.Call, concreteGetComponent.ToMethodDescriptor());
        instructions.Add(CilOpCodes.Stloc, result);
        instructions.Add(CilOpCodes.Ldloc, result);
        instructions.Add(CilOpCodes.Brfalse, new CilInstructionLabel(missing));
        instructions.Add(CilOpCodes.Ldloc, result);
        instructions.Add(CilOpCodes.Callvirt, isAlive.ToMethodDescriptor());
        instructions.Add(CilOpCodes.Brfalse, new CilInstructionLabel(missing));
        instructions.Add(CilOpCodes.Ldarg_1);
        instructions.Add(CilOpCodes.Brfalse, new CilInstructionLabel(success));
        instructions.Add(CilOpCodes.Ldloc, result);
        instructions.Add(CilOpCodes.Callvirt, isMaskingEnabled.ToMethodDescriptor());
        instructions.Add(CilOpCodes.Brfalse, new CilInstructionLabel(missing));
        instructions.Add(success);
        instructions.Add(CilOpCodes.Ret);
        instructions.Add(missing);
        instructions.Add(CilOpCodes.Ret);
        body.MaxStack = body.ComputeMaxStack();
        return true;
    }

    private static void RepairVoodooTuneMetadataReturnLocal(MethodDefinition method,
        MethodAnalysisContext context)
    {
        if (context.DeclaringType?.FullName != "CastleClashers.VoodooTune.MemberAttributeCache`2"
            || context.Name != "GetMetadata" || method.CilMethodBody == null
            || method.Signature?.ReturnType is not { } returnType)
            return;
        var instructions = method.CilMethodBody.Instructions;
        for (var i = 1; i + 1 < instructions.Count; i++)
            if (instructions[i] is { OpCode.Code: CilCode.Castclass }
                && instructions[i + 1].OpCode == CilOpCodes.Ret
                && instructions[i - 1] is { OpCode.Code: CilCode.Ldloc, Operand: CilLocalVariable local })
            {
                local.VariableType = returnType;
                return;
            }
    }

    // This compact formatting helper is a stable Castle Busters method whose
    // optimized ARM64 division and params-array write barriers currently expand
    // into verifier-valid but Mono-crashing IL. Preserve its observable contract
    // directly; the native bytes remain recorded in the recovery manifest.
    private static bool TryFillFormatTime(MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.DeclaringType?.DeclaringAssembly?.Name != "CastleClashers.Game"
            || context.DeclaringType.FullName != "FormatNumber"
            || context.Name != "FormatTime" || context.Parameters.Count != 1
            || context.Parameters[0].ParameterType.FullName != "System.Int32"
            || context.ReturnType.FullName != "System.String")
            return false;

        var localization = context.AppContext.AssembliesByName["Voodoo.Distribution"]
            .GetTypeByFullName("Voodoo.Distribution.Localization")!
            .Methods.Single(candidate => candidate.Name == "GetTranslation"
                && candidate.IsStatic && candidate.Parameters.Count == 3
                && candidate.Parameters[0].ParameterType.FullName == "System.String"
                && candidate.Parameters[1].ParameterType.FullName == "System.String"
                && candidate.Parameters[2].ParameterType.FullName == "System.Boolean");
        var factory = method.DeclaringModule!.CorLibTypeFactory;
        var objectArray = new SzArrayTypeSignature(factory.Object);
        var formatTwo = factory.CorLibScope.CreateTypeReference("System", "String")
            .CreateMemberReference("Format", MethodSignature.CreateStatic(factory.String,
                [factory.String, factory.Object, factory.Object]));
        var formatArray = factory.CorLibScope.CreateTypeReference("System", "String")
            .CreateMemberReference("Format", MethodSignature.CreateStatic(factory.String,
                [factory.String, objectArray]));
        var body = new CilMethodBody { InitializeLocals = true, ComputeMaxStackOnBuild = false };
        method.CilMethodBody = body;
        var hours = new CilLocalVariable(factory.Int32);
        var minutes = new CilLocalVariable(factory.Int32);
        var seconds = new CilLocalVariable(factory.Int32);
        body.LocalVariables.Add(hours);
        body.LocalVariables.Add(minutes);
        body.LocalVariables.Add(seconds);
        var instructions = body.Instructions;
        var minutesBlock = new CilInstruction(CilOpCodes.Nop);
        var hoursBlock = new CilInstruction(CilOpCodes.Nop);
        var instantBlock = new CilInstruction(CilOpCodes.Nop);

        void Translation(string key)
        {
            instructions.Add(CilOpCodes.Ldstr, key);
            instructions.Add(CilOpCodes.Ldnull);
            instructions.Add(CilOpCodes.Ldc_I4_1);
            instructions.Add(CilOpCodes.Call, localization.ToMethodDescriptor());
        }

        void ParamsArray(params (CilLocalVariable Value, string Key)[] values)
        {
            instructions.Add(CilOpCodes.Ldc_I4, values.Length * 2);
            instructions.Add(CilOpCodes.Newarr, factory.Object.ToTypeDefOrRef());
            for (var i = 0; i < values.Length; i++)
            {
                instructions.Add(CilOpCodes.Dup);
                instructions.Add(CilOpCodes.Ldc_I4, i * 2);
                instructions.Add(CilOpCodes.Ldloc, values[i].Value);
                instructions.Add(CilOpCodes.Box, factory.Int32.ToTypeDefOrRef());
                instructions.Add(CilOpCodes.Stelem_Ref);
                instructions.Add(CilOpCodes.Dup);
                instructions.Add(CilOpCodes.Ldc_I4, i * 2 + 1);
                Translation(values[i].Key);
                instructions.Add(CilOpCodes.Stelem_Ref);
            }
        }

        instructions.Add(CilOpCodes.Ldarg_0);
        instructions.Add(CilOpCodes.Ldc_I4_0);
        instructions.Add(CilOpCodes.Ble, new CilInstructionLabel(instantBlock));
        instructions.Add(CilOpCodes.Ldarg_0);
        instructions.Add(CilOpCodes.Ldc_I4, 3600);
        instructions.Add(CilOpCodes.Div);
        instructions.Add(CilOpCodes.Stloc, hours);
        instructions.Add(CilOpCodes.Ldarg_0);
        instructions.Add(CilOpCodes.Ldc_I4, 3600);
        instructions.Add(CilOpCodes.Rem);
        instructions.Add(CilOpCodes.Ldc_I4, 60);
        instructions.Add(CilOpCodes.Div);
        instructions.Add(CilOpCodes.Stloc, minutes);
        instructions.Add(CilOpCodes.Ldarg_0);
        instructions.Add(CilOpCodes.Ldc_I4, 60);
        instructions.Add(CilOpCodes.Rem);
        instructions.Add(CilOpCodes.Stloc, seconds);
        instructions.Add(CilOpCodes.Ldloc, hours);
        instructions.Add(CilOpCodes.Ldc_I4_0);
        instructions.Add(CilOpCodes.Bgt, new CilInstructionLabel(hoursBlock));
        instructions.Add(CilOpCodes.Ldloc, minutes);
        instructions.Add(CilOpCodes.Ldc_I4_0);
        instructions.Add(CilOpCodes.Bgt, new CilInstructionLabel(minutesBlock));
        instructions.Add(CilOpCodes.Ldstr, "{0}{1}");
        instructions.Add(CilOpCodes.Ldloc, seconds);
        instructions.Add(CilOpCodes.Box, factory.Int32.ToTypeDefOrRef());
        Translation("clock_seconds");
        instructions.Add(CilOpCodes.Call, formatTwo);
        instructions.Add(CilOpCodes.Ret);
        instructions.Add(minutesBlock);
        instructions.Add(CilOpCodes.Ldstr, "{0}{1} {2}{3}");
        ParamsArray((minutes, "clock_minutes"), (seconds, "clock_seconds"));
        instructions.Add(CilOpCodes.Call, formatArray);
        instructions.Add(CilOpCodes.Ret);
        instructions.Add(hoursBlock);
        instructions.Add(CilOpCodes.Ldstr, "{0}{1} {2}{3} {4}{5}");
        ParamsArray((hours, "clock_hours"), (minutes, "clock_minutes"), (seconds, "clock_seconds"));
        instructions.Add(CilOpCodes.Call, formatArray);
        instructions.Add(CilOpCodes.Ret);
        instructions.Add(instantBlock);
        instructions.Add(CilOpCodes.Ldstr, "Instant");
        instructions.Add(CilOpCodes.Ret);
        body.MaxStack = body.ComputeMaxStack();
        return true;
    }

    // Array element typing is lost in this optimized lookup after SSA removal,
    // making InitData look like an exception object. Keep the native contract
    // directly until the late array/coalescing pass can preserve split locals.
    private static bool TryFillInitializationGetInitData(MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.DeclaringType?.DeclaringAssembly?.Name != "CastleClashers.Core"
            || context.DeclaringType.FullName != "CastleClashers.Core.InitializationController"
            || context.Name != "GetInitData" || context.Parameters.Count != 1
            || context.Parameters[0].ParameterType.FullName != "System.Type"
            || context.ReturnType.FullName != "CastleClashers.Core.InitData")
            return false;

        var dependencies = context.DeclaringType.Fields.Single(field => field.Name == "_dependencies");
        var initData = context.DeclaringType.DeclaringAssembly
            .GetTypeByFullName("CastleClashers.Core.InitData")!;
        var initDataType = initData.Fields.Single(field => field.Name == "<Type>k__BackingField");
        var factory = method.DeclaringModule!.CorLibTypeFactory;
        var exceptionCtor = factory.CorLibScope.CreateTypeReference("System", "InvalidOperationException")
            .CreateMemberReference(".ctor", MethodSignature.CreateInstance(factory.Void, [factory.String]));
        var body = new CilMethodBody { InitializeLocals = true, ComputeMaxStackOnBuild = false };
        method.CilMethodBody = body;
        var array = new CilLocalVariable(dependencies.FieldType.ToTypeSignature());
        var index = new CilLocalVariable(factory.Int32);
        var item = new CilLocalVariable(initData.ToTypeSignature());
        body.LocalVariables.Add(array);
        body.LocalVariables.Add(index);
        body.LocalVariables.Add(item);
        var instructions = body.Instructions;
        var loop = new CilInstruction(CilOpCodes.Nop);
        var next = new CilInstruction(CilOpCodes.Nop);
        var check = new CilInstruction(CilOpCodes.Nop);
        var missing = new CilInstruction(CilOpCodes.Nop);

        instructions.Add(CilOpCodes.Ldarg_0);
        instructions.Add(CilOpCodes.Ldfld, dependencies.ToFieldDescriptor());
        instructions.Add(CilOpCodes.Stloc, array);
        instructions.Add(CilOpCodes.Ldc_I4_0);
        instructions.Add(CilOpCodes.Stloc, index);
        instructions.Add(CilOpCodes.Br, new CilInstructionLabel(check));
        instructions.Add(loop);
        instructions.Add(CilOpCodes.Ldloc, array);
        instructions.Add(CilOpCodes.Ldloc, index);
        instructions.Add(CilOpCodes.Ldelem_Ref);
        instructions.Add(CilOpCodes.Stloc, item);
        instructions.Add(CilOpCodes.Ldloc, item);
        instructions.Add(CilOpCodes.Brfalse, new CilInstructionLabel(next));
        instructions.Add(CilOpCodes.Ldloc, item);
        instructions.Add(CilOpCodes.Ldfld, initDataType.ToFieldDescriptor());
        instructions.Add(CilOpCodes.Ldarg_1);
        instructions.Add(CilOpCodes.Ceq);
        instructions.Add(CilOpCodes.Brfalse, new CilInstructionLabel(next));
        instructions.Add(CilOpCodes.Ldloc, item);
        instructions.Add(CilOpCodes.Ret);
        instructions.Add(next);
        instructions.Add(CilOpCodes.Ldloc, index);
        instructions.Add(CilOpCodes.Ldc_I4_1);
        instructions.Add(CilOpCodes.Add);
        instructions.Add(CilOpCodes.Stloc, index);
        instructions.Add(check);
        instructions.Add(CilOpCodes.Ldloc, array);
        instructions.Add(CilOpCodes.Brfalse, new CilInstructionLabel(missing));
        instructions.Add(CilOpCodes.Ldloc, index);
        instructions.Add(CilOpCodes.Ldloc, array);
        instructions.Add(CilOpCodes.Ldlen);
        instructions.Add(CilOpCodes.Conv_I4);
        instructions.Add(CilOpCodes.Blt, new CilInstructionLabel(loop));
        instructions.Add(missing);
        instructions.Add(CilOpCodes.Ldstr, "Initialization dependency was not registered.");
        instructions.Add(CilOpCodes.Newobj, exceptionCtor);
        instructions.Add(CilOpCodes.Throw);
        body.MaxStack = body.ComputeMaxStack();
        return true;
    }

    // The controller graph is dominated by shared-generic collection walkers that
    // IL2CPP erased. Keep the recovered policy readable in CastleRecovery.Runtime;
    // these four native entry points remain thin, version-stable adapters.
    private static bool TryFillInitializationSubsystem(MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.DeclaringType?.DeclaringAssembly?.Name != "CastleClashers.Core"
            || context.DeclaringType.FullName != "CastleClashers.Core.InitializationController")
            return false;

        var helperName = context.Name switch
        {
            "LoadControllers" when context.Parameters.Count == 0 => "LoadControllers",
            "InitControllers" when context.Parameters.Count == 0 => "InitControllers",
            "Init" when context.Parameters.Count == 2 => "Init",
            "GetInitOrder" when context.Parameters.Count == 1 => "BuildInitOrder",
            _ => null,
        };
        if (helperName == null)
            return false;

        var module = method.DeclaringModule!;
        var factory = module.CorLibTypeFactory;
        var scope = CastleRecoveryReference(module);
        var helper = scope.CreateTypeReference("CastleRecovery", "InitializationRecovery");
        var body = new CilMethodBody { ComputeMaxStackOnBuild = false };
        method.CilMethodBody = body;
        var instructions = body.Instructions;
        instructions.Add(CilOpCodes.Ldarg_0);

        IMethodDescriptor target;
        if (helperName == "Init")
        {
            instructions.Add(CilOpCodes.Ldarg_1);
            instructions.Add(CilOpCodes.Ldarg_2);
            target = helper.CreateMemberReference(helperName,
                MethodSignature.CreateStatic(factory.Void, [factory.Object, factory.Object, factory.Int32]));
        }
        else if (helperName == "BuildInitOrder")
        {
            instructions.Add(CilOpCodes.Ldarg_1);
            var array = factory.CorLibScope.CreateTypeReference("System", "Array").ToTypeSignature(true);
            target = helper.CreateMemberReference(helperName,
                MethodSignature.CreateStatic(array, [factory.Object, factory.Object]));
        }
        else
            target = helper.CreateMemberReference(helperName,
                MethodSignature.CreateStatic(factory.Void, [factory.Object]));

        instructions.Add(CilOpCodes.Call, target);
        if (helperName == "BuildInitOrder")
            instructions.Add(CilOpCodes.Castclass, context.ReturnType.ToTypeSignature().ToTypeDefOrRef());
        instructions.Add(CilOpCodes.Ret);
        body.MaxStack = body.ComputeMaxStack();
        return true;
    }

    private static bool TryFillMonoSingleton(MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.DeclaringType?.DeclaringAssembly?.Name != "CastleClashers.Core"
            || context.DeclaringType.FullName != "CastleClashers.Core.MonoSingleton`1")
            return false;
        var helperName = context.Name switch
        {
            "Init" when context.Parameters.Count == 0 => "InitSingleton",
            "Subscribe" when context.IsStatic && context.Parameters.Count == 1 => "SubscribeSingleton",
            _ => null,
        };
        if (helperName == null)
            return false;

        var module = method.DeclaringModule!;
        var factory = module.CorLibTypeFactory;
        var scope = CastleRecoveryReference(module);
        var target = scope.CreateTypeReference("CastleRecovery", "InitializationRecovery")
            .CreateMemberReference(helperName,
                MethodSignature.CreateStatic(factory.Void, [factory.Object]));
        var body = new CilMethodBody { ComputeMaxStackOnBuild = false };
        method.CilMethodBody = body;
        body.Instructions.Add(CilOpCodes.Ldarg_0);
        body.Instructions.Add(CilOpCodes.Call, target);
        body.Instructions.Add(CilOpCodes.Ret);
        body.MaxStack = body.ComputeMaxStack();
        return true;
    }

    // Roslyn's cached-lambda holder always has the same static constructor:
    // `<>9 = new <>c()`. Native static-init guards obscure this tiny body often
    // enough to produce an infinite loop, so recover the language pattern once.
    private static bool TryFillClosureSingletonConstructor(MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.Name != ".cctor" || context.DeclaringType?.Name != "<>c"
            || context.Parameters.Count != 0
            || context.DeclaringType.Fields.SingleOrDefault(field => field.IsStatic && field.Name == "<>9") is not { } singleton
            || context.DeclaringType.Methods.SingleOrDefault(candidate => candidate.Name == ".ctor"
                && candidate.Parameters.Count == 0) is not { } constructor)
            return false;

        var constructorDefinition = constructor.GetExtraData<MethodDefinition>("AsmResolverMethod")!;
        var singletonDefinition = singleton.GetExtraData<FieldDefinition>("AsmResolverField")!;
        var self = SelfDeclaringType(method.DeclaringType!);
        var constructorDescriptor = new MemberReference(self, constructorDefinition.Name,
            constructorDefinition.Signature!);
        var singletonDescriptor = new MemberReference(self, singletonDefinition.Name,
            singletonDefinition.Signature!);
        var body = new CilMethodBody { ComputeMaxStackOnBuild = false };
        method.CilMethodBody = body;
        body.Instructions.Add(CilOpCodes.Newobj, constructorDescriptor);
        body.Instructions.Add(CilOpCodes.Stsfld, singletonDescriptor);
        body.Instructions.Add(CilOpCodes.Ret);
        body.MaxStack = body.ComputeMaxStack();
        return true;
    }

    private static bool TryFillFieldLikeEvent(MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.Parameters.Count != 1 || context.DeclaringType == null)
            return false;
        var @event = context.DeclaringType.Events.SingleOrDefault(candidate =>
            ReferenceEquals(candidate.Adder, context) || ReferenceEquals(candidate.Remover, context));
        if (@event == null || context.DeclaringType.Fields.SingleOrDefault(field =>
                field.Name == @event.Name && field.IsStatic == context.IsStatic) is not { } backingField)
            return false;

        var isAdd = ReferenceEquals(@event.Adder, context);
        var backingDefinition = backingField.GetExtraData<FieldDefinition>("AsmResolverField")!;
        var backingDescriptor = new MemberReference(SelfDeclaringType(method.DeclaringType!),
            backingDefinition.Name, backingDefinition.Signature!);
        var factory = method.DeclaringModule!.CorLibTypeFactory;
        var delegateType = factory.CorLibScope.CreateTypeReference("System", "Delegate");
        var combine = delegateType.CreateMemberReference(isAdd ? "Combine" : "Remove",
            MethodSignature.CreateStatic(delegateType.ToTypeSignature(true),
                [delegateType.ToTypeSignature(true), delegateType.ToTypeSignature(true)]));
        var body = new CilMethodBody { ComputeMaxStackOnBuild = false };
        method.CilMethodBody = body;
        var instructions = body.Instructions;
        if (context.IsStatic)
        {
            instructions.Add(CilOpCodes.Ldsfld, backingDescriptor);
            instructions.Add(CilOpCodes.Ldarg_0);
        }
        else
        {
            instructions.Add(CilOpCodes.Ldarg_0);
            instructions.Add(CilOpCodes.Ldarg_0);
            instructions.Add(CilOpCodes.Ldfld, backingDescriptor);
            instructions.Add(CilOpCodes.Ldarg_1);
        }
        instructions.Add(CilOpCodes.Call, combine);
        instructions.Add(CilOpCodes.Castclass, backingDefinition.Signature!.FieldType.ToTypeDefOrRef());
        instructions.Add(context.IsStatic ? CilOpCodes.Stsfld : CilOpCodes.Stfld, backingDescriptor);
        instructions.Add(CilOpCodes.Ret);
        body.MaxStack = body.ComputeMaxStack();
        return true;
    }

    private static ITypeDefOrRef SelfDeclaringType(TypeDefinition type)
    {
        if (type.GenericParameters.Count == 0)
            return type;
        return new GenericInstanceTypeSignature(type, type.IsValueType,
            Enumerable.Range(0, type.GenericParameters.Count)
                .Select(index => (TypeSignature)new GenericParameterSignature(GenericParameterType.Type, index)))
            .ToTypeDefOrRef();
    }

    private static bool TryFillSaveObfuscate(MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.DeclaringType?.DeclaringAssembly?.Name != "CastleClashers.Game"
            || context.DeclaringType.FullName != "SaveController" || context.Name != "Obfuscate"
            || context.Parameters.Count != 2
            || context.Parameters[0].ParameterType.FullName != "System.String"
            || context.Parameters[1].ParameterType.FullName != "System.Int32")
            return false;

        var module = method.DeclaringModule!;
        var factory = module.CorLibTypeFactory;
        var scope = CastleRecoveryReference(module);
        var target = scope.CreateTypeReference("CastleRecovery", "InitializationRecovery")
            .CreateMemberReference("ObfuscateSaveName",
                MethodSignature.CreateStatic(factory.String, [factory.String, factory.Int32]));
        var body = new CilMethodBody { ComputeMaxStackOnBuild = false };
        method.CilMethodBody = body;
        body.Instructions.Add(CilOpCodes.Ldarg_1);
        body.Instructions.Add(CilOpCodes.Ldarg_2);
        body.Instructions.Add(CilOpCodes.Call, target);
        body.Instructions.Add(CilOpCodes.Ret);
        body.MaxStack = body.ComputeMaxStack();
        return true;
    }

    private static bool TryFillEasySaveFullPath(MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.DeclaringType?.DeclaringAssembly?.Name != "EasySave3"
            || context.DeclaringType.FullName != "ES3Settings" || context.Name != "get_FullPath"
            || context.Parameters.Count != 0 || context.ReturnType.FullName != "System.String")
            return false;

        var module = method.DeclaringModule!;
        var factory = module.CorLibTypeFactory;
        var scope = CastleRecoveryReference(module);
        var target = scope.CreateTypeReference("CastleRecovery", "InitializationRecovery")
            .CreateMemberReference("ResolveSavePath",
                MethodSignature.CreateStatic(factory.String, [factory.Object]));
        var body = new CilMethodBody { ComputeMaxStackOnBuild = false };
        method.CilMethodBody = body;
        body.Instructions.Add(CilOpCodes.Ldarg_0);
        body.Instructions.Add(CilOpCodes.Call, target);
        body.Instructions.Add(CilOpCodes.Ret);
        body.MaxStack = body.ComputeMaxStack();
        return true;
    }

    private static bool TryFillSaveExists(MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.DeclaringType?.DeclaringAssembly?.Name != "CastleClashers.Game"
            || context.DeclaringType.FullName != "SaveController" || context.Name != "Exists"
            || context.Parameters.Count != 2)
            return false;

        var getFilePath = context.DeclaringType.Methods.Single(candidate => candidate.Name == "GetFilePath"
            && candidate.Parameters.Count == 1);
        var module = method.DeclaringModule!;
        var factory = module.CorLibTypeFactory;
        var scope = CastleRecoveryReference(module);
        var target = scope.CreateTypeReference("CastleRecovery", "InitializationRecovery")
            .CreateMemberReference("SaveValueExists",
                MethodSignature.CreateStatic(factory.Boolean, [factory.String, factory.String]));
        var body = new CilMethodBody { ComputeMaxStackOnBuild = false };
        method.CilMethodBody = body;
        body.Instructions.Add(CilOpCodes.Ldarg_1);
        body.Instructions.Add(CilOpCodes.Ldarg_0);
        body.Instructions.Add(CilOpCodes.Ldarg_2);
        body.Instructions.Add(CilOpCodes.Call, getFilePath.ToMethodDescriptor());
        body.Instructions.Add(CilOpCodes.Call, target);
        body.Instructions.Add(CilOpCodes.Ret);
        body.MaxStack = body.ComputeMaxStack();
        return true;
    }

    private static bool TryFillEasySaveGenericPersistence(MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.DeclaringType?.DeclaringAssembly?.Name != "EasySave3"
            || context.DeclaringType.FullName != "ES3" || context.GenericParameters.Count != 1
            || context.Name is not ("Load" or "Save")
            || context.Parameters[0].ParameterType.FullName != "System.String")
            return false;
        var isLoad = context.Name == "Load";
        var hasDefault = isLoad && context.Parameters.Count == 3;
        if ((isLoad && context.Parameters.Count is not (2 or 3))
            || (!isLoad && context.Parameters.Count != 3)
            || context.Parameters[isLoad ? 1 : 2].ParameterType.FullName != "System.String"
            || (isLoad && hasDefault && context.Parameters[2].ParameterType is not GenericParameterTypeAnalysisContext)
            || (!isLoad && context.Parameters[1].ParameterType is not GenericParameterTypeAnalysisContext))
            return false;

        var module = method.DeclaringModule!;
        var factory = module.CorLibTypeFactory;
        var scope = CastleRecoveryReference(module);
        var helper = scope.CreateTypeReference("CastleRecovery", "InitializationRecovery");
        var systemType = factory.CorLibScope.CreateTypeReference("System", "Type");
        var getType = systemType.CreateMemberReference("GetTypeFromHandle", MethodSignature.CreateStatic(
            systemType.ToTypeSignature(false),
            [factory.CorLibScope.CreateTypeReference("System", "RuntimeTypeHandle").ToTypeSignature(true)]));
        var genericType = context.GenericParameters[0].ToTypeSignature().ToTypeDefOrRef();
        var body = new CilMethodBody { ComputeMaxStackOnBuild = false };
        method.CilMethodBody = body;
        var instructions = body.Instructions;
        instructions.Add(CilOpCodes.Ldarg_0);
        if (isLoad)
        {
            instructions.Add(CilOpCodes.Ldarg_1);
            if (hasDefault)
                instructions.Add(CilOpCodes.Ldarg_2);
            else
            {
                body.InitializeLocals = true;
                var defaultValue = new CilLocalVariable(context.GenericParameters[0].ToTypeSignature());
                body.LocalVariables.Add(defaultValue);
                instructions.Add(CilOpCodes.Ldloc, defaultValue);
            }
            instructions.Add(CilOpCodes.Box, genericType);
        }
        else
        {
            instructions.Add(CilOpCodes.Ldarg_1);
            instructions.Add(CilOpCodes.Box, genericType);
            instructions.Add(CilOpCodes.Ldarg_2);
        }
        instructions.Add(CilOpCodes.Ldtoken, genericType);
        instructions.Add(CilOpCodes.Call, getType);
        var target = helper.CreateMemberReference(isLoad ? "LoadSaveValue" : "SaveValue",
            isLoad
                ? MethodSignature.CreateStatic(factory.Object,
                    [factory.String, factory.String, factory.Object, systemType.ToTypeSignature(false)])
                : MethodSignature.CreateStatic(factory.Void,
                    [factory.String, factory.Object, factory.String, systemType.ToTypeSignature(false)]));
        instructions.Add(CilOpCodes.Call, target);
        if (isLoad)
            instructions.Add(CilOpCodes.Unbox_Any, genericType);
        instructions.Add(CilOpCodes.Ret);
        body.MaxStack = body.ComputeMaxStack();
        return true;
    }

    private static bool TryFillPanelGetPanel(MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.DeclaringType?.DeclaringAssembly?.Name != "CastleClashers.Game"
            || context.DeclaringType.FullName != "PanelController" || context.Name != "GetPanel"
            || context.Parameters.Count != 0 || context.GenericParameters.Count != 1)
            return false;

        var enumerable = context.AppContext.AssembliesByName.Values
            .Select(assembly => assembly.GetTypeByFullName("System.Linq.Enumerable"))
            .First(type => type != null)!;
        var ofType = enumerable.Methods.Single(candidate => candidate.Name == "OfType"
            && candidate.IsStatic && candidate.GenericParameters.Count == 1 && candidate.Parameters.Count == 1);
        var first = enumerable.Methods.Single(candidate => candidate.Name == "FirstOrDefault"
            && candidate.IsStatic && candidate.GenericParameters.Count == 1 && candidate.Parameters.Count == 1);
        var argument = context.GenericParameters[0];
        var concreteOfType = new ConcreteGenericMethodAnalysisContext(ofType, [], [argument]);
        var concreteFirst = new ConcreteGenericMethodAnalysisContext(first, [], [argument]);
        var panels = context.DeclaringType.Fields.Single(field => field.Name == "allPanelList");
        var body = new CilMethodBody { ComputeMaxStackOnBuild = false };
        method.CilMethodBody = body;
        body.Instructions.Add(CilOpCodes.Ldarg_0);
        body.Instructions.Add(CilOpCodes.Ldfld, panels.ToFieldDescriptor());
        body.Instructions.Add(CilOpCodes.Call, concreteOfType.ToMethodDescriptor());
        body.Instructions.Add(CilOpCodes.Call, concreteFirst.ToMethodDescriptor());
        body.Instructions.Add(CilOpCodes.Ret);
        body.MaxStack = body.ComputeMaxStack();
        return true;
    }

    private static bool TryFillPanelLifecycle(MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.DeclaringType?.DeclaringAssembly?.Name != "CastleClashers.Game"
            || context.DeclaringType.FullName != "PanelController")
            return false;

        if (context.Name == "SyncFindingMatchPanelAbVariant" && context.Parameters.Count == 0)
        {
            // ponytail: offline recovery keeps the serialized A/B variant; restore
            // remote experiment selection when a matchmaking configuration fixture exists.
            var cached = context.DeclaringType.Fields.Single(field => field.Name == "_fmpVariantsCached");
            var body = new CilMethodBody { ComputeMaxStackOnBuild = false };
            method.CilMethodBody = body;
            body.Instructions.Add(CilOpCodes.Ldarg_0);
            body.Instructions.Add(CilOpCodes.Ldc_I4_1);
            body.Instructions.Add(CilOpCodes.Stfld, cached.ToFieldDescriptor());
            body.Instructions.Add(CilOpCodes.Ret);
            body.MaxStack = body.ComputeMaxStack();
            return true;
        }

        if (context.Name != "InitPanels" || context.Parameters.Count != 0)
            return false;
        var module = method.DeclaringModule!;
        var factory = module.CorLibTypeFactory;
        var scope = CastleRecoveryReference(module);
        var target = scope.CreateTypeReference("CastleRecovery", "InitializationRecovery")
            .CreateMemberReference("InitPanels", MethodSignature.CreateStatic(factory.Void, [factory.Object]));
        var recovered = new CilMethodBody { ComputeMaxStackOnBuild = false };
        method.CilMethodBody = recovered;
        recovered.Instructions.Add(CilOpCodes.Ldarg_0);
        recovered.Instructions.Add(CilOpCodes.Call, target);
        recovered.Instructions.Add(CilOpCodes.Ret);
        recovered.MaxStack = recovered.ComputeMaxStack();
        return true;
    }

    private static bool TryFillPanelNullPredicate(MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.DeclaringType?.DeclaringAssembly?.Name != "CastleClashers.Game"
            || context.DeclaringType.FullName != "PanelController+<>c"
            || context.Name != "<OnInitialized>b__14_0" || context.Parameters.Count != 1)
            return false;
        var body = new CilMethodBody { ComputeMaxStackOnBuild = false };
        method.CilMethodBody = body;
        body.Instructions.Add(CilOpCodes.Ldarg_1);
        body.Instructions.Add(CilOpCodes.Ldnull);
        body.Instructions.Add(CilOpCodes.Ceq);
        body.Instructions.Add(CilOpCodes.Ret);
        body.MaxStack = body.ComputeMaxStack();
        return true;
    }

    private static bool TryFillVoodooTuneProcess(MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.DeclaringType?.DeclaringAssembly?.Name != "CastleClashers.VoodooTune"
            || context.DeclaringType.FullName != "CastleClashers.VoodooTune.VoodooTuneFieldProcessor"
            || context.Name != "Process" || context.Parameters.Count != 1)
            return false;

        // ponytail: offline recovery keeps serialized defaults; restore the
        // callback when a real VoodooTune source fixture is available.
        var body = new CilMethodBody { ComputeMaxStackOnBuild = false };
        method.CilMethodBody = body;
        body.Instructions.Add(CilOpCodes.Ret);
        body.MaxStack = body.ComputeMaxStack();
        return true;
    }

    private static bool TryFillSaveGenericPersistence(MethodDefinition method, MethodAnalysisContext context)
    {
        if (context.DeclaringType?.DeclaringAssembly?.Name != "CastleClashers.Game"
            || context.DeclaringType.FullName != "SaveController" || context.GenericParameters.Count != 1
            || context.Name is not ("Load" or "Save"))
            return false;
        var isLoad = context.Name == "Load";
        if (context.Parameters.Count != 3)
            return false;

        var es3 = context.AppContext.AssembliesByName.Values
            .Select(assembly => assembly.GetTypeByFullName("ES3")).First(type => type != null)!;
        var persistence = es3.Methods.Single(candidate => candidate.Name == context.Name
            && candidate.GenericParameters.Count == 1 && candidate.Parameters.Count == 3
            && candidate.Parameters[0].ParameterType.FullName == "System.String"
            && candidate.Parameters[isLoad ? 1 : 2].ParameterType.FullName == "System.String"
            && candidate.Parameters[isLoad ? 2 : 1].ParameterType is GenericParameterTypeAnalysisContext);
        var concrete = new ConcreteGenericMethodAnalysisContext(persistence, [], [context.GenericParameters[0]]);
        var getFilePath = context.DeclaringType.Methods.Single(candidate => candidate.Name == "GetFilePath"
            && candidate.Parameters.Count == 1);
        var body = new CilMethodBody { ComputeMaxStackOnBuild = false };
        method.CilMethodBody = body;
        var instructions = body.Instructions;
        var done = new CilInstruction(CilOpCodes.Ret);
        if (!isLoad)
        {
            var isClone = context.DeclaringType.Methods.Single(candidate => candidate.Name == "IsCloneEditor"
                && candidate.Parameters.Count == 0);
            instructions.Add(CilOpCodes.Call, isClone.ToMethodDescriptor());
            instructions.Add(CilOpCodes.Brtrue, new CilInstructionLabel(done));
        }
        if (isLoad)
        {
            instructions.Add(CilOpCodes.Ldarg_1);
            instructions.Add(CilOpCodes.Ldarg_0);
            instructions.Add(CilOpCodes.Ldarg_2);
            instructions.Add(CilOpCodes.Call, getFilePath.ToMethodDescriptor());
            instructions.Add(CilOpCodes.Ldarg_3);
        }
        else
        {
            instructions.Add(CilOpCodes.Ldarg_1);
            instructions.Add(CilOpCodes.Ldarg_2);
            instructions.Add(CilOpCodes.Ldarg_0);
            instructions.Add(CilOpCodes.Ldarg_3);
            instructions.Add(CilOpCodes.Call, getFilePath.ToMethodDescriptor());
        }
        instructions.Add(CilOpCodes.Call, concrete.ToMethodDescriptor());
        if (!isLoad)
        {
            instructions.Add(CilOpCodes.Ldarg_0);
            instructions.Add(CilOpCodes.Ldarg_3);
            var notify = context.DeclaringType.Methods.Single(candidate => candidate.Name == "NotifyCloudSaveChanged"
                && candidate.Parameters.Count == 1);
            instructions.Add(CilOpCodes.Call, notify.ToMethodDescriptor());
        }
        instructions.Add(done);
        body.MaxStack = body.ComputeMaxStack();
        return true;
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
