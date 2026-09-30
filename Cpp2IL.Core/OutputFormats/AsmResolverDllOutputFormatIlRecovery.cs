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
            RestoreFieldLikeEventBackingFields(context);
            RestoreInternalsVisibleTo(assemblies);
            // The injected friend-assembly attributes introduce their own
            // framework-type references; re-run the (emit-if-missing) pass.
            FrameworkSurfaceTypes.EmitMissing(assemblies);
            // After every widening the references above applied, re-assert the
            // accessibility-consistency invariants on the final emitted flags.
            MemberAccessibility.FixupEmittedVisibility(context);
            return assemblies;
        }
        finally
        {
            AccessibilityExtensions.EmittedInternalsAreShared = false;
        }
    }

    // The original C# compiles a field-like `event T E` to a private backing
    // field `E` plus public add_/remove_ accessors, and il2cpp metadata keeps
    // that private declaration. Body emission widens any field a lifted
    // instruction names to public (MemberAccessibility.EnsureAccessible), so a
    // backing field only ever touched inside its own declaring type - which
    // private access already permits - leaves the stub assembly as a public
    // field `E` sitting next to `event E`: two members with one name, which
    // decompilers refuse to fold back into an event and C# rejects as a
    // duplicate definition (CS0102). Restore the declared access when every
    // emitted reference stays inside the declaring type's private scope; a
    // wider access stays when a foreign body proved a direct (inlined) access.
    internal static void RestoreFieldLikeEventBackingFields(ApplicationAnalysisContext context)
    {
        var candidates = new List<(FieldDefinition Field, FieldAttributes DeclaredAccess)>();
        var byDefinition = new Dictionary<FieldDefinition, int>();
        var byMemberReferenceKey = new Dictionary<(string DeclaringType, string Name), List<int>>();
        foreach (var assemblyContext in context.Assemblies)
            foreach (var typeContext in assemblyContext.Types)
            {
                if (typeContext.Events.Count == 0)
                    continue;
                foreach (var eventContext in typeContext.Events)
                    foreach (var fieldContext in typeContext.Fields)
                    {
                        if (fieldContext.Name != eventContext.Name
                            || fieldContext.IsStatic != eventContext.IsStatic
                            || fieldContext.GetExtraData<FieldDefinition>("AsmResolverField") is not { } field
                            || field.DeclaringType is null)
                            continue;
                        var declaredAccess = (FieldAttributes)fieldContext.Visibility;
                        if ((field.Attributes & FieldAttributes.FieldAccessMask) == declaredAccess)
                            continue; // never promoted - nothing to restore
                        var index = candidates.Count;
                        candidates.Add((field, declaredAccess));
                        byDefinition[field] = index;
                        var key = (field.DeclaringType.FullName, field.Name?.ToString() ?? "");
                        if (!byMemberReferenceKey.TryGetValue(key, out var list))
                            byMemberReferenceKey[key] = list = [];
                        list.Add(index);
                    }
            }

        if (candidates.Count == 0)
            return;

        // Every body that touches a candidate decides whether the field must
        // stay widened. References arrive either as the FieldDefinition itself
        // or - for generic-instance receivers and cross-assembly uses - as a
        // MemberReference naming the declaring type.
        var referencingTypes = new HashSet<TypeDefinition>[candidates.Count];
        foreach (var assemblyContext in context.Assemblies)
            if (assemblyContext.GetExtraData<AssemblyDefinition>("AsmResolverAssembly") is { } assembly)
                foreach (var module in assembly.Modules)
                    foreach (var type in module.GetAllTypes())
                        foreach (var method in type.Methods)
                        {
                            if (method.DeclaringType is not { } accessingType
                                || method.CilMethodBody is not { } body)
                                continue;
                            foreach (var instruction in body.Instructions)
                                switch (instruction.Operand)
                                {
                                    case FieldDefinition field
                                        when byDefinition.TryGetValue(field, out var index):
                                        (referencingTypes[index] ??= []).Add(accessingType);
                                        break;
                                    case MemberReference { Signature: FieldSignature, Name: { } name } reference
                                        when byMemberReferenceKey.TryGetValue(
                                                (DeclaringTypeName(reference.DeclaringType) ?? "", name.ToString()),
                                                out var indices):
                                        var scopeName = DeclaringAssemblyName(reference.DeclaringType);
                                        foreach (var index in indices)
                                            if (scopeName is null
                                                || scopeName == candidates[index].Field.DeclaringModule?.Assembly?.Name)
                                                (referencingTypes[index] ??= []).Add(accessingType);
                                        break;
                                }
                        }

        var restored = 0;
        for (var i = 0; i < candidates.Count; i++)
        {
            var (field, declaredAccess) = candidates[i];
            if (referencingTypes[i] is { } accessors
                && !accessors.All(accessor => WithinPrivateScope(accessor, field.DeclaringType!)))
                continue;
            field.Attributes = (field.Attributes & ~FieldAttributes.FieldAccessMask) | declaredAccess;
            restored++;
        }

        if (restored > 0)
            Logger.InfoNewline($"Restored declared access on {restored} field-like event backing field(s).", "DllOutput");
    }

    // A private member is reachable only from its own declaring type and from
    // types nested inside it, at any depth.
    private static bool WithinPrivateScope(TypeDefinition accessing, TypeDefinition declaring)
    {
        for (var type = accessing; type is not null; type = type.DeclaringType)
            if (ReferenceEquals(type, declaring))
                return true;
        return false;
    }

    // MemberReferences on a generic instantiation carry the field's declaring
    // type as a TypeSpecification; unwrap to the underlying definition's name.
    private static string? DeclaringTypeName(ITypeDefOrRef? declaringType)
    {
        while (declaringType is TypeSpecification { Signature: GenericInstanceTypeSignature { GenericType: { } generic } })
            declaringType = generic;
        return declaringType?.FullName;
    }

    private static string? DeclaringAssemblyName(ITypeDefOrRef? declaringType)
    {
        while (declaringType is TypeSpecification { Signature: GenericInstanceTypeSignature { GenericType: { } generic } })
            declaringType = generic;
        return declaringType switch
        {
            TypeDefinition definition => definition.DeclaringModule?.Assembly?.Name?.ToString(),
            TypeReference { Scope: AssemblyReference scope } => scope.Name?.ToString(),
            TypeReference { Scope: TypeReference parent } => DeclaringAssemblyName(parent),
            TypeReference { Scope: ModuleDefinition module } => module.Assembly?.Name?.ToString(),
            _ => null,
        };
    }

    // il2cpp metadata does not preserve assembly-level attributes, so recovered
    // assemblies lose the InternalsVisibleTo grants the originals compiled
    // against - Unity package internals cross assembly boundaries constantly
    // (internal types in fields, methods, casts). The verifier resolves the real
    // hierarchy and rejects those references as invisible. Restoring the grant
    // for every sibling recreates that access, but a blanket grant also exposes
    // the internal polyfill types many packages compile privately (for example
    // the NotNullWhenAttribute copies NuGet libraries carry) to consumers that
    // never touched them - a consumer naming the same type through the runtime
    // library then sees two definitions and the compile reports duplicate-type
    // errors. Emit a grant only where the friend's own emitted metadata touches
    // the grantor's internals: the reference is the evidence the original
    // assembly carried one.
    private static void RestoreInternalsVisibleTo(List<AssemblyDefinition> assemblies)
    {
        var exercisedInternals = CollectExercisedInternals(assemblies);

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
            .Select(a => (SimpleName: a.Name!.ToString(), Name: FriendName(a), Keyed: a.PublicKey is { Length: > 0 }))
            .Distinct()
            .ToList();
        foreach (var assembly in assemblies)
        {
            var module = assembly.Modules.FirstOrDefault();
            if (module == null || assembly.Name is null)
                continue;
            if (!exercisedInternals.TryGetValue(assembly, out var exercised) || exercised.Count == 0)
                continue;
            // A strong-named grantor may only name strong-named friends - an
            // unsigned name in InternalsVisibleTo is rejected outright when
            // the signed output is recompiled (CS1726), and the original build
            // could not have carried the grant either.
            var grantorKeyed = assembly.PublicKey is { Length: > 0 };
            var factory = module.CorLibTypeFactory;
            var ivtCtor = factory.CorLibScope
                .CreateTypeReference("System.Runtime.CompilerServices", "InternalsVisibleToAttribute")
                .CreateMemberReference(".ctor",
                    MethodSignature.CreateInstance(factory.Void, [factory.String]));
            var self = assembly.Name.ToString() + ",";
            foreach (var (simpleName, friend, friendKeyed) in friends)
            {
                if (!exercised.Contains(simpleName))
                    continue;
                if (grantorKeyed && !friendKeyed)
                    continue;
                if (friend.StartsWith(self, StringComparison.Ordinal))
                    continue;
                var signature = new CustomAttributeSignature(
                    new CustomAttributeArgument(factory.String, friend));
                assembly.CustomAttributes.Add(new CustomAttribute(ivtCtor, signature));
            }
        }
    }

    // For each emitted assembly, the set of consumer assembly names whose
    // emitted metadata references a type or member the consumer could only see
    // through an InternalsVisibleTo grant: member/signature references naming
    // internal (or family-and-assembly / protected-internal) members and types,
    // type forwards of internal types, and virtual overrides whose kept access
    // relies on seeing the base member's internal half (implicit overrides
    // leave no reference of their own). References the emission-time access
    // gates widened to public need no grant; every remaining internal-facing
    // edge is evidence the original assembly carried one.
    private static Dictionary<AssemblyDefinition, HashSet<string>> CollectExercisedInternals(
        List<AssemblyDefinition> assemblies)
    {
        var needed = new Dictionary<AssemblyDefinition, HashSet<string>>();
        var typeCache = new Dictionary<ITypeDefOrRef, TypeDefinition?>();
        var memberCache = new Dictionary<IMemberDescriptor, IMemberDefinition?>();
        var exportedTypeMaps = new Dictionary<AssemblyDefinition, Dictionary<string, TypeDefinition>>();

        foreach (var consumer in assemblies)
        {
            if (consumer.Name?.ToString() is not { } consumerName)
                continue;

            void Require(AssemblyDefinition? owner)
            {
                if (owner is null || ReferenceEquals(owner, consumer))
                    return;
                if (!needed.TryGetValue(owner, out var set))
                    needed[owner] = set = new HashSet<string>(StringComparer.Ordinal);
                set.Add(consumerName);
            }

            foreach (var module in consumer.Modules)
            {
                var runtimeContext = module.RuntimeContext;

                TypeDefinition? ResolveType(ITypeDefOrRef? type)
                {
                    switch (type)
                    {
                        case null:
                            return null;
                        case TypeDefinition definition:
                            return definition;
                    }
                    if (!typeCache.TryGetValue(type, out var resolved))
                    {
                        resolved = type.Resolve(runtimeContext, out var result) == ResolutionStatus.Success
                            ? result
                            : null;
                        typeCache[type] = resolved;
                    }
                    return resolved;
                }

                IMemberDefinition? ResolveMember(IMemberDescriptor member)
                {
                    if (member is MethodSpecification { Method: { } specificationMethod })
                        member = specificationMethod;
                    if (member is IMemberDefinition definition)
                        return definition;
                    if (member is not MemberReference reference)
                        return null;
                    if (!memberCache.TryGetValue(reference, out var resolved))
                    {
                        resolved = reference.TryResolve(runtimeContext, out var result) ? result : null;
                        memberCache[reference] = resolved;
                    }
                    return resolved;
                }

                void NoteType(ITypeDescriptor? type)
                {
                    foreach (var leaf in EmittedTypeLeaves(type))
                        if (ResolveType(leaf) is { } definition && TypeNeedsFriendAccess(definition))
                            Require(definition.DeclaringModule?.Assembly);
                }

                void NoteSignature(TypeSignature? signature)
                {
                    foreach (var leaf in EmittedSignatureLeaves(signature))
                        NoteType(leaf);
                }

                void NoteMember(IMemberDescriptor? member)
                {
                    switch (member)
                    {
                        case null:
                            return;
                        case MethodSpecification specification:
                            if (specification.Signature is { } genericSignature)
                                foreach (var argument in genericSignature.TypeArguments)
                                    NoteSignature(argument);
                            NoteMember(specification.Method);
                            return;
                    }
                    NoteType(member.DeclaringType);
                    if (member is MemberReference { Signature: MethodSignature methodSignature })
                    {
                        NoteSignature(methodSignature.ReturnType);
                        foreach (var parameterType in methodSignature.ParameterTypes)
                            NoteSignature(parameterType);
                    }
                    else if (member is MemberReference { Signature: FieldSignature fieldSignature })
                    {
                        NoteSignature(fieldSignature.FieldType);
                    }
                    var resolved = ResolveMember(member);
                    if (resolved?.DeclaringType?.DeclaringModule?.Assembly is { } owner
                        && (TypeNeedsFriendAccess(resolved.DeclaringType) || MemberNeedsFriendAccess(resolved)))
                        Require(owner);
                }

                void NoteAttributes(IEnumerable<CustomAttribute> attributes)
                {
                    foreach (var attribute in attributes)
                    {
                        NoteMember(attribute.Constructor);
                        if (attribute.Signature is not { } signature)
                            continue;
                        foreach (var argument in signature.FixedArguments)
                            NoteArgument(argument);
                        foreach (var named in signature.NamedArguments)
                        {
                            NoteSignature(named.ArgumentType);
                            NoteArgument(named.Argument);
                        }
                    }
                }

                void NoteArgument(CustomAttributeArgument argument)
                {
                    NoteSignature(argument.ArgumentType);
                    NoteArgumentValue(argument.Element);
                    if (argument.Elements is { } elements)
                        foreach (var element in elements)
                            NoteArgumentValue(element);
                }

                void NoteArgumentValue(object? value)
                {
                    switch (value)
                    {
                        case TypeSignature signature:
                            NoteSignature(signature);
                            break;
                        case ITypeDefOrRef type:
                            NoteType(type);
                            break;
                        case BoxedArgument boxed:
                            NoteSignature(boxed.Type);
                            NoteArgumentValue(boxed.Value);
                            break;
                        case CustomAttributeArgument nested:
                            NoteArgument(nested);
                            break;
                        case IEnumerable<object?> sequence:
                            foreach (var element in sequence)
                                NoteArgumentValue(element);
                            break;
                    }
                }

                foreach (var type in module.GetAllTypes())
                {
                    NoteType(type.BaseType);
                    foreach (var @interface in type.Interfaces)
                        NoteType(@interface.Interface);
                    foreach (var genericParameter in type.GenericParameters)
                    {
                        foreach (var constraint in genericParameter.Constraints)
                            NoteType(constraint.Constraint);
                        NoteAttributes(genericParameter.CustomAttributes);
                    }
                    foreach (var implementation in type.MethodImplementations)
                    {
                        NoteMember(implementation.Declaration);
                        NoteMember(implementation.Body);
                    }
                    NoteAttributes(type.CustomAttributes);

                    foreach (var field in type.Fields)
                    {
                        if (field.Signature is { } fieldSignature)
                            NoteSignature(fieldSignature.FieldType);
                        NoteAttributes(field.CustomAttributes);
                    }

                    foreach (var property in type.Properties)
                    {
                        if (property.Signature is { } propertySignature)
                        {
                            NoteSignature(propertySignature.ReturnType);
                            foreach (var parameterType in propertySignature.ParameterTypes)
                                NoteSignature(parameterType);
                        }
                        NoteAttributes(property.CustomAttributes);
                    }

                    foreach (var @event in type.Events)
                    {
                        NoteType(@event.EventType);
                        NoteAttributes(@event.CustomAttributes);
                    }

                    foreach (var method in type.Methods)
                    {
                        if (method.Signature is { } methodSignature)
                        {
                            NoteSignature(methodSignature.ReturnType);
                            foreach (var parameterType in methodSignature.ParameterTypes)
                                NoteSignature(parameterType);
                        }
                        foreach (var genericParameter in method.GenericParameters)
                        {
                            foreach (var constraint in genericParameter.Constraints)
                                NoteType(constraint.Constraint);
                            NoteAttributes(genericParameter.CustomAttributes);
                        }
                        NoteAttributes(method.CustomAttributes);
                        foreach (var parameter in method.ParameterDefinitions)
                            NoteAttributes(parameter.CustomAttributes);

                        // A virtual member reusing a base slot is an implicit
                        // override: it references no base member, but keeping an
                        // internal-reliant access still needs the grant it proves.
                        if (method.IsVirtual && !method.IsStatic && !method.IsNewSlot)
                            for (var scope = type.BaseType; scope is not null;)
                            {
                                var baseDefinition = ResolveType(scope);
                                if (baseDefinition is null)
                                    break;
                                scope = baseDefinition.BaseType;
                                if (baseDefinition.DeclaringModule?.Assembly is not { } owner)
                                    continue;
                                foreach (var candidate in baseDefinition.Methods)
                                {
                                    if (!candidate.IsVirtual || candidate.IsStatic
                                        || candidate.Name?.Value != method.Name?.Value)
                                        continue;
                                    var baseAccess = (int)(candidate.Attributes & MethodAttributes.MemberAccessMask);
                                    var overrideAccess = (int)(method.Attributes & MethodAttributes.MemberAccessMask);
                                    // A protected-internal override relies on the
                                    // internal half of a protected-internal base;
                                    // an assembly/family-and-assembly base is only
                                    // visible (and overridable) through the grant.
                                    if (baseAccess is 2 or 3 || baseAccess == 5 && overrideAccess == 5)
                                        Require(owner);
                                }
                            }

                        if (method.CilMethodBody is not { } body)
                            continue;
                        foreach (var variable in body.LocalVariables)
                            NoteSignature(variable.VariableType);
                        foreach (var handler in body.ExceptionHandlers)
                            NoteType(handler.ExceptionType);
                        foreach (var instruction in body.Instructions)
                            switch (instruction.Operand)
                            {
                                case ITypeDefOrRef operandType:
                                    NoteType(operandType);
                                    break;
                                case IMemberDescriptor member:
                                    NoteMember(member);
                                    break;
                                case StandAloneSignature { Signature: MethodSignature standAlone }:
                                    NoteSignature(standAlone.ReturnType);
                                    foreach (var parameterType in standAlone.ParameterTypes)
                                        NoteSignature(parameterType);
                                    break;
                            }
                    }
                }

                NoteAttributes(module.CustomAttributes);
                NoteAttributes(consumer.CustomAttributes);

                // An exported type forwarding an internal type is only
                // nameable by the consumer through the grant.
                foreach (var exported in module.ExportedTypes)
                {
                    if (exported.Implementation is not AssemblyReference { Name: { } targetName })
                        continue;
                    var owner = assemblies.FirstOrDefault(a => a.Name?.ToString() == targetName.ToString());
                    if (owner is null || ReferenceEquals(owner, consumer))
                        continue;
                    if (!exportedTypeMaps.TryGetValue(owner, out var fullNameMap))
                    {
                        fullNameMap = owner.Modules
                            .SelectMany(m => m.GetAllTypes())
                            .GroupBy(t => t.FullName)
                            .ToDictionary(g => g.Key, g => g.First(), StringComparer.Ordinal);
                        exportedTypeMaps[owner] = fullNameMap;
                    }
                    if (exported.FullName is { } fullName
                        && fullNameMap.TryGetValue(fullName, out var forwarded)
                        && TypeNeedsFriendAccess(forwarded))
                        Require(owner);
                }
            }
        }
        return needed;
    }

    // The metadata types a descriptor can actually name: a specification's
    // signature leaves and the type itself. Resolution of a nested type's own
    // declaring chain happens inside TypeNeedsFriendAccess.
    private static IEnumerable<ITypeDefOrRef> EmittedTypeLeaves(ITypeDescriptor? type) => type switch
    {
        null => [],
        TypeSpecification specification => EmittedSignatureLeaves(specification.Signature),
        TypeSignature signature => EmittedSignatureLeaves(signature),
        ITypeDefOrRef defOrRef => [defOrRef],
        _ => [],
    };

    private static IEnumerable<ITypeDefOrRef> EmittedSignatureLeaves(TypeSignature? signature)
    {
        switch (signature)
        {
            case null or GenericParameterSignature:
                yield break;
            case CustomModifierTypeSignature modifier:
                if (modifier.ModifierType is { } modifierType)
                    yield return modifierType;
                foreach (var leaf in EmittedSignatureLeaves(modifier.BaseType))
                    yield return leaf;
                yield break;
            case GenericInstanceTypeSignature genericInstance:
                if (genericInstance.GenericType is { } genericType)
                    yield return genericType;
                foreach (var argument in genericInstance.TypeArguments)
                    foreach (var leaf in EmittedSignatureLeaves(argument))
                        yield return leaf;
                yield break;
            case TypeSpecificationSignature specification:
                foreach (var leaf in EmittedTypeLeaves(specification.DeclaringType))
                    yield return leaf;
                foreach (var leaf in EmittedSignatureLeaves(specification.BaseType))
                    yield return leaf;
                yield break;
            case TypeDefOrRefSignature typeDefOrRef:
                if (typeDefOrRef.Type is { } type)
                    yield return type;
                yield break;
            case FunctionPointerTypeSignature functionPointer:
                if (functionPointer.Signature is { } methodSignature)
                {
                    foreach (var leaf in EmittedSignatureLeaves(methodSignature.ReturnType))
                        yield return leaf;
                    foreach (var parameterType in methodSignature.ParameterTypes)
                        foreach (var leaf in EmittedSignatureLeaves(parameterType))
                            yield return leaf;
                }
                yield break;
        }
    }

    // Whether a reference to the type could only bind through an
    // InternalsVisibleTo grant: internal at the type or at any enclosing scope.
    // A private link in the chain makes the type unnameable either way.
    private static bool TypeNeedsFriendAccess(TypeDefinition type)
    {
        for (var current = type; current is not null; current = current.DeclaringType)
        {
            if (!current.IsNested)
                return current.IsNotPublic;
            if (current.IsNestedAssembly || current.IsNestedFamilyAndAssembly || current.IsNestedFamilyOrAssembly)
                return true;
            if (current.IsNestedPrivate)
                return false;
        }
        return false;
    }

    // Internal access levels (family-and-assembly, assembly, protected
    // internal's internal half) share the same low bits on methods and fields.
    private static bool MemberNeedsFriendAccess(IMemberDefinition member) => member switch
    {
        MethodDefinition method => (int)(method.Attributes & MethodAttributes.MemberAccessMask) is 2 or 3 or 5,
        FieldDefinition field => (int)(field.Attributes & FieldAttributes.FieldAccessMask) is 2 or 3 or 5,
        _ => false,
    };

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
            DecompilerMemberAccessRewrites.Apply(methodDefinition);
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

            if (TryFillClosureSingletonConstructor(methodDefinition, methodContext)
                || TryFillFieldLikeEvent(methodDefinition, methodContext))
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
