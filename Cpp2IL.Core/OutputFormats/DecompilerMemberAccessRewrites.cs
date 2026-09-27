using System.Linq;
using AsmResolver;
using AsmResolver.DotNet;
using AsmResolver.PE.DotNet.Cil;

namespace Cpp2IL.Core.OutputFormats;

/// <summary>
/// Post-pass over a finished method body that re-expresses recovered member
/// accesses whose operand names a member no C# identifier can spell. The lifted
/// code names storage directly; where a decompiler cannot print that name the
/// recovered source cannot compile, even though the access itself is honest.
///
/// Two spellings are rewritten:
/// <list type="bullet">
/// <item><c>ldfld</c>/<c>stfld</c> on an enum's <c>value__</c> field. The receiver
/// is already a managed pointer to the enum, and an enum is interchangeable with
/// its underlying type, so the same stack shape is produced by
/// <c>ldobj</c>/<c>stobj</c> of the enum itself — which decompiles as the enum
/// value rather than the unprintable field name.</item>
/// <item>field access on a <c>&lt;X&gt;k__BackingField</c> whose declaring type
/// still carries property <c>X</c> with the matching accessor. IL2CPP inline-
/// expands auto-property accessors, so the access is the accessor call the
/// original C# made; re-emitting it as <c>call</c>/<c>callvirt</c> recovers
/// <c>o.X</c>/<c>o.X = v</c>. The rewrite is skipped when the accessor does not
/// exist or is not accessible from the emitting method — calling an
/// inaccessible member would merely trade one compile error for another — and
/// inside the accessor itself, where the field access is the accessor's own
/// storage.</item>
/// </list>
/// </summary>
internal static class DecompilerMemberAccessRewrites
{
    private const string BackingFieldSuffix = ">k__BackingField";

    public static void Apply(MethodDefinition method)
    {
        if (method.CilMethodBody is not { } body || method.DeclaringModule is not { } module)
            return;
        var runtimeContext = module.RuntimeContext;
        var instructions = body.Instructions;
        for (var i = 0; i < instructions.Count; i++)
        {
            var instruction = instructions[i];
            if (instruction.Operand is not IFieldDescriptor field)
                continue;
            switch (instruction.OpCode.Code)
            {
                case CilCode.Ldfld:
                    if (!TryRewriteEnumUnderlyingAccess(field, instruction, runtimeContext, load: true))
                        RewriteBackingFieldAccess(method, field, instruction, runtimeContext, load: true);
                    break;
                case CilCode.Stfld:
                    if (!TryRewriteEnumUnderlyingAccess(field, instruction, runtimeContext, load: false))
                        RewriteBackingFieldAccess(method, field, instruction, runtimeContext, load: false);
                    break;
                case CilCode.Ldsfld:
                    RewriteBackingFieldAccess(method, field, instruction, runtimeContext, load: true);
                    break;
                case CilCode.Stsfld:
                    RewriteBackingFieldAccess(method, field, instruction, runtimeContext, load: false);
                    break;
            }
        }
    }

    private static bool TryRewriteEnumUnderlyingAccess(IFieldDescriptor field, CilInstruction instruction,
        RuntimeContext? runtimeContext, bool load)
    {
        if (field.Name?.Value != "value__" || field.DeclaringType is not ITypeDefOrRef declaringType)
            return false;
        if (!TryResolveType(declaringType, runtimeContext, out var declaringDef) || declaringDef is not { IsEnum: true })
            return false;
        instruction.OpCode = load ? CilOpCodes.Ldobj : CilOpCodes.Stobj;
        instruction.Operand = declaringType;
        return true;
    }

    private static void RewriteBackingFieldAccess(MethodDefinition method, IFieldDescriptor field,
        CilInstruction instruction, RuntimeContext? runtimeContext, bool load)
    {
        var name = field.Name?.Value;
        if (name == null || !name.StartsWith('<') || !name.EndsWith(BackingFieldSuffix))
            return;
        var propertyName = name.Substring(1, name.Length - 1 - BackingFieldSuffix.Length);
        // The field reference may be scoped to a derived type while the field
        // and its auto-property live on a base; find the property by walking
        // the scope's hierarchy rather than trusting field resolution.
        if (field.DeclaringType is not ITypeDefOrRef scopeRef
            || !TryResolveType(scopeRef, runtimeContext, out var scopeDef) || scopeDef == null)
            return;
        var staticAccess = instruction.OpCode.Code is CilCode.Ldsfld or CilCode.Stsfld;
        for (var declaringType = scopeDef; declaringType != null; declaringType = ResolveBase(declaringType, runtimeContext))
        {
            var property = declaringType.Properties.FirstOrDefault(p => p.Name?.Value == propertyName);
            if (property == null)
                continue;
            var accessor = load ? property.GetMethod : property.SetMethod;
            // The accessor's own body must keep its field access, or it would
            // recurse; a static/instance mismatch means the property does not
            // describe this field.
            if (accessor != null && accessor != method && accessor.IsStatic == staticAccess
                && AccessorCallableFrom(accessor, method, declaringType, runtimeContext))
            {
                instruction.OpCode = accessor.IsStatic || declaringType.IsValueType
                    ? CilOpCodes.Call : CilOpCodes.Callvirt;
                instruction.Operand = scopeRef is IMemberRefParent scope
                        && !ReferenceEquals(scope, accessor.DeclaringType)
                    ? scope.CreateMemberReference(accessor.Name!, accessor.Signature!)
                    : accessor;
            }
            return;
        }
    }

    private static TypeDefinition? ResolveBase(TypeDefinition type, RuntimeContext? runtimeContext)
    {
        if (type.BaseType is TypeDefinition def)
            return def;
        if (type.BaseType is { } baseRef
            && TryResolveType(baseRef, runtimeContext, out var resolved))
            return resolved;
        return null;
    }

    // IsAccessibleFromType does not model the C# widening that lets a type
    // nested inside a derived class call a protected member through a receiver
    // typed at that derived class or below. The field reference's scope names
    // the field's declaring type, not the receiver's static type, so it cannot
    // discriminate that rule — but the recovered program compiled originally,
    // so an enclosing derived type is evidence the receiver shape was legal.
    private static bool AccessorCallableFrom(MethodDefinition accessor, MethodDefinition caller,
        TypeDefinition declaringType, RuntimeContext? runtimeContext)
    {
        if (accessor.DeclaringType == null || caller.DeclaringType == null)
            return false;
        if (accessor.IsAccessibleFromType(caller.DeclaringType, runtimeContext))
            return true;
        var family = accessor.IsFamily || accessor.IsFamilyOrAssembly
            || (accessor.IsFamilyAndAssembly
                && Equals(accessor.DeclaringModule, caller.DeclaringModule));
        if (!family)
            return false;
        for (var enclosing = caller.DeclaringType; enclosing != null; enclosing = enclosing.DeclaringType)
            if (DerivesFrom(enclosing, declaringType, runtimeContext))
                return true;
        return false;
    }

    private static bool DerivesFrom(TypeDefinition type, TypeDefinition candidate,
        RuntimeContext? runtimeContext)
    {
        for (var t = ResolveBase(type, runtimeContext); t != null; t = ResolveBase(t, runtimeContext))
            if (Equals(t, candidate))
                return true;
        return false;
    }

    private static bool TryResolveType(ITypeDefOrRef type, RuntimeContext? runtimeContext, out TypeDefinition? resolved)
    {
        if (type is TypeDefinition definition)
        {
            resolved = definition;
            return true;
        }
        resolved = type.Resolve(runtimeContext, out var result) == ResolutionStatus.Success ? result : null;
        return resolved != null;
    }
}
