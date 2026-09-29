using System.Collections.Generic;
using System.Linq;
using AsmResolver;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.DotNet.Signatures;

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
/// value rather than the unprintable field name. The same applies to
/// <c>ldflda</c>: <c>&amp;e.value__</c> is <c>&amp;e</c>, so the retagging
/// <c>ldflda</c> is dropped and its <c>ldobj</c>/<c>stobj</c>/<c>ldind</c>/
/// <c>stind</c> consumer retargets to the enum.</item>
/// <item><c>ldflda</c>/<c>ldsflda</c> on a <c>&lt;X&gt;k__BackingField</c>.
/// Recovered code takes the backing field's address to feed the load or store
/// of a member access chain (an enum-typed property's payload, a struct
/// property's member). When the immediate consumer moves the field's own
/// value (<c>ldobj</c>/<c>stobj</c>/<c>ldind</c>/<c>stind</c> of the field
/// type) the pair collapses to the accessor call that produced the same
/// stack shape originally; when it reads a member of the field's value type
/// (<c>ldfld</c> of a member declared on that type) the call still works
/// because <c>ldfld</c> accepts a by-value struct. Other consumers need the
/// managed pointer itself, which no accessor can produce, so the ldflda
/// stays and the site's diagnostic or emitted member name stands.</item>
/// <item>field access on a <c>&lt;X&gt;k__BackingField</c> whose declaring type
/// still carries property <c>X</c> with the matching accessor. IL2CPP inline-
/// expands auto-property accessors, so the access is the accessor call the
/// original C# made; re-emitting it as <c>call</c>/<c>callvirt</c> recovers
/// <c>o.X</c>/<c>o.X = v</c>. The rewrite is skipped when the accessor does not
/// exist or is not accessible from the emitting method — calling an
/// inaccessible member would merely trade one compile error for another — and
/// inside the accessor itself, where the field access is the accessor's own
/// storage.</item>
/// <item><c>unbox T</c> immediately followed by <c>ldobj T</c>. The pair is
/// exactly <c>unbox.any T</c> — assert the reference is a boxed T, push its
/// value — and only exists because <c>unbox</c> serves every managed-pointer
/// consumer. Decompilers print <c>unbox.any</c> as the unboxing cast but have
/// no C# spelling for the intermediate <c>&amp;T</c>, so the fused form is the
/// only one whose printed operand types compile.</item>
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
                case CilCode.Ldflda:
                case CilCode.Ldsflda:
                    TryRewriteEnumUnderlyingAddress(field, instruction, instructions, i,
                        runtimeContext);
                    TryRewriteBackingFieldAddress(method, field, instruction, instructions, i,
                        runtimeContext);
                    break;
            }
        }
        FuseUnboxLoad(body);
    }

    // `unbox T; ldobj T` -> `unbox.any T`. Removing an instruction is only
    // safe when neither instruction sits on a jump target or a protected-block
    // boundary, so those positions are collected first; a body whose labels
    // cannot all be resolved to instructions (an offset label) keeps the pair.
    private static void FuseUnboxLoad(CilMethodBody body)
    {
        var instructions = body.Instructions;
        var jumpTargets = new HashSet<CilInstruction>();
        var foreignLabel = false;
        foreach (var instruction in instructions)
            switch (instruction.Operand)
            {
                case CilInstructionLabel label:
                    if (label.Instruction != null)
                        jumpTargets.Add(label.Instruction);
                    else
                        foreignLabel = true;
                    break;
                case CilInstruction target:
                    jumpTargets.Add(target);
                    break;
                case IEnumerable<ICilLabel> labels:
                    foreach (var label in labels)
                        if (label is CilInstructionLabel instructionLabel && instructionLabel.Instruction != null)
                            jumpTargets.Add(instructionLabel.Instruction);
                        else
                            foreignLabel = true;
                    break;
                case ICilLabel:
                    foreignLabel = true;
                    break;
            }
        foreach (var handler in body.ExceptionHandlers)
            foreach (var edge in new ICilLabel?[]
                     {
                         handler.TryStart, handler.TryEnd, handler.HandlerStart,
                         handler.HandlerEnd, handler.FilterStart
                     })
                switch (edge)
                {
                    case CilInstructionLabel label:
                        if (label.Instruction != null)
                            jumpTargets.Add(label.Instruction);
                        else
                            foreignLabel = true;
                        break;
                    case not null:
                        foreignLabel = true;
                        break;
                }
        if (foreignLabel)
            return;
        for (var i = 0; i < instructions.Count - 1; i++)
        {
            var unbox = instructions[i];
            var ldobj = instructions[i + 1];
            if (unbox.OpCode.Code != CilCode.Unbox || ldobj.OpCode.Code != CilCode.Ldobj
                || jumpTargets.Contains(unbox) || jumpTargets.Contains(ldobj))
                continue;
            if (unbox.Operand is not ITypeDefOrRef unboxed
                || ldobj.Operand is not ITypeDefOrRef loaded
                || unboxed.FullName != loaded.FullName)
                continue;
            unbox.OpCode = CilOpCodes.Unbox_Any;
            instructions.RemoveAt(i + 1);
            i--;
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

    // &e.value__ is the same address as &e: value__ is the enum's only instance
    // member, at offset zero, so the ldflda exists only to retag the managed
    // pointer to the underlying type. An immediately following ldobj, stobj,
    // ldind or stind consumes that pointer to move exactly the enum's storage -
    // the same bytes move under the enum's own name when the consumer retargets
    // to the enum and the retagging ldflda is dropped.
    private static void TryRewriteEnumUnderlyingAddress(IFieldDescriptor field, CilInstruction instruction,
        CilInstructionCollection instructions, int index, RuntimeContext? runtimeContext)
    {
        if (field.Name?.Value != "value__" || field.DeclaringType is not ITypeDefOrRef declaringType)
            return;
        if (!TryResolveType(declaringType, runtimeContext, out var declaringDef) || declaringDef is not { IsEnum: true })
            return;
        if (index + 1 >= instructions.Count)
            return;
        var consumer = instructions[index + 1];
        var load = consumer.OpCode.Code switch
        {
            CilCode.Ldobj or CilCode.Ldind_I or CilCode.Ldind_I1 or CilCode.Ldind_I2
                or CilCode.Ldind_I4 or CilCode.Ldind_I8 or CilCode.Ldind_U1 or CilCode.Ldind_U2
                or CilCode.Ldind_U4 or CilCode.Ldind_R4 or CilCode.Ldind_R8 or CilCode.Ldind_Ref => true,
            CilCode.Stobj or CilCode.Stind_I or CilCode.Stind_I1 or CilCode.Stind_I2
                or CilCode.Stind_I4 or CilCode.Stind_I8 or CilCode.Stind_R4 or CilCode.Stind_R8
                or CilCode.Stind_Ref => false,
            _ => (bool?)null,
        };
        if (load == null)
            return;
        instruction.OpCode = CilOpCodes.Nop;
        instruction.Operand = null;
        consumer.OpCode = load.Value ? CilOpCodes.Ldobj : CilOpCodes.Stobj;
        consumer.Operand = declaringType;
    }

    // &x.<P>k__BackingField feeds the consumers a nested-path load or store
    // emits: the field's own value (ldobj/stobj or the matching ldind/stind)
    // or a member read of the field's value type (ldfld). Both collapse to the
    // property accessor call that produced the stack shape originally -
    // callvirt get_P pushes the same value ldobj would have loaded, and ldfld
    // accepts a by-value struct where the code's member read expected the
    // managed pointer. Consumers that need the pointer itself (ldflda, ldloc
    // spill, stfld into the storage - a copy write an accessor call cannot
    // make) keep the ldflda; there is no faithful call for them.
    private static void TryRewriteBackingFieldAddress(MethodDefinition method, IFieldDescriptor field,
        CilInstruction instruction, CilInstructionCollection instructions, int index,
        RuntimeContext? runtimeContext)
    {
        var name = field.Name?.Value;
        if (name == null || !name.StartsWith('<') || !name.EndsWith(BackingFieldSuffix)
            || index + 1 >= instructions.Count)
            return;
        if (index > 0 && instructions[index - 1].OpCode.Code
                is CilCode.Constrained or CilCode.Readonly or CilCode.Tailcall or CilCode.Volatile)
            return; // a prefix bound to ldflda cannot bind to the call
        var consumer = instructions[index + 1];
        var fieldType = field.Signature?.FieldType
            ?? (field as FieldDefinition)?.Signature?.FieldType
            ?? ((field as MemberReference)?.Resolve(runtimeContext) as FieldDefinition)?.Signature?.FieldType;
        var (load, operandMatch) = consumer.OpCode.Code switch
        {
            CilCode.Ldobj => (true, SameType(consumer.Operand as ITypeDefOrRef, fieldType)),
            CilCode.Stobj => (false, SameType(consumer.Operand as ITypeDefOrRef, fieldType)),
            CilCode.Ldind_Ref => (true, fieldType is not { IsValueType: true }),
            CilCode.Stind_Ref => (false, fieldType is not { IsValueType: true }),
            CilCode.Ldfld => (true, consumer.Operand is IFieldDescriptor inner
                && inner.DeclaringType != null && SameType(inner.DeclaringType, fieldType)),
            _ => ((bool?)null, false),
        };
        if (load == null || !operandMatch)
            return;
        if (!TryFindBackingAccessor(method, field, runtimeContext,
                instruction.OpCode.Code == CilCode.Ldsflda, load.Value,
                out var accessor, out var declaringType))
            return;
        instruction.OpCode = accessor!.IsStatic || declaringType!.IsValueType
            ? CilOpCodes.Call : CilOpCodes.Callvirt;
        instruction.Operand = field.DeclaringType is IMemberRefParent scope
                && !ReferenceEquals(scope, accessor.DeclaringType)
            ? scope.CreateMemberReference(accessor.Name!, accessor.Signature!)
            : accessor;
        if (consumer.OpCode.Code != CilCode.Ldfld)
        {
            consumer.OpCode = CilOpCodes.Nop;
            consumer.Operand = null;
        }
    }

    private static bool SameType(ITypeDescriptor? operand, TypeSignature? signature)
        => operand != null && signature != null && operand.FullName == signature.FullName;

    private static bool TryFindBackingAccessor(MethodDefinition method, IFieldDescriptor field,
        RuntimeContext? runtimeContext, bool staticAccess, bool load,
        out MethodDefinition? accessor, out TypeDefinition? declaringType)
    {
        accessor = null;
        declaringType = null;
        var name = field.Name?.Value;
        if (name == null || !name.StartsWith('<') || !name.EndsWith(BackingFieldSuffix))
            return false;
        var propertyName = name.Substring(1, name.Length - 1 - BackingFieldSuffix.Length);
        if (field.DeclaringType is not ITypeDefOrRef scopeRef
            || !TryResolveType(scopeRef, runtimeContext, out var scopeDef) || scopeDef == null)
            return false;
        // The property may be absent from the emitted type (stripped metadata,
        // an injected surface) while its accessor method still exists, so each
        // level tries the property first and the accessor-name convention next.
        var accessorName = (load ? "get_" : "set_") + propertyName;
        for (var type = scopeDef; type != null; type = ResolveBase(type, runtimeContext))
        {
            var candidate = type.Properties.FirstOrDefault(p => p.Name?.Value == propertyName)
                    is { } property ? load ? property.GetMethod : property.SetMethod : null;
            candidate ??= type.Methods.FirstOrDefault(m => m.Name?.Value == accessorName
                && m.IsStatic == staticAccess
                && m.Parameters.Count == (load ? 0 : 1));
            if (candidate != null && candidate != method && candidate.IsStatic == staticAccess
                && AccessorCallableFrom(candidate, method, type, runtimeContext))
            {
                accessor = candidate;
                declaringType = type;
            }
            if (candidate != null)
                return accessor != null;
        }
        return false;
    }

    private static void RewriteBackingFieldAccess(MethodDefinition method, IFieldDescriptor field,
        CilInstruction instruction, RuntimeContext? runtimeContext, bool load)
    {
        // The field reference may be scoped to a derived type while the field
        // and its auto-property live on a base; the accessor lookup walks the
        // scope's hierarchy rather than trusting field resolution.
        var staticAccess = instruction.OpCode.Code is CilCode.Ldsfld or CilCode.Stsfld;
        if (!TryFindBackingAccessor(method, field, runtimeContext, staticAccess, load,
                out var accessor, out var declaringType))
            return;
        instruction.OpCode = accessor!.IsStatic || declaringType!.IsValueType
            ? CilOpCodes.Call : CilOpCodes.Callvirt;
        instruction.Operand = field.DeclaringType is IMemberRefParent scope
                && !ReferenceEquals(scope, accessor.DeclaringType)
            ? scope.CreateMemberReference(accessor.Name!, accessor.Signature!)
            : accessor;
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
