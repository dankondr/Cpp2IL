using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.Il2CppApiFunctions;
using Cpp2IL.Core.InstructionSets;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;
using LibCpp2IL;
using LibCpp2IL.Elf;
using LibCpp2IL.PE;

namespace Cpp2IL.Core.Analysis;

public static class MetadataResolver
{
    public static void ResolveAll(MethodAnalysisContext method)
    {
        if (method.AppContext.Binary is ElfFile elf)
            ResolveGotLoads(method.ControlFlowGraph!, address =>
                elf.ReadReadOnlyRelocatedPointer(address) is { } pointer
                && method.AppContext.LibCpp2IlContext.GetAnyGlobalByAddress(pointer) != null ? pointer : null);

        ResolveStringLiteralAccessors(method);
        ResolveCalls(method);
        ResolveGetter(method);
        ResolveMetadataUsages(method);
    }

    // A RELRO load defines the address of a metadata slot. Lift each such load to the slot
    // itself before branch/conditional-select merges, then remove the native dereference:
    // ResolveMetadataUsages turns the slot into the actual managed value afterwards.
    public static void ResolveGotLoads(ISILControlFlowGraph graph, Func<ulong, ulong?> readGotPointer)
    {
        var slots = new HashSet<LocalVariable>();
        foreach (var instruction in graph.Instructions)
            if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable destination, MemoryOperand { IsConstant: true } source] }
                && readGotPointer((ulong)source.Addend) is { } slot)
            {
                slots.Add(destination);
                source.Addend = (long)slot;
                instruction.SetOperand(1, source);
            }

        bool changed;
        do
        {
            changed = false;
            foreach (var instruction in graph.Instructions)
            {
                if (instruction.OpCode is not (OpCode.Move or OpCode.Phi)
                    || instruction.Operands.Count < 2
                    || instruction.Operands[0] is not LocalVariable destination)
                    continue;
                var inputs = instruction.Operands.Skip(1).OfType<LocalVariable>().ToList();
                if (inputs.Count == instruction.Operands.Count - 1 && inputs.Count > 0
                    && inputs.All(slots.Contains))
                    changed |= slots.Add(destination);
            }
        } while (changed);

        foreach (var instruction in graph.Instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
                if (instruction.Operands[i] is MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable address }
                    && slots.Contains(address))
                    instruction.SetOperand(i, address);
        }
    }

    private static void ResolveStringLiteralAccessors(MethodAnalysisContext method)
    {
        var libContext = method.AppContext.LibCpp2IlContext;

        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            if (instruction.Destination is LocalVariable destination)
                definitions[destination] = instruction;

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (instruction.OpCode != OpCode.Call || instruction.Operands[1] is not LocalVariable result)
                continue;

            for (var i = 2; i < instruction.Operands.Count; i++)
            {
                if (LiteralSlotAddress(instruction.Operands[i], definitions) is not { } address
                    || libContext.GetLiteralByAddress(address) is not { } literal)
                    continue;

                instruction.OpCode = OpCode.Move;
                instruction.SetOperands(result, new StringLiteral(literal));
                break;
            }
        }
    }

    private static ulong? LiteralSlotAddress(IOperand operand, Dictionary<LocalVariable, Instruction> definitions) =>
        operand switch
        {
            Immediate immediate => immediate.UnsignedValue,
            LocalVariable local when definitions.TryGetValue(local, out var definition)
                && definition is { OpCode: OpCode.Move, Operands: [_, Immediate immediate] } => immediate.UnsignedValue,
            _ => null,
        };

    /// <summary>
    /// Resolves <c>Move local, [absoluteAddress]</c> loads of IL2CPP metadata-usage globals into a
    /// strongly-typed operand: a string literal, a <see cref="TypeAnalysisContext"/> (an Il2CppType*/
    /// Il2CppClass* usage) or, for a MethodInfo* usage, a <see cref="RuntimeMethodInfoAnalysisContext"/>
    /// naming the method it refers to (also used to type the local - see <see cref="LocalVariables"/>),
    /// or likewise a <see cref="RuntimeFieldInfoAnalysisContext"/> for a FieldInfo* usage.
    /// </summary>
    private static void ResolveMetadataUsages(MethodAnalysisContext method)
    {
        var libContext = method.AppContext.LibCpp2IlContext;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            for (var operandIndex = 0; operandIndex < instruction.Operands.Count; operandIndex++)
            {
                if (instruction.OpCode == OpCode.Move && operandIndex == 0)
                    continue;

                var address = instruction.Operands[operandIndex] switch
                {
                    MemoryOperand { Base: null, Index: null, Scale: 0 } memory => (ulong)memory.Addend,
                    Immediate immediate when instruction.OpCode == OpCode.Move && operandIndex == 1 => immediate.UnsignedValue,
                    _ => 0ul,
                };

                if (address == 0)
                    continue;

                // String literal.
                var stringLiteral = libContext.GetLiteralByAddress(address);
                if (stringLiteral != null)
                {
                    instruction.SetOperand(operandIndex, new StringLiteral(stringLiteral));
                    continue;
                }

                // Type metadata usage (Il2CppType* / Il2CppClass*).
                if (method.DeclaringType is { } declaringType)
                {
                    var typeGlobal = libContext.GetTypeGlobalByAddress(address);
                    if (typeGlobal != null)
                    {
                        instruction.SetOperand(operandIndex, declaringType.AppContext.ResolveIl2CppType(typeGlobal));
                        continue;
                    }
                }

                // Method metadata usage (MethodInfo*). On metadata v27+ GetMethodGlobalByAddress can return
                // any global, so confirm it is actually a method before resolving - the resolver's switch
                // throws on other usage kinds.
                var methodUsage = libContext.GetMethodGlobalByAddress(address);
                if (methodUsage?.Type is MetadataUsageType.MethodDef or MetadataUsageType.MethodRef
                    && method.AppContext.ResolveContextForMethod(methodUsage) is { DeclaringType: { } methodDeclaringType } methodContext)
                {
                    instruction.SetOperand(operandIndex, new RuntimeMethodInfoAnalysisContext(methodContext, methodDeclaringType.DeclaringAssembly));
                    continue;
                }

                // Field metadata usage (FieldInfo*), e.g. the RuntimeFieldHandle passed to InitializeArray.
                if (libContext.GetRawFieldGlobalByAddress(address) is { Type: MetadataUsageType.FieldInfo } fieldUsage
                    && method.AppContext.ResolveContextForField(fieldUsage.AsField()) is { DeclaringType.DeclaringAssembly: { } fieldAssembly } fieldContext)
                    instruction.SetOperand(operandIndex, new RuntimeFieldInfoAnalysisContext(fieldContext, fieldAssembly));
            }
        }
    }

    /// <summary>
    /// Replaces every <c>[base + addend]</c> memory operand whose base is a typed local with a
    /// <see cref="FieldReference"/> to the field at that offset. Returns whether any operand was
    /// resolved this pass, so the type/field fixpoint can detect convergence: as more bases become
    /// typed (a field load types its result, which is the base of the next load), more offsets
    /// resolve, so this is re-run until it stops finding new fields.
    /// </summary>
    public static bool ResolveFieldOffsets(MethodAnalysisContext method)
    {
        var changed = NormalizeObjectAddressAliases(method);
        var definitions = method.ControlFlowGraph!.Instructions
            .Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!)
            .Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());

        // Locals that are the base register of a raw memory load emit `&T`
        // (or native int) because that use demands it. Replacing the def-source
        // of such a local with a managed value can demote its emitted type to a
        // reference and leave the surviving [v] loads with `ref` where they need
        // `&`, so substitutions into those defs are not made here.
        var loadBases = new HashSet<LocalVariable>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        foreach (var operand in instruction.Operands)
            if (operand is MemoryOperand { Base: LocalVariable baseLocal })
                loadBases.Add(baseLocal);

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var operand = instruction.Operands[i];

                if (operand is not MemoryOperand memory)
                    continue;

                if (memory.Base is not LocalVariable local
                    || EffectiveObjectType(local, definitions, method.DeclaringType) is not { } localType)
                    continue;

                // check if static field access
                var staticOwner = (localType as StaticFieldStorageTypeAnalysisContext)?.OwnerType;
                var owner = staticOwner ?? localType;
                var genericOwner = owner as GenericInstanceTypeAnalysisContext;

                if (memory.Index is LocalVariable selector
                    && TryResolveFiniteConstants(selector, definitions, [], out var selectorValues))
                {
                    var choices = new List<(long Value, FieldReference Field)>();
                    var scale = memory.Scale <= 1 ? 1 : memory.Scale;
                    foreach (var selectorValue in selectorValues.OrderBy(value => value))
                    {
                        long offset;
                        try { offset = checked(memory.Addend + selectorValue * scale); }
                        catch (System.OverflowException) { choices.Clear(); break; }

                        if (ResolveField(owner, staticOwner, offset, memory.AccessSize) is not { } selectedField
                            || (staticOwner == null
                                && !LocalSuppliesFieldBase(local, owner, method.DeclaringType, method)))
                        {
                            choices.Clear();
                            break;
                        }

                        var resolvedField = selectedField.Field;
                        if (genericOwner != null && resolvedField is not ConcreteGenericFieldAnalysisContext)
                            resolvedField = new ConcreteGenericFieldAnalysisContext(resolvedField, genericOwner);
                        choices.Add((selectorValue,
                            new FieldReference(resolvedField, local, (int)offset, selectedField.Containers,
                                memory.AccessSize)));
                    }

                    if (choices.Count > 0
                        && choices.All(c => c.Field.Field.FieldType.FullName == choices[0].Field.Field.FieldType.FullName))
                    {
                        instruction.SetOperand(i, new SelectedFieldReference(selector, choices));
                        changed = true;
                    }
                    continue;
                }

                // Has to be [base (local) + addend (field offset)]
                if (memory.Index != null || memory.Scale != 0)
                    continue;

                var resolved = ResolveField(owner, staticOwner, memory.Addend, memory.AccessSize);
                var field = resolved?.Field;

                if (field == null) // TODO: Support nested fields (Field1.Field2.Field3)
                    continue;

                // The produced reference pushes `local` as its ldfld/stfld base.
                // When the local's declared type supplies neither `&host` nor a
                // host-assignable reference the emission is invalid IL - keep the
                // diagnostic instead. Static owners emit ldsfld and need no base.
                if (staticOwner == null && !LocalSuppliesFieldBase(local, owner, method.DeclaringType, method))
                    continue;

                // make sure we have a full GIT for field access. open type is bad.
                if (genericOwner != null && field is not ConcreteGenericFieldAnalysisContext)
                    field = new ConcreteGenericFieldAnalysisContext(field, genericOwner);

                instruction.SetOperand(i, new FieldReference(field, local, (int)memory.Addend,
                    resolved!.Value.Containers, memory.AccessSize));
                changed = true;

                // A private cross-assembly field read is an inlined accessor (e.g.
                // String._stringLength behind get_Length) and cannot be named from the caller -
                // emit the public accessor call the inline came from instead, but only when the
                // candidate's own body is structurally proven to return that exact field.
                if (i == 1 && instruction.OpCode == OpCode.Move
                    && instruction.Operands[0] is LocalVariable destination
                    && instruction.Operands[1] is FieldReference fieldRef
                    && TryRecoverFieldAccessor(method, fieldRef, local) is { } accessor)
                {
                    instruction.OpCode = OpCode.Call;
                    instruction.SetOperands(accessor, destination, local);
                }
            }
        }

        changed |= ResolveAddressedStorageReads(method, definitions, loadBases);
        return changed;
    }

    /// <summary>
    /// Rewrites [v + addend] unmanaged dereferences whose base register provably holds the
    /// address of a managed storage location (v = &amp;t, plus constant displacements on it).
    /// [&amp;t] is a plain `t` read; [&amp;t + k] reaches the sibling frame slot at that
    /// offset; [&amp;f + k] reaches whatever field of f's host object sits at f's absolute
    /// offset plus k (which includes f's own interior for value-typed f). Any site whose
    /// storage cannot be proven keeps its MemoryOperand and its diagnostic.
    /// </summary>
    private static bool ResolveAddressedStorageReads(MethodAnalysisContext method,
        IReadOnlyDictionary<LocalVariable, Instruction> definitions,
        HashSet<LocalVariable> loadBases)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;

        // Frame slots by fp-relative offset; [&stack_N + k] reads the slot at -N + k,
        // which is a real local read only when exactly one local names that address.
        // A slot carried by several SSA versions is ambiguous - the load's live version
        // cannot be chosen from the address alone - so only single-version cells qualify.
        var slots = new Dictionary<int, LocalVariable>();
        foreach (var candidate in method.Locals)
        {
            if (LocalVariables.TryStackOffset(candidate.Register.Name) is not { } offset)
                continue;
            if (!slots.TryAdd(offset, candidate))
                slots[offset] = null!; // several locals share the offset - ambiguous
        }

        var changed = false;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        for (var i = 0; i < instruction.Operands.Count; i++)
        {
            if (instruction.Operands[i] is not MemoryOperand
                    { Base: LocalVariable baseLocal, Index: null, Scale: 0 } memory
                || ResolveAddressedStorage(baseLocal, definitions, []) is not { } resolved)
                continue;

            long effective;
            try
            {
                effective = checked(memory.Addend + resolved.Displacement);
            }
            catch (System.OverflowException)
            {
                continue;
            }

            switch (resolved.Storage)
            {
                case LocalVariable slot:
                    if (effective == 0)
                    {
                        // *(&t) reads t's storage; a pointer-sized deref of a wider
                        // struct local would silently truncate, so value types stay out.
                        if (memory.AccessSize == pointerSize && slot.Type is not { IsValueType: true }
                            && LoadsAsPointer(instruction, slot.Type)
                            && !DemotesLoadBase(instruction, loadBases, slot.Type, method))
                        {
                            instruction.SetOperand(i, slot);
                            changed = true;
                        }
                    }
                    else if (memory.AccessSize == pointerSize
                             && LocalVariables.TryStackOffset(slot.Register.Name) is { } slotOffset
                             && slotOffset + effective is >= int.MinValue and <= int.MaxValue
                             && slots.TryGetValue((int)(slotOffset + effective), out var siblingSlot)
                             && siblingSlot != null
                             && siblingSlot.Type is not { IsValueType: true }
                             && LoadsAsPointer(instruction, siblingSlot.Type)
                             && !DemotesLoadBase(instruction, loadBases, siblingSlot.Type, method))
                    {
                        instruction.SetOperand(i, siblingSlot);
                        changed = true;
                    }
                    break;

                case FieldReference addressed when !addressed.Field.IsStatic:
                    if (effective == 0)
                    {
                        // *(&f) is f itself when f's storage is a single pointer slot.
                        if (memory.AccessSize == pointerSize
                            && addressed.Field.FieldType is { IsValueType: false }
                                and not PointerTypeAnalysisContext
                            && (addressed.Containers.Count > 0
                                    ? addressed.Containers[0].DeclaringType
                                    : addressed.Field.DeclaringType) is { } declaredOwner
                            && LocalSuppliesFieldBase(addressed.Local, declaredOwner, method.DeclaringType, method)
                            && LoadsAsPointer(instruction, addressed.Field.FieldType)
                            && !DemotesLoadBase(instruction, loadBases, addressed.Field.FieldType, method))
                        {
                            instruction.SetOperand(i, addressed);
                            changed = true;
                        }
                        break;
                    }

                    var host = EffectiveObjectType(addressed.Local, definitions, method.DeclaringType)
                               ?? addressed.Field.DeclaringType;
                    if (host == null
                        // The produced reference's Local is pushed as the ldfld/stfld
                        // base: `&host` for a value-type host, a host-assignable
                        // reference otherwise. object/untyped supplies neither.
                        || !LocalSuppliesFieldBase(addressed.Local, host, method.DeclaringType, method)
                        || ResolveField(host, null, addressed.Offset + effective,
                            memory.AccessSize) is not { } sibling
                        || !LoadsAsPointer(instruction, sibling.Field.FieldType)
                        || DemotesLoadBase(instruction, loadBases, sibling.Field.FieldType, method))
                        break;
                    instruction.SetOperand(i, new FieldReference(sibling.Field, addressed.Local,
                        (int)(addressed.Offset + effective), sibling.Containers, memory.AccessSize));
                    changed = true;
                    break;
            }
        }
        return changed;
    }

    // Chases a base register's single-definition Move/Add/Subtract chain to the
    // addressed storage it carries (&t or &f), accumulating byte displacement.
    private static (IOperand Storage, long Displacement)? ResolveAddressedStorage(
        IOperand operand, IReadOnlyDictionary<LocalVariable, Instruction> definitions,
        HashSet<LocalVariable> visiting)
    {
        switch (operand)
        {
            case AddressOf { Target: LocalVariable or FieldReference } address:
                return (address.Target, 0);

            case LocalVariable local:
                if (!visiting.Add(local)
                    || !definitions.TryGetValue(local, out var definition))
                    return null;

                (IOperand Storage, long Displacement)? resolved = definition switch
                {
                    { OpCode: OpCode.Move, Operands.Count: >= 2 }
                        => ResolveAddressedStorage(definition.Operands[1], definitions, visiting),
                    { OpCode: OpCode.Add or OpCode.Subtract, Operands: [_, { } source, Immediate displacement] }
                        => ResolveAddressedStorage(source, definitions, visiting) is { } inner
                            ? (inner.Storage, inner.Displacement
                                + (definition.OpCode == OpCode.Subtract ? -displacement.Value : displacement.Value))
                            : null,
                    { OpCode: OpCode.Add, Operands: [_, Immediate displacement, { } source] }
                        => ResolveAddressedStorage(source, definitions, visiting) is { } inner
                            ? (inner.Storage, inner.Displacement + displacement.Value)
                            : null,
                    _ => null,
                };

                visiting.Remove(local);
                return resolved;

            default:
                return null;
        }
    }

    // The instruction's produced value lands in a local that other instructions
    // may consume as an address (`[dest]` loads, `&dest`, ldfld receivers, cpblk,
    // `in`/`ref` arguments, calli targets) rather than as a value. Substituting a
    // managed operand for the unmanaged def-source changes the local's emitted
    // type to the produced type, so every such consumer must still be satisfied:
    // [dest + off] must resolve through the produced type's instance layout (they
    // then resolve in this same pass - a bare [dest] deref of a reference type
    // reads the object header, not a managed field, and ResolveField's offset-0
    // miss keeps the diagnostic), a field receiver needs the produced type
    // assignable to the declaring type, an arithmetic or pointer-demanding use
    // needs a non-reference produced type, and `&`-positions need an exact type.
    private static bool DemotesLoadBase(Instruction instruction, HashSet<LocalVariable> loadBases,
        TypeAnalysisContext? producedType, MethodAnalysisContext method, bool checkMemoryBases = true)
    {
        if (instruction.Destination is not LocalVariable destination
            || destination.Type is ByRefTypeAnalysisContext or PointerTypeAnalysisContext)
            return false;
        return BreaksConsumers(destination, producedType, method, [], checkMemoryBases);
    }

    private static bool BreaksConsumers(LocalVariable dest, TypeAnalysisContext? producedType,
        MethodAnalysisContext method, HashSet<LocalVariable> visited, bool checkMemoryBases)
    {
        if (!visited.Add(dest))
            return false;
        foreach (var user in method.ControlFlowGraph!.Instructions)
        for (var j = 0; j < user.Operands.Count; j++)
        {
            switch (user.Operands[j])
            {
                case MemoryOperand { Base: { } baseLocal } memory
                    when checkMemoryBases && ReferenceEquals(baseLocal, dest):
                    // The use's own host type wins over what this def alone
                    // produces: a declared/propagated type is what emission sees.
                    var host = dest.Type ?? producedType;
                    if (host == null || memory.Index != null || memory.Scale != 0
                        || ResolveField(host, null, memory.Addend, memory.AccessSize) == null)
                        return true;
                    break;
                case AddressOf { Target: { } target } when ReferencesLocal(target, dest):
                    // `&dest` forwards whatever address the produced operand's
                    // storage carries; its consumer's exact type cannot be
                    // established here, so the diagnostic stays.
                    return true;
                case FieldReference { Local: { } receiver } field
                    when ReferenceEquals(receiver, dest):
                    // The receiver supplies the first container's owner on a
                    // chained access (`v.a.b` needs `a`'s declaring type), not
                    // the leaf field's.
                    if (producedType == null
                        || !ReceiverSatisfied(producedType, LocalVariables.ReceiverHost(field)))
                        return true;
                    break;
                case SelectedFieldReference { Selector: LocalVariable selector }
                    when ReferenceEquals(selector, dest):
                    return true; // the selector slot is numeric, a reference cannot fill it
                case ArrayAccess { Array: { } array } when ReferenceEquals(array, dest):
                    if (producedType is not SzArrayTypeAnalysisContext)
                        return true;
                    break;
                case LocalVariable local when ReferenceEquals(local, dest):
                    if (BreaksValueUse(user, j, producedType, method, visited, checkMemoryBases))
                        return true;
                    break;
            }
        }
        return false;
    }

    private static bool ReferencesLocal(IOperand operand, LocalVariable local) => operand switch
    {
        LocalVariable localOperand => ReferenceEquals(localOperand, local),
        FieldReference { Local: { } fieldLocal } => ReferenceEquals(fieldLocal, local),
        ArrayAccess { Array: { } array, Index: { } index } =>
            ReferenceEquals(array, local) || index is LocalVariable indexLocal
                && ReferenceEquals(indexLocal, local),
        _ => false,
    };

    // A ldfld/stfld or instance-call receiver emits `&host` for a value-type
    // host (ldloca on a host-typed local) or a host-assignable reference
    // otherwise. `&` consumption needs the exact element type; a reference
    // receiver accepts any subtype.
    private static bool ReceiverSatisfied(TypeAnalysisContext producedType, TypeAnalysisContext? host)
        => LocalVariables.ReceiverSatisfied(producedType, host);

    private static bool BreaksValueUse(Instruction user, int operandIndex,
        TypeAnalysisContext? producedType, MethodAnalysisContext method, HashSet<LocalVariable> visited,
        bool checkMemoryBases)
    {
        switch (user.OpCode)
        {
            // `Move copy, dest` propagates the produced type to the copy - its
            // consumers must satisfy it too.
            case OpCode.Move:
                return operandIndex != 0 && user.Destination is LocalVariable copy
                       && BreaksConsumers(copy, producedType, method, visited, checkMemoryBases);
            // Arithmetic and pointer-shaping ops need a numeric/`&` operand; a
            // managed reference cannot fill them.
            case OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide
                or OpCode.Modulo or OpCode.ShiftLeft or OpCode.ShiftRight or OpCode.And
                or OpCode.Or or OpCode.Xor or OpCode.Not or OpCode.Negate
                or OpCode.SignExtend32 or OpCode.VectorMin or OpCode.VectorMax or OpCode.NewArr:
                return producedType is not { IsValueType: true }
                       and not ByRefTypeAnalysisContext and not PointerTypeAnalysisContext
                       and not GenericParameterTypeAnalysisContext;
            // Raw-memory ops take `&`-positions; calli/jump targets a code pointer.
            case OpCode.MemoryCopy or OpCode.MemorySet or OpCode.MemoryMove
                or OpCode.IndirectCall or OpCode.IndirectJump:
                return true;
            case OpCode.Box:
                return producedType is not { IsValueType: true };
            case OpCode.Call or OpCode.CallVoid:
                if (user.Operands[0] is not MethodAnalysisContext callee)
                    return false;
                var baseIndex = user.OpCode == OpCode.Call ? 2 : 1;
                if (!callee.IsStatic)
                {
                    if (operandIndex == baseIndex)
                        return producedType == null
                               || !ReceiverSatisfied(producedType, callee.DeclaringType);
                    baseIndex++;
                }
                var parameterIndex = operandIndex - baseIndex;
                return parameterIndex >= 0 && parameterIndex < callee.Parameters.Count
                       && callee.Parameters[parameterIndex].ParameterType
                            is ByRefTypeAnalysisContext { ElementType: { } element }
                       && (producedType == null || element.FullName != producedType.FullName);
            default:
                return false;
        }
    }

    // Operand positions consumed as a raw address rather than a value slot:
    // cpblk/initblk destinations and sources, and calli/jump targets. A local or
    // field substituted there is only honest when its declared type already is a
    // pointer - pushing an object reference and conv.u-ing it is invalid IL and
    // would misread a reference as an address anyway.
    private static bool LoadsAsPointer(Instruction instruction, TypeAnalysisContext? producedType)
        => instruction.OpCode is not (OpCode.MemoryCopy or OpCode.MemorySet or OpCode.MemoryMove
                or OpCode.IndirectCall or OpCode.IndirectJump)
           || producedType is ByRefTypeAnalysisContext or PointerTypeAnalysisContext
               or { FullName: "System.IntPtr" or "System.UIntPtr" };

    // A FieldReference's Local is pushed as the ldfld/stfld receiver: `&host` for
    // a value-type host (ldloca on a T-declared local, or a &T local), or a
    // reference assignable to the host. An object/untyped local supplies neither,
    // so such sites keep their MemoryOperand and their diagnostic.
    private static bool LocalSuppliesFieldBase(LocalVariable local, TypeAnalysisContext host,
        TypeAnalysisContext? thisType, MethodAnalysisContext method)
    {
        // Mirrors EmittedLocalTypeCore's `this` arm: ldarg.0 pushes the declaring
        // type (`&T` for value types), the self-instantiation on generic types.
        TypeAnalysisContext? type;
        if (local.IsThis && thisType != null)
        {
            var thisEmit = local.Type as GenericInstanceTypeAnalysisContext ?? thisType;
            type = thisEmit.IsValueType ? new ByRefTypeAnalysisContext(thisEmit) : thisEmit;
        }
        else
            type = local.Type;
        var declaredSupplies = type is ByRefTypeAnalysisContext { ElementType: { } pointee }
            ? pointee.IsAssignableTo(host)
            : type != null && type.IsAssignableTo(host);
        var emitted = LocalVariables.EmittedSlotLocalType(local, method);
        if (!declaredSupplies)
            // local.Type can be transiently unannotated mid-fixpoint; a concrete
            // declared type is the contract and stays rejected, but an empty
            // annotation proves nothing - the def-derived slot type decides.
            return type == null && emitted != null && ReceiverSatisfied(emitted, host);
        // The receiver pushes the local's emitted slot type - a `Move`-copy's
        // source, a numeric view or an `&`-emission can differ from local.Type,
        // and a ldfld on a mismatched `&` is invalid IL.
        return emitted != null && ReceiverSatisfied(emitted, host);
    }

    private static (FieldAnalysisContext Field, IReadOnlyList<FieldAnalysisContext> Containers)? ResolveField(
        TypeAnalysisContext owner, TypeAnalysisContext? staticOwner, long offset, int accessSize)
    {
        if (staticOwner != null)
        {
            if (FindStaticFieldAtOffset(owner, offset) is { } staticField)
                return (staticField, []);
            if (FindNestedStaticFieldAtOffset(owner, offset, accessSize) is { } nestedStatic)
                return (nestedStatic.Field, [nestedStatic.Container]);
            return null;
        }

        return FindInstanceFieldPathAtOffset(owner, offset, accessSize);
    }

    // The honest public equivalent of a cross-assembly private field read: IL2CPP inlines managed
    // accessors (String.get_Length => _stringLength, List<T>.get_Count => _size), leaving a direct
    // read of a field the emitted assembly cannot name. A read is rewritten to an accessor call
    // only when the candidate is structurally proven to read that exact field: the declaring type
    // exposes exactly one public parameterless instance getter of the field's type, AND the
    // getter's own native body is just `return this.<field>` - a single load from
    // [this + accessOffset] into the return register followed by ret. Uniqueness, return type, or
    // naming alone are never proof: a type could have a second private field of the same type
    // whose only getter returns the other field, so an unproven candidate leaves the
    // inaccessible-field read in place as the diagnostic.
    private static MethodAnalysisContext? TryRecoverFieldAccessor(
        MethodAnalysisContext caller, FieldReference fieldRef, LocalVariable receiver)
    {
        var field = fieldRef.Field;

        // A container path is a nested member access (this.a.b) - no simple getter produces that.
        if (fieldRef.Containers.Count > 0 || !NeedsAccessor(field, caller)
            || receiver.Type is { IsValueType: true })
            return null;

        var genericInstance = field.DeclaringType as GenericInstanceTypeAnalysisContext;
        var lookup = genericInstance?.GenericType ?? field.DeclaringType;
        if (lookup == null)
            return null;

        var candidates = lookup.Methods
            .Where(m => !m.IsStatic && m.Parameters.Count == 0
                && m.Name.StartsWith("get_", StringComparison.Ordinal)
                && (m.Attributes & MethodAttributes.MemberAccessMask) == MethodAttributes.Public
                && m.ReturnType.FullName == field.FieldType.FullName)
            .ToList();
        if (candidates.Count != 1)
            return null;

        var accessor = genericInstance != null
            ? (MethodAnalysisContext)new ConcreteGenericMethodAnalysisContext(candidates[0],
                genericInstance.GenericArguments, [])
            : candidates[0];
        return GetterProvablyReadsField(caller.AppContext, accessor, fieldRef.Offset)
            && InaccessibleCalleeRecovery.IsVisibleFrom(accessor, caller) ? accessor : null;
    }

    // Disassemble the candidate's native body and require it to be a pure field projection:
    // a single load from [this + fieldOffset] into the return register, then ret, with no
    // stores, calls, branches, or arithmetic in between. This is the only acceptable proof that
    // the getter returns this field - anything else is not sound to substitute.
    private static bool GetterProvablyReadsField(ApplicationAnalysisContext app,
        MethodAnalysisContext accessor, long fieldOffset)
    {
        // Shared generic methods carry their code on the definition's method pointer.
        var pointer = accessor.UnderlyingPointer;
        if (pointer == 0 && accessor is ConcreteGenericMethodAnalysisContext generic)
            pointer = generic.BaseMethodContext.UnderlyingPointer;
        if (pointer == 0)
            return false;
        return app.InstructionSet switch
        {
            NewArmV8InstructionSet => GetterProvablyReadsFieldArm64(app, pointer, fieldOffset),
            X86InstructionSet => GetterProvablyReadsFieldX86(app, pointer, fieldOffset),
            _ => false,
        };
    }

    private static bool GetterProvablyReadsFieldArm64(ApplicationAnalysisContext app,
        ulong pointer, long fieldOffset)
    {
        List<Disarm.Arm64Instruction> body;
        try
        {
            body = NewArm64Utils.GetArm64MethodBodyAtVirtualAddress(app, pointer);
        }
        catch
        {
            return false;
        }

        var loaded = false;
        var thisRegister = Disarm.InternalDisassembly.Arm64Register.X0; // instance method: `this` is the first argument
        foreach (var insn in body)
        {
            switch (insn.Mnemonic)
            {
                case Disarm.Arm64Mnemonic.NOP or Disarm.Arm64Mnemonic.HINT
                    or Disarm.Arm64Mnemonic.PRFM or Disarm.Arm64Mnemonic.PRFUM:
                    continue;
                case Disarm.Arm64Mnemonic.MOV
                    when insn.Op0Kind == Disarm.Arm64OperandKind.Register
                        && insn.Op1Kind == Disarm.Arm64OperandKind.Register
                        && insn.Op1Reg == thisRegister:
                    thisRegister = insn.Op0Reg; // a `this` alias (mov x8, x0)
                    continue;
                case Disarm.Arm64Mnemonic.LDR or Disarm.Arm64Mnemonic.LDRB
                    or Disarm.Arm64Mnemonic.LDRH or Disarm.Arm64Mnemonic.LDRSB
                    or Disarm.Arm64Mnemonic.LDRSH or Disarm.Arm64Mnemonic.LDRSW
                    or Disarm.Arm64Mnemonic.LDUR or Disarm.Arm64Mnemonic.LDURB
                    or Disarm.Arm64Mnemonic.LDURH or Disarm.Arm64Mnemonic.LDURSB
                    or Disarm.Arm64Mnemonic.LDURSH or Disarm.Arm64Mnemonic.LDURSW
                    when !loaded && insn.MemBase == thisRegister
                        && insn.MemOffset == fieldOffset && insn.MemAddendReg == Disarm.InternalDisassembly.Arm64Register.INVALID
                        && insn.MemIndexMode == Disarm.Arm64MemoryIndexMode.Offset
                        && insn.Op0Reg is Disarm.InternalDisassembly.Arm64Register.W0 or Disarm.InternalDisassembly.Arm64Register.X0
                            or Disarm.InternalDisassembly.Arm64Register.S0 or Disarm.InternalDisassembly.Arm64Register.D0
                            or Disarm.InternalDisassembly.Arm64Register.B0 or Disarm.InternalDisassembly.Arm64Register.H0
                            or Disarm.InternalDisassembly.Arm64Register.V0:
                    loaded = true;
                    continue;
                case Disarm.Arm64Mnemonic.RET or Disarm.Arm64Mnemonic.RETAA
                    or Disarm.Arm64Mnemonic.RETAB:
                    return loaded;
                default:
                    return false; // any other memory traffic, arithmetic, or control flow
            }
        }
        return false;
    }

    private static bool GetterProvablyReadsFieldX86(ApplicationAnalysisContext app,
        ulong pointer, long fieldOffset)
    {
        Iced.Intel.InstructionList body;
        try
        {
            body = X86Utils.GetMethodBodyAtVirtAddressNew(pointer, true, app);
        }
        catch
        {
            return false;
        }

        var loaded = false;
        var thisRegisters = new HashSet<Iced.Intel.Register>
            { app.Binary is PE ? Iced.Intel.Register.RCX : Iced.Intel.Register.RDI };
        foreach (var insn in body)
        {
            switch (insn.Mnemonic)
            {
                case Iced.Intel.Mnemonic.Nop or Iced.Intel.Mnemonic.Int3:
                    continue;
                case Iced.Intel.Mnemonic.Mov
                    when insn.Op0Kind == Iced.Intel.OpKind.Register
                        && insn.Op1Kind == Iced.Intel.OpKind.Register
                        && thisRegisters.Contains(insn.Op1Register):
                    thisRegisters.Add(insn.Op0Register); // a `this` alias (mov rbx, rcx)
                    continue;
                case Iced.Intel.Mnemonic.Mov or Iced.Intel.Mnemonic.Movzx
                    or Iced.Intel.Mnemonic.Movsx or Iced.Intel.Mnemonic.Movsxd
                    or Iced.Intel.Mnemonic.Movss or Iced.Intel.Mnemonic.Movsd
                    or Iced.Intel.Mnemonic.Movd or Iced.Intel.Mnemonic.Movq
                    or Iced.Intel.Mnemonic.Movaps or Iced.Intel.Mnemonic.Movups
                    when !loaded && insn.Op1Kind == Iced.Intel.OpKind.Memory
                        && thisRegisters.Contains(insn.MemoryBase)
                        && insn.MemoryIndex == Iced.Intel.Register.None
                        && insn.MemoryDisplacement64 == (ulong)fieldOffset
                        && insn.Op0Register is Iced.Intel.Register.EAX or Iced.Intel.Register.RAX
                            or Iced.Intel.Register.XMM0 or Iced.Intel.Register.AL:
                    loaded = true;
                    continue;
                case Iced.Intel.Mnemonic.Ret:
                    return loaded;
                default:
                    return false;
            }
        }
        return false;
    }

    private static bool NeedsAccessor(FieldAnalysisContext field, MethodAnalysisContext caller)
    {
        var access = field.Attributes & FieldAttributes.FieldAccessMask;
        if (access is FieldAttributes.Public or FieldAttributes.Family or FieldAttributes.FamORAssem)
            return false;

        var declaring = field.DeclaringType;
        var callerType = caller.DeclaringType;
        if (declaring == null || callerType == null)
            return false;

        if (declaring is GenericInstanceTypeAnalysisContext instance)
            declaring = instance.GenericType;
        if (callerType is GenericInstanceTypeAnalysisContext callerInstance)
            callerType = callerInstance.GenericType;
        if (ReferenceEquals(declaring, callerType))
            return false; // private access within the same type stays a direct read

        var declaringAssembly = declaring?.DeclaringAssembly;
        var callerAssembly = callerType.DeclaringAssembly;
        return declaringAssembly == null || callerAssembly == null
            || !(ReferenceEquals(declaringAssembly, callerAssembly)
                || (declaringAssembly.Name != null && declaringAssembly.Name == callerAssembly.Name)
                || Extensions.AccessibilityExtensions.SharesEmittedInternals(declaringAssembly, callerAssembly));
    }

    internal static (FieldAnalysisContext Field, IReadOnlyList<FieldAnalysisContext> Containers)?
        FindInstanceFieldPathAtOffset(TypeAnalysisContext owner, long offset, int accessSize)
    {
        if (FindNestedInstanceFieldAtOffset(owner, offset, accessSize) is { } nested)
            return (nested.Field, [nested.Container]);
        return FindInstanceFieldAtOffset(owner, offset) is { } field ? (field, []) : null;
    }

    private static (FieldAnalysisContext Container, FieldAnalysisContext Field)? FindNestedStaticFieldAtOffset(
        TypeAnalysisContext owner, long offset, int accessSize)
    {
        if (accessSize <= 0 || owner is GenericInstanceTypeAnalysisContext || owner.GenericParameters.Count > 0)
            return null;

        for (var candidate = owner; candidate != null; candidate = candidate.BaseType)
        foreach (var container in candidate.Fields.Where(field => field.IsStatic
                         && (field.Attributes & FieldAttributes.Literal) == 0 && field.FieldType.IsValueType)
                     .OrderByDescending(field => field.Offset))
        {
            var relativeOffset = offset - container.Offset;
            if (relativeOffset < 0)
                continue;
            var nested = container.FieldType.Fields.FirstOrDefault(field => !field.IsStatic
                && field.Offset == relativeOffset
                && PrimitiveStorageSize(field.FieldType, owner.AppContext.Binary.PointerSizeBytes) == accessSize);
            if (nested != null)
                return (container, nested);
        }

        return null;
    }

    private static bool TryResolveFiniteConstants(LocalVariable local,
        IReadOnlyDictionary<LocalVariable, Instruction> definitions, HashSet<LocalVariable> visiting,
        out HashSet<long> values)
    {
        values = [];
        if (!visiting.Add(local) || !definitions.TryGetValue(local, out var definition))
            return false;

        var sources = definition.OpCode switch
        {
            OpCode.Move when definition.Operands.Count == 2 => definition.Operands.Skip(1),
            OpCode.Phi => definition.Operands.Skip(1),
            _ => []
        };

        foreach (var source in sources)
        {
            if (source is Immediate immediate)
                values.Add(immediate.Value);
            else if (source is LocalVariable sourceLocal
                && TryResolveFiniteConstants(sourceLocal, definitions, visiting, out var nested))
                values.UnionWith(nested);
            else
            {
                visiting.Remove(local);
                values.Clear();
                return false;
            }
        }

        visiting.Remove(local);
        return values.Count > 0;
    }

    internal static FieldAnalysisContext? FindStaticFieldAtOffset(TypeAnalysisContext owner, long offset)
    {
        if (owner is GenericInstanceTypeAnalysisContext genericOwner)
            return GenericInstanceFieldLayout.FindStaticFieldAtOffset(genericOwner, offset);

        if (owner.GenericParameters.Count > 0)
            return GenericInstanceFieldLayout.FindStaticFieldAtOffset(owner, offset);

        for (var candidateOwner = owner; candidateOwner != null; candidateOwner = candidateOwner.BaseType)
            if (candidateOwner.Fields.FirstOrDefault(f => f.IsStatic
                    && (f.Attributes & FieldAttributes.Literal) == 0
                    && f.Offset == offset) is { } field)
                return field;

        return null;
    }

    // SSA pre-indexed accesses can leave subsequent loads and stores relative to an
    // address alias (alias = root + displacement) rather than the object or array
    // itself. Folding the alias back into the base is an exact substitution, but is
    // only worthwhile where the folded form resolves to a known access shape: an
    // instance field at that offset, the array length slot, or an element boundary.
    private static bool NormalizeObjectAddressAliases(MethodAnalysisContext method)
    {
        var instructions = method.ControlFlowGraph!.Instructions;
        var definitions = instructions.Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!)
            .Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var changed = false;
        foreach (var instruction in instructions)
        for (var i = 0; i < instruction.Operands.Count; i++)
        {
            if (instruction.Operands[i] is not MemoryOperand { Base: LocalVariable alias } memory
                || !definitions.TryGetValue(alias, out var definition)
                || definition is not { OpCode: OpCode.Add or OpCode.Subtract, Operands: [_, LocalVariable root, Immediate displacement] }
                || ReferenceEquals(root, alias)
                || EffectiveObjectType(root, definitions, method.DeclaringType) is not { } rootType
                || rootType.IsValueType && !root.IsThis)
                continue;
            // ldarg.0 of a struct method's own `this` is &T, so this + disp is interior
            // addressing just like object + disp is for references.
            var signed = definition.OpCode == OpCode.Subtract ? -displacement.Value : displacement.Value;
            long offset;
            try { offset = checked(memory.Addend + signed); }
            catch (System.OverflowException) { continue; }
            var folded = memory;
            folded.Base = root;
            folded.Addend = offset;
            if (!ResolvesToKnownAccess(rootType, folded, pointerSize))
                continue;
            instruction.SetOperand(i, folded);
            changed = true;
        }
        return changed;
    }

    private static TypeAnalysisContext? EffectiveObjectType(LocalVariable local,
        IReadOnlyDictionary<LocalVariable, Instruction> definitions,
        TypeAnalysisContext? thisType = null) =>
        EffectiveObjectType(local, definitions, [], thisType);

    private static TypeAnalysisContext? EffectiveObjectType(LocalVariable local,
        IReadOnlyDictionary<LocalVariable, Instruction> definitions, HashSet<LocalVariable> visiting,
        TypeAnalysisContext? thisType)
    {
        // `this` denotes the declaring type's instance (byref interior on
        // structs), which is strictly more informative than an erased placeholder
        // annotation like System.Object. A real carried type - including the
        // generic instantiation X<T0> the field layout needs - always wins.
        var fallback = local.IsThis && thisType != null
            && (local.Type == null || local.Type.FullName == "System.Object")
            ? thisType
            : local.Type;
        if (!visiting.Add(local) || !definitions.TryGetValue(local, out var definition))
            return fallback;

        var recovered = definition switch
        {
            { OpCode: OpCode.Newobj, Operands.Count: > 1 } => definition.Operands[1] switch
            {
                RuntimeClassTypeAnalysisContext runtimeClass => runtimeClass.RepresentedType,
                TypeAnalysisContext allocatedType => allocatedType,
                LocalVariable { Type: RuntimeClassTypeAnalysisContext runtimeClass } => runtimeClass.RepresentedType,
                _ => null,
            },
            { OpCode: OpCode.Move, Operands: [_, LocalVariable source] }
                => EffectiveObjectType(source, definitions, visiting, thisType),
            // A local holding a field's / element's / cast's loaded value carries that
            // value's managed type, even when the local itself was never annotated.
            { OpCode: OpCode.Move, Operands: [_, FieldReference field] }
                => field.Field.FieldType,
            { OpCode: OpCode.Move, Operands: [_, SelectedFieldReference selected] }
                => selected.FieldType,
            { OpCode: OpCode.Move, Operands: [_, ReferenceCast cast] }
                => cast.Type,
            { OpCode: OpCode.Move, Operands: [_, ArrayAccess access] }
                => EffectiveObjectType(access.Array, definitions, visiting, thisType) is SzArrayTypeAnalysisContext array
                    ? array.ElementType : null,
            // A local holding &valueTypeStorage addresses the storage interior:
            // [v + off] reaches the container's field at off. Reference-typed storage
            // is handled by ResolveAddressedStorageReads instead, where [v] is the
            // slot's own value.
            { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: LocalVariable { Type: { IsValueType: true } addressedType } }] }
                => addressedType,
            { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: FieldReference { Field.FieldType: { IsValueType: true } addressedFieldType } }] }
                => addressedFieldType,
            { OpCode: OpCode.Move, Operands: [_, AddressOf { Target: ArrayAccess element }] }
                => EffectiveObjectType(element.Array, definitions, visiting, thisType) is SzArrayTypeAnalysisContext { ElementType: { IsValueType: true } elementType }
                    ? elementType : null,
            _ => null,
        };

        visiting.Remove(local);
        return recovered ?? fallback;
    }

    private static bool ResolvesToKnownAccess(TypeAnalysisContext owner, MemoryOperand memory, int pointerSize)
    {
        if (owner is SzArrayTypeAnalysisContext arrayType)
            return ArrayRecovery.ResolvesAccess(memory, arrayType, pointerSize);

        if (owner is StaticFieldStorageTypeAnalysisContext staticStorage)
            return memory.Index == null && memory.Scale == 0
                && FindStaticFieldAtOffset(staticStorage.OwnerType, memory.Addend) != null;

        return memory.Index == null && memory.Scale == 0
            && FindInstanceFieldPathAtOffset(owner, memory.Addend, memory.AccessSize) != null;
    }

    internal static (FieldAnalysisContext Container, FieldAnalysisContext Field)? FindNestedInstanceFieldAtOffset(
        TypeAnalysisContext owner, long offset, int accessSize)
    {
        if (accessSize <= 0)
            return null;

        if (owner is GenericInstanceTypeAnalysisContext genericOwner)
        {
            var containing = GenericInstanceFieldLayout.FindFieldContainingOffset(genericOwner, offset);
            if (containing is not { Field.FieldType.IsValueType: true } range
                || range.Size == accessSize)
                return null;
            var relativeOffset = offset - range.Offset;
            var nested = range.Field.FieldType is GenericInstanceTypeAnalysisContext nestedGeneric
                ? GenericInstanceFieldLayout.FindFieldContainingOffset(nestedGeneric, relativeOffset) is
                    { Offset: var nestedFieldOffset, Size: var nestedFieldSize, Field: var concrete }
                    && nestedFieldOffset == relativeOffset && nestedFieldSize == accessSize ? concrete : null
                : range.Field.FieldType.Fields.FirstOrDefault(field => !field.IsStatic
                    && (field.BackingData?.FieldOffset ?? field.Offset) == relativeOffset
                    && PrimitiveStorageSize(field.FieldType, owner.AppContext.Binary.PointerSizeBytes) == accessSize);
            return nested == null ? null : (range.Field, nested);
        }

        if (owner.GenericParameters.Count > 0)
            return null;

        for (var candidate = owner; candidate != null; candidate = candidate.BaseType)
        {
            // generic candidates' field offsets are layout placeholders, not real offsets
            if (candidate is GenericInstanceTypeAnalysisContext || candidate.GenericParameters.Count > 0)
                continue;

            foreach (var container in candidate.Fields.Where(f => !f.IsStatic && f.FieldType.IsValueType)
                         .OrderByDescending(f => f.Offset))
            {
                var relativeOffset = offset - container.Offset;
                if (relativeOffset < 0 || PrimitiveStorageSize(container.FieldType, owner.AppContext.Binary.PointerSizeBytes) == accessSize)
                    continue;

                var nested = container.FieldType.Fields.FirstOrDefault(f => !f.IsStatic
                    && f.Offset == relativeOffset
                    && PrimitiveStorageSize(f.FieldType, owner.AppContext.Binary.PointerSizeBytes) == accessSize);
                if (nested != null)
                    return (container, nested);
            }
        }

        return null;
    }

    // A native store can land strictly inside a value-typed instance field - the
    // object the base operand names is only the outermost level: a state machine
    // keeps struct awaiters, enumerators and wrapper structs as fields, so
    // [this + K] may write `this.awaiter.cancellationToken`, not any field
    // sitting at K directly. Descend through value-typed containers collecting
    // every member boundary the access covers exactly, shallowest first; each
    // candidate leaf is provably a member the binary writes, and the caller
    // picks the one the stored value can actually carry (a whole struct write
    // for a struct-typed source, or the member inside it for a primitive one).
    // Anything else - past every field, inside reference-typed storage,
    // part-way through a member, or a store whose width is unknown - yields no
    // candidate and keeps its diagnostic.
    internal static List<(FieldAnalysisContext Field, IReadOnlyList<FieldAnalysisContext> Containers)>?
        FindInteriorInstanceFieldPaths(TypeAnalysisContext owner, long offset, int accessSize)
    {
        if (accessSize <= 0)
            return null;

        var pointerSize = owner.AppContext.Binary.PointerSizeBytes;
        var paths = new List<(FieldAnalysisContext, IReadOnlyList<FieldAnalysisContext>)>();
        var containers = new List<FieldAnalysisContext>();
        var current = owner;
        var relative = offset;
        for (var depth = 0; depth < 8; depth++)
        {
            if (FindFieldCovering(current, relative, pointerSize) is not { } hit)
                break;
            var (field, fieldOffset, fieldSize) = hit;
            if (fieldOffset == relative && fieldSize == accessSize)
                paths.Add((field, containers.ToArray()));
            if (!field.FieldType.IsValueType)
                break;
            containers.Add(field);
            current = field.FieldType;
            relative -= fieldOffset;
        }

        return paths.Count == 0 ? null : paths;
    }

    // The single instance field whose byte range covers the offset, on the type
    // or any of its bases. Generic definitions and generic instances both keep
    // placeholder metadata offsets, so their layout comes from
    // GenericInstanceFieldLayout instead.
    private static (FieldAnalysisContext Field, long Offset, long Size)? FindFieldCovering(
        TypeAnalysisContext owner, long offset, int pointerSize)
    {
        for (var candidate = owner; candidate != null; candidate = candidate.BaseType)
        {
            if (candidate is GenericInstanceTypeAnalysisContext genericCandidate)
            {
                if (GenericInstanceFieldLayout.FindFieldContainingOffset(genericCandidate, offset)
                    is { } genericHit)
                    return genericHit;
                continue;
            }
            if (candidate.GenericParameters.Count > 0)
                continue;
            foreach (var field in candidate.Fields.Where(f => !f.IsStatic
                         && (f.Attributes & FieldAttributes.Literal) == 0))
            {
                var fieldOffset = field.BackingData?.FieldOffset ?? field.Offset;
                var size = GenericInstanceFieldLayout.FieldStorageSize(field.FieldType, pointerSize);
                if (size > 0 && offset >= fieldOffset && offset < fieldOffset + size)
                    return (field, fieldOffset, size);
            }
        }

        return null;
    }

    private static int? PrimitiveStorageSize(TypeAnalysisContext type, int pointerSize)
    {
        if (!type.IsValueType)
            return pointerSize;
        if (type.IsEnumType)
            return PrimitiveStorageSize(type.EnumUnderlyingType
                                        ?? type.Fields.FirstOrDefault(f => !f.IsStatic)?.FieldType
                                        ?? type.AppContext.SystemTypes.SystemInt32Type,
                pointerSize);
        return type.FullName switch
        {
            "System.Boolean" or "System.Byte" or "System.SByte" => 1,
            "System.Int16" or "System.UInt16" or "System.Char" => 2,
            "System.Int32" or "System.UInt32" or "System.Single" => 4,
            "System.Int64" or "System.UInt64" or "System.Double" => 8,
            "System.IntPtr" or "System.UIntPtr" => pointerSize,
            _ => null
        };
    }

    // Mirrors the owner selection in ResolveFieldOffsets: generic definitions have
    // all-0 metadata offsets, so their layout is recomputed instead. A generic
    // instance's own fields are recomputed that way too, but fields inherited from a
    // non-generic base keep their real metadata offsets, so the whole chain is searched.
    internal static FieldAnalysisContext? FindInstanceFieldAtOffset(TypeAnalysisContext owner, long offset)
    {
        if (owner is GenericInstanceTypeAnalysisContext genericOwner)
        {
            // Own-field layout is recomputed on the instantiated field types, so value-type
            // arguments land at the offsets the runtime produced; inherited fields on the chain
            // keep their real metadata offsets, so fall through to the walk.
            if (GenericInstanceFieldLayout.FindFieldAtOffset(genericOwner, offset) is { } ownField)
                return ownField;
        }
        else if (owner.GenericParameters.Count > 0
                 && GenericInstanceFieldLayout.FindFieldAtOffset(owner, offset) is { } openOwnerField)
        {
            return openOwnerField;
        }

        for (var candidate = owner; candidate != null; candidate = candidate.BaseType)
        {
            if (candidate is GenericInstanceTypeAnalysisContext genericCandidate)
            {
                if (GenericInstanceFieldLayout.FindFieldAtOffset(genericCandidate, offset) is { } genericField)
                    return genericField;
                continue; // a generic instance's metadata offsets are layout placeholders, never real
            }
            if (candidate.GenericParameters.Count > 0)
            {
                if (GenericInstanceFieldLayout.FindFieldAtOffset(candidate, offset) is { } openGenericField)
                    return openGenericField;
                continue;
            }
            if (candidate.Fields.FirstOrDefault(f => !f.IsStatic
                    && (f.Attributes & FieldAttributes.Literal) == 0 // consts have no storage but their metadata offset is 0, which would match
                    && (f.BackingData?.FieldOffset ?? f.Offset) == offset) is { } field)
                return field;
        }

        return null;
    }

    private static void ResolveCalls(MethodAnalysisContext method)
    {
        var recoveredImplicitHelpers = new HashSet<Block>();
        foreach (var block in method.ControlFlowGraph!.Blocks)
        {
            if (block.BlockType != BlockType.Call && block.BlockType != BlockType.TailCall)
                continue;

            var callInstruction = block.Instructions[^1];
            if (callInstruction.Operands[0] is not Immediate dest)
                continue;

            var target = dest.UnsignedValue;

            var keyFunctionAddresses = method.AppContext.GetOrCreateKeyFunctionAddresses();

            if (keyFunctionAddresses.IsKeyFunctionAddress(target))
            {
                HandleKeyFunction(method.AppContext, callInstruction, target, keyFunctionAddresses);

                if (target == keyFunctionAddresses.il2cpp_codegen_initialize_runtime_metadata_inline
                    && callInstruction is { OpCode: OpCode.Call, Operands: [_, var initResult, var handle, ..] })
                {
                    callInstruction.OpCode = OpCode.Move;
                    callInstruction.SetOperands(initResult, handle);
                }

                continue;
            }

            //Non-key function call. Try to find a single match
            if (!method.AppContext.MethodsByAddress.TryGetValue(target, out var targetMethods))
            {
                // Not a managed method at all. It may be one of the runtime helpers built around an exception
                // type, which either throw it themselves or build it and hand it back for the caller to raise.
                if (ThrowHelperRecovery.GetThrownException(method.AppContext, target) is { } thrown)
                {
                    LowerThrowHelperCall(method, block, callInstruction, thrown,
                        NonReturningHelperRecovery.IsProven(method.AppContext, target), recoveredImplicitHelpers);

                    continue;
                }

                // Otherwise it may be one of the raisers, which throw the exception they are given
                var raisedIndex = callInstruction.OpCode == OpCode.CallVoid ? 1 : 2;

                if (callInstruction.Operands.Count > raisedIndex && ThrowHelperRecovery.IsExceptionRaiser(method.AppContext, target))
                {
                    var raised = callInstruction.Operands[raisedIndex];

                    callInstruction.OpCode = OpCode.Throw;
                    callInstruction.SetOperands(raised);
                }

                continue;
            }

            // Duplicated/Shared method bodies are resolved later in ResolveCallsViaMethodInfo/ResolveAmbiguousCalls.
            if (targetMethods is not [{ } singleTargetMethod])
                continue;

            callInstruction.SetOperand(0, singleTargetMethod);
            singleTargetMethod.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(callInstruction, singleTargetMethod);
        }

        method.ControlFlowGraph.MergeCallBlocks();
    }

    // A helper built around an exception type either raises it (proven non-returning, or
    // its result is never read) or hands the constructed exception back for the caller to
    // raise. A proven non-returning helper always lowers to Throw: keeping the call's
    // fall-through edge alive via Newobj lets downstream joins read locals that no path
    // to them assigns (CS0165 in decompiled output), while every real reader of the
    // produced value is unreachable anyway because the call cannot return.
    internal static void LowerThrowHelperCall(MethodAnalysisContext method, Block block,
        Instruction callInstruction, TypeAnalysisContext thrown, bool isProvenNonReturning,
        HashSet<Block> recoveredImplicitHelpers)
    {
        var produced = callInstruction.Destination as LocalVariable;
        var hasReader = produced != null
            && method.ControlFlowGraph!.Instructions.Any(i => i.Sources.Any(s => ReferenceEquals(s, produced)));

        // Implicit-failure equivalence must be evaluated before the opcode mutates:
        // it expects the block's last instruction to still be the call.
        var implicitFailure = isProvenNonReturning
            && InjectedCheckRemover.HasEquivalentImplicitFailure(method, block, thrown.FullName, recoveredImplicitHelpers);

        if (isProvenNonReturning || !hasReader)
        {
            callInstruction.OpCode = OpCode.Throw;
            callInstruction.SetOperands(thrown);
            if (implicitFailure)
                recoveredImplicitHelpers.Add(block);
            else if (hasReader)
                // A bare Throw block reads to the injected-check remover as an il2cpp
                // check epilogue; a raise whose result was still consumed is not one,
                // so tag the instruction to keep its guarding branches intact.
                callInstruction.ThrowFromNonReturningCall = true;
        }
        else
        {
            callInstruction.OpCode = OpCode.Newobj;
            callInstruction.SetOperands(produced!, thrown);
        }
    }

    /// <summary>
    /// Resolves calls whose address maps to more than one method by matching the receiver's known
    /// type against the candidates' declaring types. Runs inside the type/field fixpoint and so
    /// re-fires as receivers become typed - a resolved call types its return value, which can type
    /// the receiver of a further call. Returns whether any call was resolved this pass.
    ///
    /// Conservative by design: it commits only when exactly one non-static candidate's declaring
    /// type matches the receiver's type. Anything still untyped or ambiguous is left for a later
    /// pass, or left unresolved - it never guesses.
    /// </summary>
    public static bool ResolveAmbiguousCalls(MethodAnalysisContext method)
    {
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (!instruction.IsCall)
                continue;

            // A resolved call's target is a method/key-function name; only unresolved ones are still numeric.
            if (instruction.Operands[0] is not Immediate target)
                continue;

            if (!method.AppContext.MethodsByAddress.TryGetValue(target.UnsignedValue, out var candidates) || candidates.Count < 2)
                continue;

            // e.g. string.Equals and string.op_Equality, identical params, instance type, and bodies are shared
            // we can't differentiate which is being called but it doesn't matter
            if (AreInterchangeable(candidates))
            {
                var preferred = PreferredOf(candidates);
                instruction.SetOperand(0, preferred);
                preferred.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, preferred);
                changed = true;
                continue;
            }

            // A shared generic wrapper (for example ClearListAtExit<T>.Dispose)
            // can lose its stack receiver type while every address candidate still
            // names the same base method. Rebuild that declaring instantiation from
            // the enclosing method's generic parameters instead of leaving a known
            // managed call unresolved.
            var baseMethods = candidates.Select(BaseMethodOf).Distinct().ToList();
            if (baseMethods is [{ DeclaringType: { } baseDeclaring } baseMethod]
                && baseDeclaring.GenericParameters.Count > 0
                && baseDeclaring.GenericParameters.Count == method.GenericParameters.Count)
            {
                var concrete = new ConcreteGenericMethodAnalysisContext(baseMethod, method.GenericParameters, []);
                instruction.SetOperand(0, concrete);
                concrete.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, concrete);
                changed = true;
                continue;
            }

            if (GetReceiver(instruction) is not { Type: { } receiverType } receiver)
                continue;

            // Prefer picking base ctor if we are a ctor
            var callerIsCtor = method.Name == ".ctor" && receiver.IsThis;

            // Handle methods with shared bodies
            var match = default(MethodAnalysisContext);

            for (var type = receiverType; type != null && match == null; type = type.BaseType)
            {
                var matches = candidates.Where(c => !c.IsStatic && IsSameType(c.DeclaringType, type)).ToList();

                if (matches.Count > 1 && callerIsCtor)
                    matches = matches.Where(c => c.Name == ".ctor").ToList();

                if (matches.Count > 1)
                    break;

                match = matches.SingleOrDefault();
            }

            if (match == null)
                continue;

            instruction.SetOperand(0, match);
            match.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, match);
            changed = true;
        }

        return changed;
    }

    private static bool AreInterchangeable(List<MethodAnalysisContext> candidates)
    {
        var first = candidates[0];

        return candidates.All(c => c.IsStatic == first.IsStatic
            && ReferenceEquals(c.DeclaringType, first.DeclaringType)
            && ReferenceEquals(c.ReturnType, first.ReturnType)
            && c.Parameters.Count == first.Parameters.Count
            && SameParameterTypes(c, first));
    }

    private static bool SameParameterTypes(MethodAnalysisContext a, MethodAnalysisContext b)
    {
        for (var i = 0; i < a.Parameters.Count; i++)
        {
            if (!ReferenceEquals(a.Parameters[i].ParameterType, b.Parameters[i].ParameterType))
                return false;
        }

        return true;
    }

    // Prefer operators if possible
    private static MethodAnalysisContext PreferredOf(List<MethodAnalysisContext> candidates) =>
        candidates.FirstOrDefault(c => c.Name.StartsWith("op_")) ?? candidates[0];

    // The receiver ('this') of a call is the first integer-slot argument: operand 1 for CallVoid
    // (after the target), operand 2 for Call (after the target and the return value).
    // A value type receiver is passed byref, so it arrives as an AddressOf over the local.
    private static LocalVariable? GetReceiver(Instruction call)
    {
        var index = call.OpCode == OpCode.CallVoid ? 1 : 2;

        return index < call.Operands.Count
            ? call.Operands[index] switch
            {
                LocalVariable local => local,
                AddressOf { Target: LocalVariable addressed } => addressed,
                _ => null
            }
            : null;
    }

    // Concrete generic method contexts build their declaring type fresh rather than via the
    // GetOrCreate cache, so generic instances also need comparing structurally.
    // TODO Fix this, concrete generic methods should use GetOrCreate
    private static bool IsSameType(TypeAnalysisContext? a, TypeAnalysisContext? b)
    {
        if (ReferenceEquals(a, b))
            return true;

        if (a is not GenericInstanceTypeAnalysisContext leftInstance
            || b is not GenericInstanceTypeAnalysisContext rightInstance
            || !ReferenceEquals(leftInstance.GenericType, rightInstance.GenericType)
            || leftInstance.GenericArguments.Count != rightInstance.GenericArguments.Count)
            return false;

        for (var i = 0; i < leftInstance.GenericArguments.Count; i++)
        {
            if (!IsSameType(leftInstance.GenericArguments[i], rightInstance.GenericArguments[i]))
                return false;
        }

        return true;
    }

    /// <summary>
    /// Resolves any Call (theoretically should always be a CallVoid) target directly after a Newobj to a constructor call.
    /// </summary>
    public static bool ResolveConstructorCalls(MethodAnalysisContext method)
    {
        var definitions = new Dictionary<LocalVariable, Instruction>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
            if (instruction.Destination is LocalVariable definition)
                definitions[definition] = instruction;

        var changed = false;

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (!instruction.IsCall || instruction.Operands[0] is not Immediate callTarget)
                continue;

            if (!method.AppContext.MethodsByAddress.TryGetValue(callTarget.UnsignedValue, out var candidates))
                continue;

            if (GetReceiver(instruction) is not { } receiver || AllocatedType(receiver, definitions) is not { } allocatedType)
                continue;

            var constructor = candidates.FirstOrDefault(c => !c.IsStatic && c.Name == ".ctor" && ReferenceEquals(c.DeclaringType, allocatedType))
                              ?? FindConstructorForSharedBody(allocatedType, candidates);
            if (constructor == null)
                continue;

            instruction.SetOperand(0, constructor);
            constructor.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, constructor);
            changed = true;
        }

        return changed;
    }

    private static MethodAnalysisContext? FindConstructorForSharedBody(TypeAnalysisContext allocatedType, List<MethodAnalysisContext> candidates)
    {
        var candidateParamCounts = new HashSet<int>(candidates
            .Where(c => c is { IsStatic: false, Name: ".ctor" })
            .Select(c => c.Parameters.Count));

        if (candidateParamCounts.Count == 0)
            return null;

        var definition = allocatedType is GenericInstanceTypeAnalysisContext genericInstance ? genericInstance.GenericType : allocatedType;
        var matches = definition.Methods
            .Where(m => m is { IsStatic: false, Name: ".ctor" } && candidateParamCounts.Contains(m.Parameters.Count))
            .ToList();

        if (matches is not [{ } match])
            return null;

        return allocatedType is GenericInstanceTypeAnalysisContext instance
            ? new ConcreteGenericMethodAnalysisContext(match, instance.GenericArguments, [])
            : match;
    }

    // Follow SSA copies from a local back to the Newobj that produced the value
    private static TypeAnalysisContext? AllocatedType(LocalVariable local, Dictionary<LocalVariable, Instruction> definitions)
    {
        var visited = new HashSet<LocalVariable>();

        while (visited.Add(local) && definitions.TryGetValue(local, out var definition))
        {
            switch (definition.OpCode)
            {
                case OpCode.Newobj:
                    return (definition.Operands[0] as LocalVariable)?.Type;
                case OpCode.Move when definition.Operands[1] is LocalVariable source:
                    local = source;
                    continue;
            }

            break;
        }

        return null;
    }

    /// <summary>
    /// Resolves calls whose address maps to more than one method by reading the runtime
    /// <c>MethodInfo*</c> the caller passes in, if there is one.
    /// </summary>
    public static bool ResolveCallsViaMethodInfo(MethodAnalysisContext method)
    {
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (!instruction.IsCall)
                continue;

            if (GetMethodInfoArgument(instruction) is not { RepresentedMethod: { } representedMethod })
                //No MethodInfo to work with
                continue;

            if (instruction.Operands[0] is MethodAnalysisContext resolved)
            {
                if (!ReferenceEquals(resolved, representedMethod)
                    && ReferenceEquals(BaseMethodOf(resolved), BaseMethodOf(representedMethod))
                    && ErasedGenericArgumentCount(representedMethod) < ErasedGenericArgumentCount(resolved)
                    && ReceiverTypeConsistent(instruction, representedMethod))
                {
                    instruction.SetOperand(0, representedMethod);
                    representedMethod.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, representedMethod);
                    changed = true;
                }
                continue;
            }

            if (instruction.Operands[0] is not Immediate target)
                continue;

            // A concrete MethodInfo* in the exact hidden-argument slot is more
            // authoritative than the shared native thunk's address. A thunk can
            // have one unrelated representative in MethodsByAddress (the common
            // AddComponent<T> case), which previously blocked this recovery.
            var firstArg = instruction.OpCode == OpCode.CallVoid ? 1 : 2;
            var hiddenParamIndex = firstArg
                + (representedMethod.AppContext.InstructionSet.CallingConventionResolver?.ReturnsViaHiddenBuffer(representedMethod) == true ? 1 : 0)
                + (representedMethod.IsStatic ? 0 : 1) + representedMethod.Parameters.Count;
            if (!ReferenceEquals(representedMethod, method)
                && hiddenParamIndex < instruction.Operands.Count
                && AsMethodInfo(instruction.Operands[hiddenParamIndex]) is { RepresentedMethod: { } hiddenMethod }
                && ReferenceEquals(BaseMethodOf(hiddenMethod), BaseMethodOf(representedMethod))
                && ReceiverTypeConsistent(instruction, representedMethod))
            {
                instruction.SetOperand(0, representedMethod);
                representedMethod.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, representedMethod);
                changed = true;
                continue;
            }

            if (!method.AppContext.MethodsByAddress.TryGetValue(target.UnsignedValue, out var candidates))
            {
                // Some shared generic bodies aren't in the address map at all (todo investigate?).
                // Il2cpp still passes the concrete MethodInfo as the hidden final parameter, so we can use a methodof there if we have one.
                // However, make sure it isn't our OWN hidden MethodInfo arg, because that would turn all unknown calls into recursion
                if (ReferenceEquals(representedMethod, method))
                    continue;

                if (hiddenParamIndex >= instruction.Operands.Count
                    || AsMethodInfo(instruction.Operands[hiddenParamIndex]) == null
                    || !ReceiverTypeConsistent(instruction, representedMethod))
                    continue;

                instruction.SetOperand(0, representedMethod);
                representedMethod.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, representedMethod);
                changed = true;
                continue;
            }

            if (candidates.Count < 2)
                continue;

            //Try to actually match on the method name so we don't just replace a call with something else.
            var representedBase = BaseMethodOf(representedMethod);
            if (!candidates.Any(candidate => ReferenceEquals(BaseMethodOf(candidate), representedBase))
                || !ReceiverTypeConsistent(instruction, representedMethod))
                continue;

            instruction.SetOperand(0, representedMethod);
            representedMethod.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, representedMethod);
            changed = true;
        }

        return changed;
    }

    private static int ErasedGenericArgumentCount(MethodAnalysisContext method)
    {
        var count = method.DeclaringType is GenericInstanceTypeAnalysisContext declaring
            ? declaring.GenericArguments.Count(argument => argument.FullName == "System.Object"
                || argument is GenericParameterTypeAnalysisContext)
            : 0;
        if (method is ConcreteGenericMethodAnalysisContext concrete)
            count += concrete.MethodGenericParameters.Count(argument => argument.FullName == "System.Object"
                || argument is GenericParameterTypeAnalysisContext);
        return count;
    }

    // Offset of Il2CppClass::vtable, VirtualInvokeData entries of {methodPtr, MethodInfo*}.
    // TODO this is almost certainly not correct on every version
    private const long VTableOffset64 = 0x138;
    private const long VTableOffset32 = 0xC0;
    
    // Resolves virtual dispatch through <c>[klass + vtableOffset + slot * sizeof(VirtualInvokeData)]</c>
    // as long as the klass local's represented type is known.
    public static bool ResolveVirtualCalls(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var vtableOffset = pointerSize == 8 ? VTableOffset64 : VTableOffset32;
        var invokeDataSize = 2L * pointerSize;
        var changed = false;

        var loads = new Dictionary<LocalVariable, MemoryOperand>();
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode == OpCode.Move
                && instruction.Operands[0] is LocalVariable destination
                && instruction.Operands[1] is MemoryOperand { Index: null, Scale: 0 } load)
                loads[destination] = load;
        }

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (instruction.OpCode is not (OpCode.IndirectCall or OpCode.IndirectJump))
                continue;

            if (SlotLoad(instruction.Operands[0]) is not { } target
                || target.Base is not LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: { } receiverType } } klassLocal)
                continue;

            var offset = target.Addend - vtableOffset;
            if (offset < 0 || offset % invokeDataSize != 0)
                continue;

            var slot = (int)(offset / invokeDataSize);
            if (ResolveVTableSlot(method.AppContext, receiverType, slot) is not { } resolved)
                continue;

            var tail = instruction.OpCode == OpCode.IndirectJump;
            var block = tail ? method.ControlFlowGraph.Blocks.FirstOrDefault(b => b.Instructions.LastOrDefault() == instruction) : null;
            if (resolved.IsStatic || tail && (block == null || method.IsVoid != resolved.IsVoid
                    || !method.IsVoid && method.ReturnType.FullName != resolved.ReturnType.FullName))
                continue;

            var assembly = resolved.DeclaringType?.DeclaringAssembly ?? method.DeclaringType?.DeclaringAssembly;

            if (tail)
            {
                var operands = new List<IOperand> { resolved };
                if (!resolved.IsVoid)
                    operands.Add(new LocalVariable("virtualTailCallResult", resolved.AppContext.InstructionSet.CallingConventionResolver?.ReturnRegister(resolved) ?? new Register(null, "return"), resolved.ReturnType));
                operands.AddRange(instruction.Operands.Skip(2));
                instruction.SetOperands(operands);
            }
            else
            {
                if (resolved.IsVoid)
                    instruction.RemoveOperandAt(1);
                instruction.SetOperand(0, resolved);
            }
            instruction.OpCode = resolved.IsVoid ? OpCode.CallVoid : OpCode.Call;
            instruction.IsVirtualDispatch = true;
            resolved.AppContext.InstructionSet.CallingConventionResolver?.RemapRawArguments(instruction, resolved);

            // the MethodInfo field is also the same method, name it, for cleanliness and so it can
            // serve as a hidden final parameter if needed
            for (var i = 1; i < instruction.Operands.Count && assembly != null; i++)
            {
                if (SlotLoad(instruction.Operands[i]) is { } methodInfoLoad
                    && ReferenceEquals(methodInfoLoad.Base, klassLocal)
                    && methodInfoLoad.Addend == target.Addend + pointerSize)
                    instruction.SetOperand(i, new RuntimeMethodInfoAnalysisContext(resolved, assembly));
            }

            if (tail)
            {
                block!.AddInstruction(new Instruction(-1, OpCode.Return,
                    resolved.IsVoid ? [] : [instruction.Operands[1]]));
                block.CalculateBlockType();
            }

            changed = true;
        }

        return changed;

        MemoryOperand? SlotLoad(IOperand operand) => operand switch
        {
            MemoryOperand { Index: null, Scale: 0 } inlined => inlined,
            LocalVariable local when loads.TryGetValue(local, out var load) => load,
            _ => null
        };
    }

    private static MethodAnalysisContext? ResolveVTableSlot(ApplicationAnalysisContext appContext, TypeAnalysisContext type, int slot)
    {
        var definition = (type as GenericInstanceTypeAnalysisContext)?.GenericType.Definition ?? type.Definition;

        if (definition == null || slot >= definition.VtableCount)
            return null;

        if (appContext.ResolveContextForMethod(definition.VTable[slot]) is { } implementation)
            return implementation;

        // an abstract method has no implementation, try to resolve it
        for (var declarer = type; declarer != null; declarer = declarer.BaseType)
        {
            if (declarer.Methods.FirstOrDefault(m => m.Definition?.slot == slot) is { } declaration)
                return declaration;
        }

        return null;
    }

    private static MethodAnalysisContext BaseMethodOf(MethodAnalysisContext method) =>
        method is ConcreteGenericMethodAnalysisContext { BaseMethodContext: { } baseMethod } ? baseMethod : method;

    private static RuntimeMethodInfoAnalysisContext? GetMethodInfoArgument(Instruction call)
    {
        var firstArg = call.OpCode == OpCode.CallVoid ? 1 : 2;

        for (var i = call.Operands.Count - 1; i >= firstArg; i--)
        {
            if (AsMethodInfo(call.Operands[i]) is { } methodInfo)
                return methodInfo;
        }

        return null;
    }

    private static RuntimeMethodInfoAnalysisContext? AsMethodInfo(IOperand operand) =>
        operand switch
        {
            RuntimeMethodInfoAnalysisContext methodInfo => methodInfo,
            LocalVariable { Type: RuntimeMethodInfoAnalysisContext methodInfoLocal } => methodInfoLocal,
            _ => null
        };

    // The MethodInfo* a call's operand list carries can be a stale register leftover
    // rather than this call's hidden argument - an earlier sibling call's rgctx load
    // still occupies the register. A callee bound from it is only believable when the
    // receiver operand's known type can be the declaring type: a `&SomeStruct` this
    // can never be a class instance, and an `&A` this can never host a method of B.
    private static bool ReceiverTypeConsistent(Instruction call, MethodAnalysisContext representedMethod)
    {
        if (representedMethod.IsStatic || representedMethod.DeclaringType is not { } declaring)
            return true;

        // A hidden return buffer shifts the receiver register on conventions where it
        // consumes an argument slot, and where it does not the buffer is still operand
        // clutter - skip rather than inspect the wrong operand.
        var resolver = representedMethod.AppContext.InstructionSet.CallingConventionResolver;
        if (resolver?.ReturnsViaHiddenBuffer(representedMethod) == true)
            return true;

        var firstArg = call.OpCode == OpCode.CallVoid ? 1 : 2;
        if (firstArg >= call.Operands.Count
            || OperandEmittedType(call.Operands[firstArg]) is not { } receiverType)
            return true;

        if (receiverType is RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext
            or RuntimeClassTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext
            or RgctxTableTypeAnalysisContext or MethodRgctxTableTypeAnalysisContext)
            // Runtime handle operands say nothing about the receiver object.
            return true;

        if (receiverType is not ByRefTypeAnalysisContext { ElementType: { } receiverElement })
            // Only a managed-pointer operand carries reliable receiver evidence: a
            // byref type states what the register points at, while a plain local's
            // static type can be stale (register reuse re-labels a pointer value).
            return true;

        if (receiverElement is GenericParameterTypeAnalysisContext
            || receiverElement.FullName?.Contains("__Il2CppFullySharedGeneric") == true)
            // Shared-generic or erased receivers cannot be checked against a declaring type.
            return true;

        // A managed pointer can be a struct `this`, or a class receiver under
        // `constrained.` (a `&T` holding a T object), or reach the type through
        // the pointed-to struct's offset-0 field (the pointer is the same address).
        if (SameTypeFamily(receiverElement, declaring)
            || ZeroOffsetField(receiverElement, declaring) != null)
            return true;

        // &v.f0 names the same address as &v: treat it as a pointer to V.
        if (call.Operands[firstArg] is AddressOf
            { Target: FieldReference { Offset: 0, Containers: { Count: 0 } } addressedField })
        {
            var addressedStruct = addressedField.Local.Type is ByRefTypeAnalysisContext addressedByRef
                ? addressedByRef.ElementType
                : addressedField.Local.Type;
            if (addressedStruct is { IsValueType: true })
                return SameTypeFamily(addressedStruct, declaring);
        }
        return false;
    }

    private static TypeAnalysisContext? OperandEmittedType(IOperand operand) => operand switch
    {
        LocalVariable local => local.Type,
        FieldReference field => field.Field.FieldType,
        AddressOf { Target: LocalVariable addressed } => addressed.Type is { } localType
            ? new ByRefTypeAnalysisContext(localType)
            : null,
        AddressOf { Target: FieldReference field } => new ByRefTypeAnalysisContext(field.Field.FieldType),
        _ => null,
    };

    // Generic-sharing erases receiver types (a MapField<K,V> body sees MapField<object,object>),
    // so family membership is decided on the generic definitions; a System.Object operand
    // carries no evidence either way. Context objects for one type are not interned, so the
    // erased names are what is compared.
    private static bool SameTypeFamily(TypeAnalysisContext actual, TypeAnalysisContext expected)
    {
        var erasedActual = actual is GenericInstanceTypeAnalysisContext actualInstance
            ? actualInstance.GenericType ?? actual : actual;
        var erasedExpected = expected is GenericInstanceTypeAnalysisContext expectedInstance
            ? expectedInstance.GenericType ?? expected : expected;
        if (ReferenceEquals(erasedActual, erasedExpected)
            || erasedActual.FullName == erasedExpected.FullName
            || erasedActual.FullName is "System.Object")
            return true;
        for (var type = erasedActual; type != null; type = type.BaseType)
        {
            var erased = type is GenericInstanceTypeAnalysisContext instance
                ? instance.GenericType ?? type : type;
            if (erased.FullName == erasedExpected.FullName)
                return true;
            // Interface dispatch reaches the receiver through implements, not extends.
            foreach (var iface in type.InterfaceContexts)
                if ((iface is GenericInstanceTypeAnalysisContext ifaceInstance
                        ? ifaceInstance.GenericType ?? iface : iface).FullName == erasedExpected.FullName)
                    return true;
        }
        for (var type = erasedExpected.BaseType; type != null; type = type.BaseType)
            if ((type is GenericInstanceTypeAnalysisContext instance ? instance.GenericType ?? type : type)
                    .FullName == erasedActual.FullName)
                return true;
        return false;
    }

    private static FieldAnalysisContext? ZeroOffsetField(TypeAnalysisContext owner, TypeAnalysisContext fieldType) =>
        owner.Fields.Where(field => !field.IsStatic && field.Offset == 0 && SameTypeFamily(field.FieldType, fieldType))
            .ToList() is [var field] ? field : null;

    private static void HandleKeyFunction(ApplicationAnalysisContext appContext, Instruction instruction, ulong target, BaseKeyFunctionAddresses kFA)
    {
        var method = "";
        if (kFA.WriteBarrierAliases.Contains(target))
            method = nameof(kFA.il2cpp_codegen_write_barrier);
        else if (kFA.BoxAliases.Contains(target))
            method = nameof(kFA.il2cpp_vm_object_box);
        else if (target == kFA.il2cpp_codegen_initialize_method || target == kFA.il2cpp_codegen_initialize_runtime_metadata)
        {
            if (appContext.MetadataVersion < 27)
            {
                method = nameof(kFA.il2cpp_codegen_initialize_method);
            }
            else
            {
                method = nameof(kFA.il2cpp_codegen_initialize_runtime_metadata);
            }
        }
        else
        {
            var pairs = kFA.Pairs.ToList();
            var key = pairs.FirstOrDefault(pair => pair.Value == target).Key;
            if (key == null)
                return;
            method = key;
        }

        if (method != "")
        {
            instruction.SetOperand(0, new StringLiteral(method));
        }
    }

    // Because of il2cpp fields (like cctor_finished_or_no_cctor) [local @ reg+offset] sometimes can't be resolved, but this works for now
    private static void ResolveGetter(MethodAnalysisContext method)
    {
        if (!method.Name.StartsWith("get_"))
            return;

        // Default get: Return [this @ reg+offset]
        var instructions = method.ControlFlowGraph!.Instructions;
        if (instructions.Count == 1)
        {
            var instr = instructions[0];

            if (instr.OpCode != OpCode.Return
                || instr.Operands.Count < 1
                || instr.Operands[0] is not MemoryOperand memory
                || memory.Index != null || memory.Scale != 0
                || memory.Base is not LocalVariable local)
                return;

            var fieldName = $"<{method.Name[4..]}>k__BackingField";

            var field = method.DeclaringType!.Fields.Find(f => f.Name == fieldName);
            if (field == null)
                return;

            instr.SetOperand(0, new FieldReference(field, local, (int)memory.Addend));
        }
    }
}
