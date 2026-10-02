using System.Collections.Generic;
using System.Linq;
using System.Reflection;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;
using Cpp2IL.Core.Utils;

namespace Cpp2IL.Core.Analysis;

public static class LocalVariables
{
    public static int MaxTypePropagationLoopCount = 5000;

    private const long StaticFieldsOffset64 = 0xB8;
    private const long StaticFieldsOffset32 = 0x5C;

    public static void CreateAll(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        var instructions = cfg.Instructions;

        // Get all registers
        var registers = new List<Register>();
        foreach (var instruction in instructions)
            registers.AddRange(GetRegisters(instruction));

        // Remove duplicates
        registers = registers.Distinct().ToList();

        // Map those to locals
        var locals = new Dictionary<Register, LocalVariable>();
        for (var i = 0; i < registers.Count; i++)
        {
            var register = registers[i];
            locals.Add(register, new LocalVariable($"v{i}", register));
        }

        // Replace registers with locals
        foreach (var instruction in instructions)
        {
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                var operand = instruction.Operands[i];

                if (operand is Register register)
                    instruction.SetOperand(i, locals[register]);

                if (operand is AddressOf { Target: Register addressed })
                    instruction.SetOperand(i, new AddressOf(locals[addressed]));

                if (operand is MemoryOperand memory)
                {
                    if (memory.Base != null)
                    {
                        var baseRegister = (Register)memory.Base;
                        memory.Base = locals[baseRegister];
                    }

                    if (memory.Index != null)
                    {
                        var index = (Register)memory.Index;
                        memory.Index = locals[index];
                    }

                    instruction.SetOperand(i, memory);
                }
            }
        }

        method.Locals = locals.Select(kv => kv.Value).ToList();

        // Return local names
        var retValIndex = 0;
        foreach (var instruction in instructions)
        {
            if (instruction.OpCode != OpCode.Return || instruction.Operands.Count != 1) continue;

            var returnLocal = (LocalVariable)instruction.Sources[0];

            returnLocal.Name = $"returnVal{retValIndex + 1}";
            returnLocal.IsReturn = true;
            retValIndex++;
        }

        // Add parameter names
        var paramLocals = new List<LocalVariable>();

        var operandOffset = method.IsStatic ? 0 : 1; // 'this'

        // 'this' param
        if (!method.IsStatic && method.Locals.Count > 0 && method.ParameterOperands.Count > 0)
        {
            var thisOperand = (Register)method.ParameterOperands[0];
            var thisLocal = method.Locals.FirstOrDefault(l => l.Register.Number == thisOperand.Number && l.Register.Version == -1);

            if (thisLocal != null)
            {
                thisLocal.Name = "this";
                thisLocal.IsThis = true;
                paramLocals.Add(thisLocal);
            }
        }

        // Check if method has MethodInfo*
        var hasMethodInfo = (method.ParameterOperands.Count - operandOffset) > method.Parameters.Count;
        var methodInfoIndex = method.ParameterOperands.Count - 1;

        // Add normal parameter names
        for (var i = 0; i < method.Parameters.Count; i++)
        {
            var operandIndex = i + operandOffset;
            if (hasMethodInfo && operandIndex == methodInfoIndex)
                break; // Skip MethodInfo*

            if (operandIndex >= method.ParameterOperands.Count)
                break;

            if (method.ParameterOperands[operandIndex] is not Register reg)
                continue;

            var local = method.Locals.FirstOrDefault(l => l.Register.Number == reg.Number && l.Register.Version == -1);
            if (local == null)
                continue;

            local.Name = method.Parameters[i].ParameterName;
            paramLocals.Add(local);
        }

        // Add MethodInfo*
        if (hasMethodInfo)
        {
            var methodInfoOperand = (Register)method.ParameterOperands[methodInfoIndex];
            var methodInfoLocal = method.Locals.FirstOrDefault(l => l.Register.Number == methodInfoOperand.Number && l.Register.Version == -1);

            if (methodInfoLocal != null)
            {
                methodInfoLocal.Name = "methodInfo";
                methodInfoLocal.IsMethodInfo = true;
                paramLocals.Add(methodInfoLocal);
            }
        }

        method.ParameterLocals = paramLocals;

        // the hidden return buffer takes the first argument register. we type it as the return
        // type so stores into it resolve to fields
        if (method.AppContext.Binary.PointerSizeBytes == 8
            && method.AppContext.InstructionSet.CallingConventionResolver?.HiddenReturnBufferRegister(method) is { } bufferRegister
            && method.Locals.FirstOrDefault(l => l.Register.Number == bufferRegister.Number && l.Register.Version == -1) is { } bufferLocal)
        {
            bufferLocal.Name = "returnBuffer";
            bufferLocal.Type = method.ReturnType;
            // The result is what the method built in the buffer; x0 at `ret` holds nothing of it.
            foreach (var ret in method.ControlFlowGraph!.Instructions)
                if (ret is { OpCode: OpCode.Return, Operands.Count: > 0 })
                    ret.SetOperands([bufferLocal]);
        }

        // Runs here, not with the rest of type resolution: the sibling
        // `Move(Vn, …)` lane definitions it reads are removed by the first
        // dead-code pass, which runs before ResolveTypesAndFields.
        VectorLanePacking.Run(method);
    }

    public static void RemoveUnused(MethodAnalysisContext method)
    {
        var cfg = method.ControlFlowGraph!;
        cfg.BuildUseDefLists();

        var usedLocals = new HashSet<LocalVariable>();

        foreach (var block in cfg.Blocks)
        {
            foreach (var usedVar in block.Use.OfType<LocalVariable>())
                usedLocals.Add(usedVar);

            foreach (var definedVar in block.Def.OfType<LocalVariable>())
                usedLocals.Add(definedVar);

            // Use/def only sees top-level LocalVariable operands, but a local can be
            // referenced only through a nested operand - a field lane inside an array
            // index, an addressed field's receiver, a selected field's owner.
            // Emission resolves any of those through the locals table, so a local
            // reachable through any operand shape stays registered.
            foreach (var instruction in block.Instructions)
                foreach (var operand in instruction.Operands)
                    foreach (var nested in OperandLocals(operand))
                        usedLocals.Add(nested);
        }

        method.Locals.RemoveAll(x => !usedLocals.Contains(x));
    }

    // Every local an operand can reach, through any nesting the emitter walks:
    // field receivers, array bases and indices, addressed targets, casts.
    internal static IEnumerable<LocalVariable> OperandLocals(IOperand operand)
    {
        switch (operand)
        {
            case LocalVariable local:
                yield return local;
                break;
            case FieldReference field:
                yield return field.Local;
                break;
            case SelectedFieldReference selected:
                yield return selected.Selector;
                foreach (var (_, choiceField) in selected.Choices)
                    yield return choiceField.Local;
                break;
            case AddressOf { Target: { } target }:
                foreach (var nested in OperandLocals(target))
                    yield return nested;
                break;
            case ArrayAccess access:
                yield return access.Array;
                foreach (var nested in OperandLocals(access.Index))
                    yield return nested;
                break;
            case ArrayElementFieldReference elementField:
                yield return elementField.Array;
                foreach (var nested in OperandLocals(elementField.Index))
                    yield return nested;
                break;
            case ArrayLength arrayLength:
                yield return arrayLength.Array;
                break;
            case MemoryOperand memory:
                if (memory.Base is { } memoryBase)
                    foreach (var nested in OperandLocals(memoryBase))
                        yield return nested;
                if (memory.Index is { } memoryIndex)
                    foreach (var nested in OperandLocals(memoryIndex))
                        yield return nested;
                break;
            case ReferenceCast cast:
                yield return cast.Value;
                break;
        }
    }

    private static List<Register> GetRegisters(Instruction instruction)
    {
        var registers = new List<Register>();

        foreach (var implicitDefinition in instruction.ImplicitDefinitions)
            if (!registers.Contains(implicitDefinition))
                registers.Add(implicitDefinition);

        foreach (var operand in instruction.Operands)
        {
            if (operand is AddressOf { Target: Register addressed })
            {
                if (!registers.Contains(addressed))
                    registers.Add(addressed);
            }

            if (operand is Register register)
            {
                if (!registers.Contains(register))
                    registers.Add(register);
            }

            if (operand is MemoryOperand memory)
            {
                if (memory.Base != null)
                {
                    var baseRegister = (Register)memory.Base;
                    if (!registers.Contains(baseRegister))
                        registers.Add(baseRegister);
                }

                if (memory.Index != null)
                {
                    var index = (Register)memory.Index;
                    if (!registers.Contains(index))
                        registers.Add(index);
                }
            }
        }

        return registers;
    }

    /// <summary>
    /// Resolves field accesses and propagates types together, to a fixpoint, while the method is
    /// still in SSA form (every local has a single, version-stable definition).
    ///
    /// The two are mutually enabling and so cannot be ordered as separate passes: a typed base lets
    /// <see cref="MetadataResolver.ResolveFieldOffsets"/> turn <c>[base + offset]</c> into a
    /// <see cref="FieldReference"/>, a resolved field load types its result with the field's type,
    /// and that result is in turn the base of the next access (directly, or after flowing through
    /// moves/phis). Both steps are monotonic - each only ever resolves an operand or fills a
    /// previously-unknown type - so the loop converges.
    /// </summary>
    public static void ResolveTypesAndFields(MethodAnalysisContext method)
    {
        // Seed types from fixed ground truth - the method's own signature, and type-metadata global
        // loads. Applied once up front and, being applied first, they win over anything inferred later.
        PropagateFromReturn(method);
        PropagateFromParameters(method);
        SeedRuntimeClassTypes(method);
        SeedIl2CppDefaultsClassTypes(method);
        SeedNewobjResults(method);
        SeedMethodInfoTypes(method);
        SeedComparisonResults(method);
        SeedFloatLiterals(method);
        SeedNativeIntegerWidths(method);
        SeedNativeFloatWidths(method);

        ResolveHiddenReturnBuffers(method);

        // Everywhere there's a CallVoid after a Newobj, we can resolve the constructor call.
        MetadataResolver.ResolveConstructorCalls(method);

        // Everything else is mutually enabling and so runs to a fixpoint: a typed receiver lets an
        // ambiguous call resolve, a resolved call types its return value and arguments, a typed base
        // lets a field offset resolve, a field load types its result, and any of those can be the
        // receiver/base of the next step. Every pass is monotonic - it only resolves an operand or
        // fills a previously-unknown type - so the loop converges.
        var changed = true;
        var loopCount = 0;
        var hiddenReturnsSharpened = false;
        var allowCanonicalCallTypes = false;

        while (changed)
        {
            if (MaxTypePropagationLoopCount != -1 && ++loopCount > MaxTypePropagationLoopCount)
                throw new DecompilerException($"Type and field resolution not settling! (looped {MaxTypePropagationLoopCount} times)");

            changed = false;
            changed |= MetadataResolver.ResolveCallsViaMethodInfo(method);
            changed |= MetadataResolver.ResolveAmbiguousCalls(method);
            changed |= MetadataResolver.ResolveVirtualCalls(method);
            changed |= PropagateFromCallParameters(method, allowCanonicalCallTypes);
            changed |= AggregateResultLanes.Run(method);
            changed |= PackedRegisterFields.Run(method);
            changed |= MetadataResolver.LoadThroughMergedAddresses(method);
            changed |= MetadataResolver.ResolveFieldOffsets(method);
            changed |= ResolveSharpenedFieldOwners(method);
            changed |= RgctxResolver.Run(method);
            changed |= PropagateStaticFieldStorage(method);
            changed |= TypeAddressedLocals(method, allowCanonicalCallTypes);
            changed |= PropagateTypesOnce(method);
            changed |= ResolveStackAggregateFields(method);
            changed |= RewriteAggregateFieldStores(method);
            changed |= InheritEscapedCellVersions(method);

            // Hidden struct returns are discovered before field/type propagation, when a shared-
            // generic receiver may still be untyped. Once the regular fixpoint settles, use its
            // concrete receiver type to sharpen the return and run the same fixpoint once more.
            if (!changed && !hiddenReturnsSharpened)
            {
                hiddenReturnsSharpened = true;
                changed = SharpenHiddenReturnBuffers(method);
            }

            // Let metadata copies, RGCTX loads and receiver producers settle before a shared
            // implementation can seed erased types. Otherwise those types survive a later
            // concrete MethodInfo resolution and poison copies/phis and field lookup.
            if (!changed && !allowCanonicalCallTypes)
            {
                changed = MetadataResolver.ResolveAmbiguousCalls(method, specializeReceivers: true);
                if (!changed)
                {
                    allowCanonicalCallTypes = true;
                    changed = true;
                }
            }
        }

        // Where a vector binop's destination register view carries a sibling
        // lifetime's scalar type, the def site gets its own vector-typed local.
        SplitVectorBinopDefSites(method);

        // With every local's stack kind resolved, operand positions whose kind is
        // incompatible with the whole-register local they read can be split off to
        // the register's lane-0 view - the slot the scalar operation actually sees.
        SplitScalarOperandViews(method);
        VectorLanePacking.SurrenderPackedArgs(method);
    }

    private static bool ResolveStackAggregateFields(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var roots = method.Locals
            .Select(local => (Local: local, Offset: TryStackOffset(local.Register.Name), Size:
                local.Type is { IsValueType: true } type ? TypeSizes.MinimumUnboxedSize(type, pointerSize) : 0))
            .Where(candidate => candidate.Offset != null && candidate.Size > pointerSize)
            .ToList();
        var changed = false;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        for (var operandIndex = 0; operandIndex < instruction.Operands.Count; operandIndex++)
        {
            if (operandIndex == 0 && instruction.IsAssignment
                || instruction.Operands[operandIndex] is not LocalVariable slot
                || TryStackOffset(slot.Register.Name) is not { } slotOffset)
                continue;
            var accessSize = instruction.NativeMemoryAccessSize
                ?? (int)System.Math.Min(TypeSizes.MinimumUnboxedSize(
                    slot.Type ?? method.AppContext.SystemTypes.SystemObjectType, pointerSize), int.MaxValue);
            if (accessSize <= 0)
                continue;
            var matches = roots.Select(root =>
                {
                    var relativeOffset = slotOffset - root.Offset!.Value;
                    var nested = relativeOffset > 0
                        ? MetadataResolver.FindNestedInstanceFieldPathAtOffset(root.Local.Type!, relativeOffset, accessSize)
                        : null;
                    return (Root: root.Local, Offset: relativeOffset, Nested: nested);
                })
                .Where(match => match.Nested != null)
                .ToList();
            if (matches.Count == 0)
                continue;
            var nearestOffset = matches.Min(match => match.Offset);
            var nearest = matches.Where(match => match.Offset == nearestOffset)
                .GroupBy(match => (match.Root.Register.Number, match.Nested!.Value.Field))
                .Select(group => group.First())
                .ToList();
            if (nearest.Count != 1)
                continue;
            var match = nearest[0];
            if (MetadataResolver.MemberPathUnspellable(match.Nested!.Value, method,
                    instruction.OpCode == OpCode.Move && operandIndex == 0, addressed: false))
                continue;
            instruction.SetOperand(operandIndex, new FieldReference(match.Nested!.Value.Field,
                match.Root, match.Offset, match.Nested.Value.Containers, accessSize));
            if (instruction.OpCode == OpCode.Move && operandIndex == 1
                && instruction.Destination is LocalVariable destination)
                destination.Type = match.Nested.Value.Field.FieldType;
            changed = true;
        }
        return changed;
    }

    // A Move that stores into a whole struct-typed local but records less than the
    // struct's width is an interior store: the operand lands in one of the local's
    // fields, not in the value itself. (`new T(field)` lowers to exactly those
    // stores - `ctx.buffer = span` arrives as a pointer-width store into a 100+
    // byte ref-struct slot.) Rewriting the destination to the covered field lets
    // the store emit as a real field store instead of dropping the operand across
    // the value/reference boundary. Three faithful shapes:
    //   - the source's own type names a unique instance field of the struct
    //     (`span -> ctx.buffer`),
    //   - a leading span field fed an `array + data offset` pointer: `&arr[0]`
    //     lowers to the span-of-array constructor, so the honest operand is the
    //     array itself rather than the pointer-carrying local,
    //   - a literal zero covering the leading field (`f = default`/`f = null`).
    // Every other pairing keeps the diagnosed default. The rewrite only runs where
    // the field is writable from the method (no initonly store outside the
    // declaring .ctor, no private store outside the declaring type) and the
    // recorded access width stays inside the field.
    private static bool RewriteAggregateFieldStores(MethodAnalysisContext method)
    {
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var changed = false;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move
                || instruction.Operands is not [LocalVariable destination, var source])
                continue;
            if (!(destination.Type is { IsValueType: true } destinationType)
                || destinationType is ByRefTypeAnalysisContext or PointerTypeAnalysisContext
                    or GenericParameterTypeAnalysisContext)
                continue;
            var destinationSize = TypeSizes.MinimumUnboxedSize(destinationType, pointerSize);
            if (destinationSize <= pointerSize)
                continue;
            var accessSize = instruction.NativeMemoryAccessSize ?? StoredOperandSize(source, pointerSize);
            if (accessSize <= 0 || accessSize >= destinationSize)
                continue;
            var fields = (destinationType is GenericInstanceTypeAnalysisContext genericDestination
                    ? genericDestination.GenericType.Fields.Select(field =>
                        (FieldAnalysisContext)field.MakeConcreteGenericField(genericDestination.GenericArguments))
                    : (IEnumerable<FieldAnalysisContext>)destinationType.Fields)
                .Where(field => !field.IsStatic && field.Offset >= 0
                    && field.Offset + TypeSizes.MinimumUnboxedSize(field.FieldType, pointerSize)
                        <= destinationSize
                    && AggregateFieldWritableFrom(field, method))
                .ToList();

            // The operand's own type can name the covered field outright
            // (`span -> ctx.buffer`) when exactly one field declares it.
            var sourceType = IlGenerator.EmittedOperandType(source, method);
            var typeMatches = sourceType is not { IsValueType: true }
                    || IlGenerator.IntegralStackWidth(sourceType) != 0
                ? []
                : fields.Where(field => field.FieldType.FullName == sourceType.FullName
                        && TypeSizes.MinimumUnboxedSize(field.FieldType, pointerSize) >= accessSize)
                    .ToList();
            if (typeMatches is [var matched])
            {
                instruction.SetOperand(0,
                    new FieldReference(matched, destination, matched.Offset, [], accessSize));
                changed = true;
                continue;
            }

            var leading = fields.FirstOrDefault(field => field.Offset == 0
                && TypeSizes.MinimumUnboxedSize(field.FieldType, pointerSize) >= accessSize);
            if (leading == null)
                continue;
            if (source is Immediate { Value: 0 }
                && !FieldTypeMayCarryPointer(leading.FieldType))
            {
                instruction.SetOperand(0, new FieldReference(leading, destination, 0, [], accessSize));
                changed = true;
                continue;
            }
            if (SpanFieldElementType(leading) is { } spanElement
                && TryUnwrapArrayDataPointer(source, method, pointerSize, out var arrayOperand)
                && IlGenerator.EmittedOperandType(arrayOperand!, method) is SzArrayTypeAnalysisContext
                    { ElementType: { } arrayElement }
                && arrayElement.FullName == spanElement.FullName)
            {
                instruction.SetOperand(0, new FieldReference(leading, destination, 0, [], accessSize));
                instruction.SetOperand(1, arrayOperand!);
                changed = true;
            }
        }
        return changed;
    }

    // `arr + K` on an array local is `&arr[0]` - K is the array data offset and
    // Il2CppArray's header is four pointer words. For a span-typed consumer the
    // honest operand is the array itself: `new Span(arr)` writes the same data
    // pointer plus the array's own length. A phi'd store source resolves only
    // when every branch unwraps to the same operand - the store carries one
    // operand, so genuinely different arrays per branch keep the diagnostic.
    internal static bool TryUnwrapArrayDataPointer(IOperand operand, MethodAnalysisContext method,
        int pointerSize, out IOperand? arrayOperand)
    {
        arrayOperand = null;
        return operand switch
        {
            LocalVariable local => TryUnwrapArrayDataPointer(local, method, pointerSize, [],
                out arrayOperand),
            // An Add embedded as the operand carries the same `arr + K` shape
            // without a local to trace; a local base still traces its defs.
            Instruction { OpCode: OpCode.Add, Operands: [_, LocalVariable addBaseLocal, Immediate { Value: var addOffset1 }] }
                when addOffset1 == pointerSize * 4
                => TryUnwrapArrayDataPointer(addBaseLocal, method, pointerSize, [], out arrayOperand),
            Instruction { OpCode: OpCode.Add, Operands: [_, var addBase, Immediate { Value: var addOffset }] }
                when addOffset == pointerSize * 4
                    && IlGenerator.EmittedOperandType(addBase, method) is SzArrayTypeAnalysisContext
                => (arrayOperand = addBase) != null,
            _ => false,
        };
    }

    private static bool TryUnwrapArrayDataPointer(LocalVariable local, MethodAnalysisContext method,
        int pointerSize, HashSet<LocalVariable> visited, out IOperand? arrayOperand)
    {
        arrayOperand = null;
        if (!visited.Add(local))
            return false;
        var definitions = method.ControlFlowGraph!.Instructions
            .Where(instruction => instruction.IsAssignment
                && instruction.Operands.Count >= 2
                && ReferenceEquals(instruction.Operands[0], local))
            .ToList();
        var add = definitions.FirstOrDefault(definition => definition.OpCode == OpCode.Add
            && definition.Operands is [_, _, Immediate { Value: var offset }]
            && offset == pointerSize * 4);
        if (add != null)
        {
            // `arr + K` where the base already emits an array needs no tracing -
            // but only for a non-local base (a field load, an embedded value): a
            // local's declared type can read array while the local currently
            // holds a coerced pointer, so locals keep tracing their own defs.
            if (add.Operands[1] is { } addBase && addBase is not LocalVariable
                && IlGenerator.EmittedOperandType(addBase, method) is SzArrayTypeAnalysisContext)
            {
                arrayOperand = addBase;
                return true;
            }
            if (add.Operands[1] is LocalVariable addBaseLocal && !ReferenceEquals(addBaseLocal, local))
                return TryUnwrapArrayDataPointer(addBaseLocal, method, pointerSize, visited,
                    out arrayOperand);
            definitions.Remove(add);
        }
        if (definitions is [{ OpCode: OpCode.Move, Operands: [_, var moveSource, ..] }])
        {
            if (IlGenerator.EmittedOperandType(moveSource, method) is SzArrayTypeAnalysisContext)
            {
                arrayOperand = moveSource;
                return true;
            }
            return moveSource is LocalVariable moveLocal
                && TryUnwrapArrayDataPointer(moveLocal, method, pointerSize, visited,
                    out arrayOperand);
        }
        // `unbox Int32(arr)` is the unsafe load of the array's first pointer word;
        // a following `+32` makes it the data pointer. The operand only unwraps
        // when what was unboxed is provably an array - an `object` local could
        // hold anything and keeps the diagnostic.
        if (definitions is [{ OpCode: OpCode.Unbox, Operands: [_, TypeAnalysisContext unboxedType, var boxedOperand, ..] }]
            && IlGenerator.IntegralStackWidth(unboxedType) > 0
            && IlGenerator.EmittedOperandType(boxedOperand, method) is SzArrayTypeAnalysisContext)
        {
            arrayOperand = boxedOperand;
            return true;
        }
        if (definitions is [{ OpCode: OpCode.Phi } phi] && phi.Operands.Count >= 3)
        {
            foreach (var phiSource in phi.Operands.Skip(1))
            {
                // Every branch gets the visited set the phi saw, so a source
                // reaching back through this phi is a cycle and fails the unwrap,
                // while independent branch chains never block each other.
                if (phiSource is not LocalVariable phiLocal
                    || !TryUnwrapArrayDataPointer(phiLocal, method, pointerSize,
                        new HashSet<LocalVariable>(visited), out var sourceOperand)
                    || sourceOperand == null)
                    return false;
                if (arrayOperand == null)
                    arrayOperand = sourceOperand;
                else if (!SameOperand(arrayOperand, sourceOperand))
                    return false;
            }
            return arrayOperand != null;
        }
        return false;
    }

    // `new Span<T>(arr)`/`new ReadOnlySpan<T>(arr)` lowers to
    // `arr == null ? default : new Span(arr)`, whose arms arrive as
    // `spanLocal := arr + dataOffset` on the non-null edge and a literal
    // `spanLocal := 0` on the null edge. Left as-is, the add's result emits as
    // an uncoercible native-int store into the span local and the zero store
    // is dropped as a default - two diagnosed losses for one managed value.
    // When the local's non-null defs unwrap to an array operand and the zero
    // store provably sits on that array's `== null` edge, both stores rewrite
    // to `Move spanLocal := arr`, which emits `new Span(arr)`: on the null arm
    // that evaluates to default - exactly the zero the binary wrote.
    private static void RecoverArrayBackedSpanStores(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var pointerSize = method.AppContext.Binary.PointerSizeBytes;
        var instructions = graph.Instructions.ToList();
        foreach (var instruction in instructions)
        {
            if (instruction.Destination is not LocalVariable destination
                || destination.Type is not GenericInstanceTypeAnalysisContext
                    { GenericType.FullName: "System.Span`1" or "System.ReadOnlySpan`1" } spanDestination)
                continue;

            if (instruction.OpCode == OpCode.Add
                && instruction.Operands is [_, _, Immediate { Value: var offset }]
                && offset == pointerSize * 4
                && TryUnwrapArrayDataPointer(instruction, method, pointerSize, out var addArray)
                && SpanElementMatches(addArray!, spanDestination, method))
            {
                instruction.OpCode = OpCode.Move;
                instruction.SetOperands(destination, addArray!);
                continue;
            }

            if (instruction.OpCode != OpCode.Move
                || instruction.Operands is not [_, Immediate { Value: 0 }])
                continue;
            var siteBlock = graph.Blocks.FirstOrDefault(block => block.Instructions.Contains(instruction));
            if (siteBlock == null)
                continue;
            foreach (var sibling in instructions.Where(definition =>
                !ReferenceEquals(definition, instruction)
                && ReferenceEquals(definition.Destination, destination)))
            {
                var candidate = sibling switch
                {
                    { OpCode: OpCode.Add } => UnwrapArrayOperand(sibling, method, pointerSize),
                    { OpCode: OpCode.Move, Operands: [_, var moveSource] }
                        => UnwrapArrayOperand(moveSource, method, pointerSize),
                    _ => null,
                };
                if (candidate == null
                    || !SpanElementMatches(candidate, spanDestination, method)
                    || !OnNullEdge(instruction, siteBlock, candidate, method))
                    continue;
                instruction.SetOperand(1, candidate);
                break;
            }
        }
    }

    private static IOperand? UnwrapArrayOperand(IOperand operand, MethodAnalysisContext method, int pointerSize) =>
        TryUnwrapArrayDataPointer(operand, method, pointerSize, out var arrayOperand) ? arrayOperand
        : IlGenerator.EmittedOperandType(operand, method) is SzArrayTypeAnalysisContext ? operand
        : null;

    private static bool SpanElementMatches(IOperand arrayOperand,
        GenericInstanceTypeAnalysisContext spanDestination, MethodAnalysisContext method) =>
        IlGenerator.EmittedOperandType(arrayOperand, method) is SzArrayTypeAnalysisContext
            { ElementType: { } element }
        && element.FullName == spanDestination.GenericArguments[0].FullName;

    // The store must execute only on the `array == null` edge of a guard that
    // compares the unwrapped array operand against zero: every predecessor
    // whose incoming edge actually reaches the site is either such a guard or
    // a block the site block itself dominates (a back-edge into the null arm),
    // and nothing in the block may redefine the array between the edge and
    // the store. An edge bypasses the site when its landing instruction sits
    // after it in the block - a phi-edge copy at the head of a join block is
    // reached only by the edge that targets it.
    private static bool OnNullEdge(Instruction site, Block siteBlock, IOperand arrayOperand,
        MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph!;
        var siteIndex = siteBlock.Instructions.IndexOf(site);
        var sawGuard = false;
        foreach (var predecessor in siteBlock.Predecessors)
        {
            if (ReferenceEquals(predecessor, siteBlock)
                || method.DominatorInfo?.Dominates(siteBlock, predecessor) == true)
                continue;
            if (!EdgeReachesSite(predecessor, siteBlock, siteIndex, graph))
                continue;
            if (IsNullEdgeGuard(predecessor, siteBlock, siteIndex, arrayOperand, graph))
            {
                sawGuard = true;
                continue;
            }
            return false;
        }
        if (!sawGuard)
            return false;
        foreach (var earlier in siteBlock.Instructions.TakeWhile(i => !ReferenceEquals(i, site)))
        {
            switch (arrayOperand)
            {
                case LocalVariable arrayLocal when ReferenceEquals(earlier.Destination, arrayLocal):
                // A store through memory or into a field may alias the array
                // field, so the null proof does not survive it.
                case FieldReference when earlier.Destination is MemoryOperand or FieldReference:
                    return false;
            }
        }
        return true;
    }

    // Does control entering `siteBlock` from `predecessor` reach `siteIndex`?
    // Edges land on their target instruction (or the block head when the edge
    // is a fallthrough or names a block); landing after the site bypasses it.
    private static bool EdgeReachesSite(Block predecessor, Block siteBlock, int siteIndex,
        ISILControlFlowGraph graph)
    {
        var terminator = predecessor.Instructions.LastOrDefault();
        if (terminator is not { OpCode: OpCode.Jump or OpCode.ConditionalJump })
            return true; // Fallthrough into the block head.
        var taken = terminator.Operands[0];
        var takenBlock = LandingBlock(taken, graph);
        var fallthroughReaches = predecessor.Successors.Any(successor =>
            ReferenceEquals(successor, siteBlock) && !ReferenceEquals(successor, takenBlock));
        if (terminator.OpCode == OpCode.Jump)
            return LandingIndex(taken, siteBlock, graph) <= siteIndex;
        return (LandingIndex(taken, siteBlock, graph) <= siteIndex) || fallthroughReaches;
    }

    private static Block? LandingBlock(IOperand target, ISILControlFlowGraph graph) =>
        target switch
        {
            Block blockTarget => blockTarget,
            Instruction targetInstruction
                => graph.Blocks.FirstOrDefault(b => b.Instructions.Contains(targetInstruction)),
            _ => null,
        };

    private static int? LandingIndex(IOperand target, Block siteBlock, ISILControlFlowGraph graph) =>
        target switch
        {
            Block blockTarget => ReferenceEquals(blockTarget, siteBlock) ? 0 : null,
            Instruction targetInstruction
                => siteBlock.Instructions.IndexOf(targetInstruction) is { } index && index >= 0
                    ? index
                    : null,
            _ => null,
        };

    private static bool IsNullEdgeGuard(Block guard, Block siteBlock, int siteIndex,
        IOperand arrayOperand, ISILControlFlowGraph graph)
    {
        if (guard.Instructions.Count == 0
            || guard.Instructions[^1] is not { OpCode: OpCode.ConditionalJump } jump
            || jump.Operands.Count < 2
            || jump.Operands[1] is not LocalVariable condition
            || ResolveNullCheck(condition, graph) is not { } check
            || !SameOperand(ResolveAliasOperand(check.Compared, graph), arrayOperand))
            return false;
        var taken = jump.Operands[0];
        var landing = LandingIndex(taken, siteBlock, graph);
        var takenBlock = LandingBlock(taken, graph);
        var fallthroughFeeds = guard.Successors.Any(successor =>
            ReferenceEquals(successor, siteBlock) && !ReferenceEquals(successor, takenBlock));
        // The null side is the taken edge for CheckEqual and the fallthrough
        // for CheckNotEqual; the other edge of the same guard must not also
        // feed the site.
        if (check.NotEqual)
            return fallthroughFeeds && (landing == null || landing > siteIndex);
        return landing is { } reached && reached <= siteIndex && !fallthroughFeeds;
    }

    // The operand a comparison actually reads: a guard like `CheckEqual(v, 0)`
    // often compares a `Move` copy of the value the span was built from, so
    // single-definition Move chains resolve through to the ultimate operand.
    // Locals on the chain must stay immutable - with more than one definition
    // the comparison would prove nothing about the operand at the store.
    private static IOperand ResolveAliasOperand(IOperand operand, ISILControlFlowGraph graph)
    {
        var visited = new HashSet<LocalVariable>();
        while (operand is LocalVariable local && visited.Add(local)
            && graph.Instructions.Where(i => i.IsAssignment && ReferenceEquals(i.Destination, local))
                    .ToList() is [{ OpCode: OpCode.Move, Operands: [_, var moveSource] }])
            operand = moveSource;
        return operand;
    }

    // The condition feeding the null check, resolved through single-definition
    // Move/Not chains: NotEqual is true when the null side is the
    // condition-false edge (CheckNotEqual, or a negated CheckEqual).
    private static (IOperand Compared, bool NotEqual)? ResolveNullCheck(LocalVariable condition,
        ISILControlFlowGraph graph)
    {
        var visited = new HashSet<LocalVariable>();
        var negated = false;
        var current = condition;
        while (visited.Add(current))
        {
            if (graph.Instructions.Where(i => i.IsAssignment && ReferenceEquals(i.Destination, current))
                    .ToList() is not [var definition])
                return null;
            switch (definition)
            {
                case { OpCode: OpCode.Move, Operands: [_, LocalVariable moveSource] }:
                    current = moveSource;
                    continue;
                case { OpCode: OpCode.Not, Operands: [_, LocalVariable notSource] }:
                    negated = !negated;
                    current = notSource;
                    continue;
                case { OpCode: OpCode.CheckEqual or OpCode.CheckNotEqual,
                        Operands: [_, var left, var right] }:
                    var compared = left is Immediate { Value: 0 } ? right
                        : right is Immediate { Value: 0 } ? left
                        : null;
                    return compared == null
                        ? null
                        : (compared, (definition.OpCode == OpCode.CheckNotEqual) != negated);
                default:
                    return null;
            }
        }
        return null;
    }

    private static bool SameOperand(IOperand left, IOperand right) =>
        (left, right) switch
        {
            (LocalVariable leftLocal, LocalVariable rightLocal) =>
                ReferenceEquals(leftLocal, rightLocal),
            (FieldReference leftField, FieldReference rightField) =>
                leftField.Field.Name == rightField.Field.Name
                    && leftField.Offset == rightField.Offset
                    && ReferenceEquals(leftField.Local, rightField.Local),
            _ => ReferenceEquals(left, right)
        };

    private static TypeAnalysisContext? SpanFieldElementType(FieldAnalysisContext field) =>
        field.FieldType is GenericInstanceTypeAnalysisContext
            { GenericType.FullName: "System.Span`1" or "System.ReadOnlySpan`1" } span
        && span.GenericArguments is [var element]
            ? element
            : null;

    // A zero covering a pointer-carrying field is ambiguous: lifted
    // data-pointer stores also collapse to `Move := 0` when the pointer `add`
    // emits as a dead sibling expression, so `field = default` would silently
    // mask a lost array. Only fields that cannot carry a pointer take the
    // `default` rewrite; the rest keep the whole-struct destination and its
    // named diagnostic.
    private static bool FieldTypeMayCarryPointer(TypeAnalysisContext type) =>
        type is PointerTypeAnalysisContext or ByRefTypeAnalysisContext
        || type.FullName is "System.IntPtr" or "System.UIntPtr"
        || type is GenericInstanceTypeAnalysisContext
            { GenericType.FullName: "System.Span`1" or "System.ReadOnlySpan`1" or "System.ByReference`1" }
        || IlGenerator.IsByRefLike(type);

    // stfld can only write what the method may legally touch: no initonly store
    // outside the declaring type's own .ctor, and no private/family store outside
    // the declaring type. Anything else keeps the whole-struct destination and
    // its diagnostic rather than emitting a store the verifier rejects.
    private static bool AggregateFieldWritableFrom(FieldAnalysisContext field, MethodAnalysisContext method)
    {
        var attributes = field.Attributes;
        if ((attributes & FieldAttributes.InitOnly) != 0
            && !(method.Name is ".ctor"
                && field.DeclaringType?.FullName == method.DeclaringType?.FullName))
            return false;
        return (attributes & FieldAttributes.FieldAccessMask) switch
        {
            FieldAttributes.Private or FieldAttributes.PrivateScope or FieldAttributes.Family
                => field.DeclaringType?.FullName == method.DeclaringType?.FullName,
            FieldAttributes.Assembly or FieldAttributes.FamANDAssem
                => field.DeclaringType?.DeclaringAssembly?.Name
                    == method.DeclaringType?.DeclaringAssembly?.Name,
            _ => true,
        };
    }

    private static int StoredOperandSize(IOperand operand, int pointerSize) => operand switch
    {
        LocalVariable { Type: { } type }
            => (int)System.Math.Min(TypeSizes.MinimumUnboxedSize(type, pointerSize), int.MaxValue),
        FieldReference field
            => (int)System.Math.Min(TypeSizes.MinimumUnboxedSize(field.Field.FieldType, pointerSize),
                int.MaxValue),
        _ => pointerSize,
    };

    // A FieldReference materialized while its owner local still typed the erased shared
    // instantiation (e.g. `Dictionary<K,V>.Enumerator<object,object>` under generic
    // sharing) keeps that instantiation even though the local emits as the sharpened
    // one (EmittedLocalType). The emitted member then disagrees with the declared
    // slots: `Enumerator<string,...>::get_Current` returns `KeyValuePair<string,...>`
    // into a `KeyValuePair<object,object>` local. When the local's emitted type is a
    // different instantiation of the same generic definition, re-resolve the field
    // path on the instantiation the local actually emits as so PropagateMove retypes
    // the destination to match.
    private static bool ResolveSharpenedFieldOwners(MethodAnalysisContext method)
    {
        var changed = false;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        for (var i = 0; i < instruction.Operands.Count; i++)
        {
            var (reference, addressed) = instruction.Operands[i] switch
            {
                FieldReference direct => (direct, false),
                AddressOf { Target: FieldReference addressedField } => (addressedField, true),
                _ => (null, false),
            };
            if (reference is not { Field: ConcreteGenericFieldAnalysisContext
                    { DeclaringType: GenericInstanceTypeAnalysisContext owner } }
                // Only the one-way erased -> concrete transition is safe to take:
                // without it a sharpening that later revises would flip the owner
                // back and forth and the fixpoint would never settle.
                || !owner.GenericArguments.Any(IlGenerator.ContainsErasedSharedArgument))
                continue;
            if (IlGenerator.EmittedLocalType(reference.Local, method) is not
                    GenericInstanceTypeAnalysisContext emitted
                || emitted.GenericType.FullName != owner.GenericType.FullName
                || emitted.FullName == owner.FullName
                || emitted.GenericArguments.Any(IlGenerator.ContainsErasedSharedArgument))
                continue;
            if (MetadataResolver.FindInstanceFieldPathAtOffset(emitted, reference.Offset,
                    reference.AccessSize) is not { } resolved
                || MetadataResolver.MemberPathUnspellable(resolved, method,
                    instruction.OpCode == OpCode.Move && i == 0, addressed))
                continue;
            var field = resolved.Field;
            if (field is not ConcreteGenericFieldAnalysisContext)
                field = MetadataResolver.BindResolvedFieldLeaf(emitted, resolved.Containers, field);
            var replacement = new FieldReference(field, reference.Local, reference.Offset,
                resolved.Containers, reference.AccessSize);
            instruction.SetOperand(i, addressed ? new AddressOf(replacement) : replacement);
            changed = true;
        }
        return changed;
    }

    internal static void ResolveHiddenReturnBuffers(MethodAnalysisContext method)
    {
        var instructions = method.ControlFlowGraph!.Instructions;
        var addressed = method.ControlFlowGraph!.Instructions
            .Where(instruction => instruction is { OpCode: OpCode.Move,
                Operands: [LocalVariable, AddressOf { Target: LocalVariable }] })
            .ToDictionary(instruction => (LocalVariable)instruction.Operands[0],
                instruction => (LocalVariable)((AddressOf)instruction.Operands[1]).Target);

        var definedAt = DefinitionPositions(instructions);
        var hiddenReturns = new List<(Instruction Call, LocalVariable Buffer,
            MethodAnalysisContext Target, TypeAnalysisContext ResultType, int Index)>();
        foreach (var call in instructions)
        {
            if (call is not { OpCode: OpCode.Call,
                    Operands: [MethodAnalysisContext target, MemoryOperand { Index: null, Addend: 0, Scale: 0,
                        Base: LocalVariable pointer }, ..] }
                || !addressed.TryGetValue(pointer, out var buffer))
                continue;

            var concreteTarget = !target.IsStatic && call.Operands.Count > 2
                ? IlGenerator.RetargetToReceiverInstantiation(target,
                    IlGenerator.SharedGenericEvidenceType(call.Operands[2], method))
                : target;
            var resultType = IlGenerator.EffectiveCallReturnType(concreteTarget);
            hiddenReturns.Add((call, buffer, concreteTarget, resultType, instructions.IndexOf(call)));
        }

        foreach (var hiddenReturn in hiddenReturns)
        {
            var (call, buffer, _, resultType, callIndex) = hiddenReturn;
            var endIndex = hiddenReturns
                .Where(candidate => candidate.Index > callIndex
                    && (ReferenceEquals(candidate.Buffer, buffer)
                        || TryStackOffset(candidate.Buffer.Register.Name) is { } candidateOffset
                        && TryStackOffset(buffer.Register.Name) == candidateOffset))
                .Select(candidate => candidate.Index)
                .DefaultIfEmpty(instructions.Count)
                .Min();
            // The same native stack slot is routinely reused for several different
            // generic struct returns. A CLR local has one fixed type, so model each
            // hidden return as its own local and reconnect only its own lifetime.
            LocalVariable? result = null;
            var aliases = new HashSet<LocalVariable> { buffer };
            foreach (var next in instructions.Skip(callIndex + 1).Take(endIndex - callIndex - 1))
                if (next is { OpCode: OpCode.Move,
                        Operands: [LocalVariable destination, LocalVariable source] }
                    && !ReferenceEquals(destination, source) && aliases.Contains(source))
                {
                    aliases.Add(destination);
                    result = destination;
                }
            if (result == null)
            {
                result = new LocalVariable($"{buffer.Name}_hret_{call.Index}",
                    new Register(null, $"HRET_{call.Index}"), resultType);
                method.Locals.Add(result);
            }
            result.Type = resultType;
            result.HiddenReturnBuffer = buffer;
            call.Destination = result;

            for (var i = callIndex + 1; i < endIndex; i++)
            {
                var next = instructions[i];
                var destination = next.Destination;
                for (var operandIndex = 0; operandIndex < next.Operands.Count; operandIndex++)
                {
                    var operand = next.Operands[operandIndex];
                    if (ReferenceEquals(operand, destination))
                        continue;
                    if (RewriteHiddenReturnStackOperand(operand, buffer, result, resultType,
                            next.NativeMemoryAccessSize ?? 0, local => StoredBetween(definedAt, local, callIndex, i)) is { } rewritten)
                        next.SetOperand(operandIndex, rewritten);
                }
            }
        }
    }

    private static bool SharpenHiddenReturnBuffers(MethodAnalysisContext method)
    {
        var changed = false;
        var instructions = method.ControlFlowGraph!.Instructions;
        var definedAt = DefinitionPositions(instructions);
        foreach (var call in method.ControlFlowGraph!.Instructions)
        {
            if (call is not { OpCode: OpCode.Call,
                    Operands: [MethodAnalysisContext target, LocalVariable result, var receiver, ..] }
                || target.IsStatic
                || result.HiddenReturnBuffer == null)
                continue;

            var concreteTarget = IlGenerator.RetargetToReceiverInstantiation(target,
                IlGenerator.SharedGenericEvidenceType(receiver, method));
            var resultType = IlGenerator.EffectiveCallReturnType(concreteTarget);
            if (result.Type?.FullName == resultType.FullName)
                continue;

            result.Type = resultType;
            call.SetOperand(0, concreteTarget);
            var callIndex = instructions.IndexOf(call);
            for (var index = 0; index < instructions.Count; index++)
            for (var operandIndex = 0; operandIndex < instructions[index].Operands.Count; operandIndex++)
            {
                var instruction = instructions[index];
                var operand = instruction.Operands[operandIndex];
                var field = operand switch
                {
                    FieldReference direct when ReferenceEquals(direct.Local, result) => direct,
                    AddressOf { Target: FieldReference addressed } when ReferenceEquals(addressed.Local, result)
                        => addressed,
                    _ => null,
                };
                // An address of the slot taken before the call is not the call's result: an early
                // `return new T[0, 0]` takes the address of its lengths stored in the same slot.
                IOperand? replacement = field == null
                    ? result.HiddenReturnBuffer == null || operandIndex == 0 && instruction.IsAssignment
                      || operand is AddressOf && index <= callIndex
                        ? null
                        : RewriteHiddenReturnStackOperand(operand, result.HiddenReturnBuffer, result,
                            resultType, instruction.NativeMemoryAccessSize ?? 0,
                            local => StoredBetween(definedAt, local, callIndex, index))
                    : HiddenReturnField(resultType, result, field.Offset, field.AccessSize);
                if (replacement == null)
                    continue;
                instruction.SetOperand(operandIndex, field != null && operand is AddressOf
                    ? new AddressOf(replacement)
                    : replacement);
                if (instruction.OpCode == OpCode.Move && operandIndex == 1
                    && instruction.Destination is LocalVariable destination
                    && replacement is FieldReference replacementField)
                    destination.Type = replacementField.Field.FieldType;
            }

            foreach (var instruction in method.ControlFlowGraph.Instructions)
                if (instruction is { OpCode: OpCode.Move,
                        Operands: [LocalVariable klass,
                            MemoryOperand { Index: null, Scale: 0, Addend: 0,
                                Base: LocalVariable { Type: { IsValueType: false } instance } }] }
                    && klass.Type is RuntimeClassTypeAnalysisContext { RepresentedType: var represented }
                    && represented.FullName != instance.FullName)
                    klass.Type = new RuntimeClassTypeAnalysisContext(instance, instance.DeclaringAssembly);
            changed = true;
        }
        return changed;
    }

    private static IOperand? RewriteHiddenReturnStackOperand(IOperand operand, LocalVariable buffer,
        LocalVariable result, TypeAnalysisContext returnType, int accessSize, System.Func<LocalVariable, bool> overwritten)
    {
        // An address of the cell is the result's address under the same rule as a read: once the
        // slot is stored again (a later `new T[w, h]` writing its lengths there), it is that store's.
        if (operand is AddressOf address
            && HiddenReturnStackStorage(address.Target, buffer, result, returnType, accessSize, overwritten) is { } addressed)
            return new AddressOf(addressed);

        return HiddenReturnStackStorage(operand, buffer, result, returnType, accessSize, overwritten);
    }

    // Where each local is defined in the instruction list; a local defined twice is absent.
    private static Dictionary<LocalVariable, int> DefinitionPositions(List<Instruction> instructions)
    {
        var positions = new Dictionary<LocalVariable, int>();
        var twice = new HashSet<LocalVariable>();
        for (var i = 0; i < instructions.Count; i++)
            if (instructions[i].IsAssignment && instructions[i].Operands is [LocalVariable defined, ..] && !positions.TryAdd(defined, i))
                twice.Add(defined);
        foreach (var local in twice)
            positions.Remove(local);
        return positions;
    }

    // A cell stored between the call and the read no longer holds the bytes the call returned
    // into it: the frame slot was reused (`stp xzr, x9, [sp, #0x38]` after the enumerator moved
    // out). A store before the call (the buffer's zeroing) is overwritten by the call, and one
    // after the read has not happened yet.
    private static bool StoredBetween(Dictionary<LocalVariable, int> definedAt, LocalVariable local, int callIndex, int readIndex)
        => definedAt.TryGetValue(local, out var at) && at > callIndex && at < readIndex;

    // A read of a buffer cell is the returned struct's field only while the cell still holds the
    // returned bytes.
    private static IOperand? HiddenReturnStackStorage(IOperand operand, LocalVariable buffer,
        LocalVariable result, TypeAnalysisContext returnType, int accessSize, System.Func<LocalVariable, bool>? overwritten)
    {
        if (operand is not LocalVariable local
            || overwritten != null && overwritten(local)
            || TryStackOffset(buffer.Register.Name) is not { } bufferOffset
            || TryStackOffset(local.Register.Name) is not { } localOffset)
            return null;

        var relativeOffset = localOffset - bufferOffset;
        if (relativeOffset == 0)
            return result;
        if (relativeOffset < 0)
            return null;

        return HiddenReturnField(returnType, result, relativeOffset, accessSize);
    }

    private static FieldReference? HiddenReturnField(TypeAnalysisContext returnType,
        LocalVariable result, int relativeOffset, int accessSize = 0)
    {
        FieldAnalysisContext? field;
        long fieldOffset;
        long fieldSize;
        if (returnType is GenericInstanceTypeAnalysisContext generic)
        {
            var containing = GenericInstanceFieldLayout.FindFieldContainingOffset(generic, relativeOffset);
            field = containing?.Field;
            fieldOffset = containing?.Offset ?? 0;
            fieldSize = containing?.Size ?? 0;
        }
        else
        {
            field = returnType.Fields.FirstOrDefault(candidate => !candidate.IsStatic
                && (candidate.BackingData?.FieldOffset ?? candidate.Offset) == relativeOffset);
            fieldOffset = field == null ? 0 : field.BackingData?.FieldOffset ?? field.Offset;
            fieldSize = field == null ? 0 : TypeSizes.MinimumUnboxedSize(field.FieldType,
                returnType.AppContext.Binary.PointerSizeBytes);
        }

        if (field == null)
            return null;

        if (accessSize > 0 && field.FieldType.IsValueType && fieldSize > accessSize)
        {
            var nestedOffset = relativeOffset - fieldOffset;
            var nested = field.FieldType is GenericInstanceTypeAnalysisContext nestedGeneric
                ? GenericInstanceFieldLayout.FindFieldContainingOffset(nestedGeneric, nestedOffset) is
                    { Offset: var offset, Size: var size, Field: var concrete }
                    && offset == nestedOffset && size == accessSize ? concrete : null
                : field.FieldType.Fields.FirstOrDefault(candidate => !candidate.IsStatic
                    && (candidate.BackingData?.FieldOffset ?? candidate.Offset) == nestedOffset
                    && TypeSizes.MinimumUnboxedSize(candidate.FieldType,
                        returnType.AppContext.Binary.PointerSizeBytes) == accessSize);
            if (nested != null)
                return new FieldReference(nested, result, relativeOffset, [field], accessSize);
        }

        return new FieldReference(field, result, relativeOffset, accessSize: accessSize);
    }

    internal static int? TryStackOffset(string registerName)
    {
        const string Prefix = "stack_";
        if (!registerName.StartsWith(Prefix, System.StringComparison.Ordinal))
            return null;
        var offset = registerName[Prefix.Length..];
        var negative = offset.StartsWith("-", System.StringComparison.Ordinal);
        if (negative)
            offset = offset[1..];
        return System.Int32.TryParse(offset, System.Globalization.NumberStyles.HexNumber,
            System.Globalization.CultureInfo.InvariantCulture, out var value)
            ? negative ? -value : value
            : null;
    }

    /// <summary>
    /// The storage one register name provably covers: a B/H/S/W/D/X/V/Q
    /// register-shaped name (`letter + digits`) covers its named width — a
    /// whole Vector3 or Quaternion lives inside one V register's 16 bytes —
    /// while a stack-slot, frame or virtual register name only covers a
    /// pointer-sized cell.
    /// </summary>
    internal static int RegisterCoverageBytes(string registerName, int pointerSize)
    {
        if (registerName.Length > 1 && char.IsAsciiDigit(registerName[1]))
            return registerName[0] switch
            {
                'B' or 'b' => 1,
                'H' or 'h' => 2,
                'S' or 's' or 'W' or 'w' => 4,
                'D' or 'd' or 'X' or 'x' => 8,
                'V' or 'v' or 'Q' or 'q' => 16,
                _ => pointerSize
            };
        return pointerSize;
    }

    // A type-metadata global load (Move local, typeof(T)) puts the runtime class pointer for T into
    // the local - an Il2CppClass*, not an instance of T. That is known exactly from the instruction,
    // so it is seeded as ground truth (overriding any prior guess) before the inference fixpoint,
    // rather than letting a monotonic pass first mistype the local as T itself.
    private static void SeedRuntimeClassTypes(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move || instruction.Operands.Count < 2)
                continue;

            if (instruction.Operands[0] is LocalVariable destination
                && instruction.Operands[1] is TypeAnalysisContext type and not (RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext))
                destination.Type = new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly);
        }
    }

    internal static void SeedIl2CppDefaultsClassTypes(MethodAnalysisContext method)
    {
        if (!method.AppContext.UnityVersion.GreaterThanOrEquals(6000))
            return;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction is not { OpCode: OpCode.Move,
                    Operands: [LocalVariable destination,
                        MemoryOperand { Base: LocalVariable defaults, Index: null, Scale: 0, Addend: var offset }] }
                || !KeyFunctionRecovery.HasAbsoluteDefinition(method.ControlFlowGraph, defaults)
                || KeyFunctionRecovery.Unity6PrimitiveDefaultsClass(method.AppContext.SystemTypes, offset) is not { } type)
                continue;
            destination.Type = new RuntimeClassTypeAnalysisContext(type, type.DeclaringAssembly);
        }
    }

    private static void SeedNewobjResults(MethodAnalysisContext method)
    {
        var definitions = method.ControlFlowGraph!.Instructions
            .Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!)
            .Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Newobj || instruction.Operands.Count < 2)
                continue;

            if (instruction.Operands[0] is LocalVariable destination
                && InstantiatedType(instruction.Operands[1], definitions) is { } type)
                destination.Type = type;
        }
    }

    private static TypeAnalysisContext? InstantiatedType(IOperand classOperand,
        IReadOnlyDictionary<LocalVariable, Instruction> definitions) =>
        InstantiatedType(classOperand, definitions, []);

    // The class operand is often a copy of the ldtoken'ed klass (Move local, source). Untyped copy
    // locals are only typed later inside the fixpoint, so follow single-definition Move chains here
    // to still identify the allocated type through the copy.
    private static TypeAnalysisContext? InstantiatedType(IOperand classOperand,
        IReadOnlyDictionary<LocalVariable, Instruction> definitions, HashSet<LocalVariable> visiting) =>
        classOperand switch
        {
            LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: var t } } => t,
            RuntimeClassTypeAnalysisContext { RepresentedType: var t } => t,
            LocalVariable { Type: { } t } => t,
            LocalVariable local when visiting.Add(local)
                && definitions.TryGetValue(local, out var definition)
                && definition is { OpCode: OpCode.Move, Operands: [_, { } source] }
                => InstantiatedType(source, definitions, visiting),
            TypeAnalysisContext type => type, //not sure this is actually valid but for completeness
            _ => null,
        };

    // A method/field-metadata global load (Move local, methodof(M) / fieldof(F)) puts a MethodInfo*
    // or FieldInfo* into the local. MetadataResolver already resolved the address to a context naming
    // the member; that same context is the local's type (a runtime handle, recoverable via its
    // RepresentedMethod/RepresentedField).
    private static void SeedMethodInfoTypes(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move || instruction.Operands.Count < 2)
                continue;

            if (instruction.Operands[0] is LocalVariable destination
                && instruction.Operands[1] is RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext)
                destination.Type = (TypeAnalysisContext)instruction.Operands[1];
        }
    }

    // A comparison (CheckEqual, CheckLess, ...) writes a 0/1 result into its destination, so that local
    // is a System.Boolean regardless of what the compared operands are.
    private static void SeedComparisonResults(MethodAnalysisContext method)
    {
        var booleanType = method.AppContext.SystemTypes.SystemBooleanType;

        var allDefinitions = method.ControlFlowGraph!.Instructions
            .Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!)
            .ToDictionary(g => g.Key, g => (IReadOnlyList<Instruction>)g.ToList());

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode is < OpCode.CheckEqual or > OpCode.CheckLessOrEqual)
                continue;

            if (instruction.Destination is LocalVariable destination
                && TryClaimBoolean(destination, method, allDefinitions))
                destination.Type = booleanType;
        }
    }
    
    //Handles typing of locals for ref/out params. Returns whether anything new was typed
    public static bool TypeAddressedLocals(MethodAnalysisContext method, bool allowCanonicalCallTypes = true)
    {
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (!instruction.IsCall || instruction.Operands[0] is not MethodAnalysisContext calledMethod)
                continue;
            var deferGenericSlots = !allowCanonicalCallTypes
                && MetadataResolver.ErasedGenericArgumentCount(calledMethod) > 0;
            var definition = (calledMethod as ConcreteGenericMethodAnalysisContext)?.BaseMethodContext ?? calledMethod;

            var firstArg = instruction.OpCode == OpCode.CallVoid ? 1 : 2;

            // the receiver of a value type's instance method is a pointer to the value
            if (!deferGenericSlots && !calledMethod.IsStatic && firstArg < instruction.Operands.Count
                && instruction.Operands[firstArg] is AddressOf { Target: LocalVariable receiver }
                && calledMethod.DeclaringType is { IsValueType: true } declaringType)
                changed |= SetTypeIfUnknown(receiver, declaringType);

            var paramOffset = firstArg + (calledMethod.IsStatic ? 0 : 1);

            for (var i = paramOffset; i < instruction.Operands.Count; i++)
            {
                var parameterIndex = i - paramOffset;
                if (parameterIndex > calledMethod.Parameters.Count - 1) // Probably MethodInfo*
                    continue;

                if (deferGenericSlots && definition.Parameters[parameterIndex].ParameterType.HasAnyGenericParameters())
                    continue;

                if (instruction.Operands[i] is AddressOf { Target: LocalVariable referenced }
                    && calledMethod.Parameters[parameterIndex].ParameterType is ByRefTypeAnalysisContext { ElementType: { } referencedType })
                    changed |= SetTypeIfUnknown(referenced, referencedType);
            }
        }

        return changed;
    }

    // An address-taken cell whose content may be observed by later reads gets a fresh SSA version
    // for the post-call value (the callee can write through the pointer). That version is never a
    // definition target - the write comes through the pointer, not an assignment. When nothing else
    // resolved such a version's type, it inherits the type of the most recent earlier version of
    // the same storage: a write barrier or an initobj-style helper stores or reinitializes the same
    // slot, it does not change the managed type the slot models. This runs last in the fixpoint so
    // real byref/addressed typing (TypeAddressedLocals, PropagateFromCallParameters) wins.
    private static bool InheritEscapedCellVersions(MethodAnalysisContext method)
    {
        var definedLocals = method.ControlFlowGraph!.Instructions
            .Select(instruction => instruction.Destination)
            .OfType<LocalVariable>()
            .ToHashSet();
        var typedVersions = method.Locals.Where(local => local.Type != null).ToList();

        var changed = false;
        foreach (var local in method.Locals)
        {
            // a defined nowhere, versioned local is a clobbered cell version
            if (local.Type != null || local.Register.Version <= 0 || definedLocals.Contains(local))
                continue;

            var prior = typedVersions
                .Where(candidate => candidate.Register.Name == local.Register.Name
                    && candidate.Register.Version < local.Register.Version)
                .MaxBy(candidate => candidate.Register.Version);
            if (prior == null)
                continue;

            local.Type = prior.Type;
            changed = true;
        }
        return changed;
    }

    // Fills in a local's type only when it is currently unknown, keeping propagation monotonic (a
    // type, once set, is never changed) so the fixpoint terminates. Returns whether it set anything.
    private static bool SetTypeIfUnknown(LocalVariable local, TypeAnalysisContext? type)
    {
        if (type == null || local.Type != null)
            return false;

        local.Type = type;
        return true;
    }

    private static bool PropagateStaticFieldStorage(MethodAnalysisContext method)
    {
        var staticFieldsOffset = method.AppContext.Binary.is32Bit ? StaticFieldsOffset32 : StaticFieldsOffset64;
        var definitions = method.ControlFlowGraph!.Instructions
            .Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!)
            .Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());
        var changed = false;

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (instruction.OpCode != OpCode.Move || instruction.Operands.Count < 2)
                continue;

            if (instruction.Operands[0] is not LocalVariable destination || destination.Type is StaticFieldStorageTypeAnalysisContext)
                continue;

            if (instruction.Operands[1] is not MemoryOperand { Index: null, Scale: 0 } memory
                || memory.Base is not LocalVariable baseLocal)
                continue;

            var addend = memory.Addend;
            if (definitions.TryGetValue(baseLocal, out var definition)
                && definition is { OpCode: OpCode.Add, Operands: [_, LocalVariable root, Immediate displacement] })
            {
                baseLocal = root;
                addend += displacement.Value;
            }

            if (addend != staticFieldsOffset
                || baseLocal.Type is not RuntimeClassTypeAnalysisContext { RepresentedType: var owner })
                continue;

            destination.Type = new StaticFieldStorageTypeAnalysisContext(owner, owner.DeclaringAssembly);
            changed = true;
        }

        return changed;
    }

    // A single propagation sweep over every move and phi. Returns whether it filled in any type.
    private static bool PropagateTypesOnce(MethodAnalysisContext method)
    {
        var changed = false;

        var definitions = method.ControlFlowGraph!.Instructions
            .Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!)
            .Where(g => g.Count() == 1)
            .ToDictionary(g => g.Key, g => g.Single());

        var allDefinitions = method.ControlFlowGraph.Instructions
            .Where(i => i.Destination is LocalVariable)
            .GroupBy(i => (LocalVariable)i.Destination!)
            .ToDictionary(g => g.Key, g => (IReadOnlyList<Instruction>)g.ToList());

        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            switch (instruction.OpCode)
            {
                case OpCode.SignExtend32:
                    if (instruction.Destination is LocalVariable extended)
                        changed |= SetTypeIfUnknown(extended, method.AppContext.SystemTypes.SystemInt64Type);
                    break;
                case OpCode.Convert:
                    // The conversion's result type is its destination register's
                    // width - never the converted operand's type.
                    if (instruction.Destination is LocalVariable converted)
                        changed |= SetTypeIfUnknown(converted, ConversionResultType(instruction, method));
                    break;
                case OpCode.Move:
                    changed |= PropagateMove(instruction, method, method.AppContext.Binary.PointerSizeBytes,
                        method.AppContext.SystemTypes.SystemInt32Type, definitions, allDefinitions);
                    break;
                case OpCode.Phi:
                    changed |= PropagatePhi(instruction, method, definitions, allDefinitions);
                    break;
                case OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.VectorMin or OpCode.VectorMax:
                    changed |= PropagateArithmetic(instruction, method);
                    break;
                case OpCode.Divide or OpCode.Modulo:
                    changed |= PropagateArithmetic(instruction, method) || PropagateIntegerResult(instruction, method);
                    break;
                case OpCode.Not when instruction.Operands is [LocalVariable destination, LocalVariable { Type.FullName: "System.Boolean" }]
                    && IsGuardOnlyResult(destination, instruction, method):
                    // IlGenerator emits boolean Not as ceq 0, not bitwise complement.
                    // Keep its result typed even when the lifter introduced Not before
                    // comparison-result seeding (rather than the late flag simplifier).
                    changed |= SetTypeRespectingBooleanClaim(destination, method.AppContext.SystemTypes.SystemBooleanType, method,
                        allDefinitions);
                    break;
                case OpCode.Negate:
                    changed |= PropagateArithmetic(instruction, method)
                        || PropagateBooleanResult(instruction, method, allDefinitions)
                        || PropagateIntegerResult(instruction, method);
                    break;
                case OpCode.And or OpCode.Or or OpCode.Xor or OpCode.Not
                    or OpCode.ShiftLeft or OpCode.ShiftRight:
                    changed |= PropagateBooleanResult(instruction, method, allDefinitions) || PropagateIntegerResult(instruction, method);
                    break;
            }
        }

        return changed;
    }

    // A Convert's result type: its destination register's width, signed or unsigned
    // as the instruction says. Never inferred from the converted operand - that is
    // what separates a conversion from a move.
    internal static TypeAnalysisContext ConversionResultType(Instruction instruction, MethodAnalysisContext method)
    {
        var systemTypes = method.AppContext.SystemTypes;
        if (instruction.NativeFloatWidthBits == 32)
            return systemTypes.SystemSingleType;
        if (instruction.NativeFloatWidthBits == 64)
            return systemTypes.SystemDoubleType;
        if (instruction.NativeIntegerWidthBits == 64)
            return instruction.ConversionUnsigned
                ? systemTypes.SystemUInt64Type : systemTypes.SystemInt64Type;
        return instruction.ConversionUnsigned
            ? systemTypes.SystemUInt32Type : systemTypes.SystemInt32Type;
    }

    // Types that reach a Boolean slot as raw bits: the flag itself or a 4-byte integer the
    // store truncates to the same byte pattern the binary wrote. Anything else - a reference,
    // a managed pointer, a wider value - has no legal conversion.
    private static bool BooleanSlotTypeSatisfied(TypeAnalysisContext? type) =>
        type?.FullName is "System.Boolean" or "System.Byte" or "System.SByte" or "System.Char"
            or "System.Int16" or "System.UInt16" or "System.Int32" or "System.UInt32";

    // A local may only claim System.Boolean when every definition feeding it proves a flag
    // or a same-width integer. A definition-less local - a register the analysis never
    // resolved - emits an unconstrained object and breaks the claim.
    private static bool LocalBooleanClaimConsistent(LocalVariable local,
        IReadOnlyDictionary<LocalVariable, IReadOnlyList<Instruction>> allDefinitions) =>
        allDefinitions.TryGetValue(local, out var defs)
        && defs.All(def => !DefBreaksBooleanClaim(def, allDefinitions, []));

    // The claim is also kept when the local is read somewhere an emitted System.Object
    // cannot honestly carry the flag: a branch condition (a boxed flag makes brtrue
    // silently always-true), a comparison, arithmetic, a typed slot (an object reaching
    // it needs a castclass/unbox the binary never made), or a member/address base. Only
    // locals consumed exclusively through System.Object slots may honestly drop the claim.
    private static bool MayClaimBoolean(LocalVariable local, MethodAnalysisContext method,
        IReadOnlyDictionary<LocalVariable, IReadOnlyList<Instruction>> allDefinitions) =>
        LocalBooleanClaimConsistent(local, allDefinitions)
        || !AllUsesObjectCompatible(local, method, []);

    private const string BooleanClaimVetoedKey = "BooleanClaimVetoed";

    // A claim attempt the gate vetoes is recorded: the local falls back to an
    // object slot, and IlGenerator wraps that slot's contract so any scalar
    // edge reaching it keeps the named note the Boolean-typed slot emitted.
    private static bool TryClaimBoolean(LocalVariable local, MethodAnalysisContext method,
        IReadOnlyDictionary<LocalVariable, IReadOnlyList<Instruction>> allDefinitions)
    {
        if (MayClaimBoolean(local, method, allDefinitions))
            return true;
        if (method.GetExtraData<HashSet<LocalVariable>>(BooleanClaimVetoedKey) is not { } vetoed)
            method.PutExtraData(BooleanClaimVetoedKey, vetoed = []);
        vetoed.Add(local);
        return false;
    }

    internal static bool CarriesVetoedBooleanClaim(LocalVariable local, MethodAnalysisContext context) =>
        context.GetExtraData<HashSet<LocalVariable>>(BooleanClaimVetoedKey)?.Contains(local) == true;

    private static bool SetTypeRespectingBooleanClaim(LocalVariable local, TypeAnalysisContext? type,
        MethodAnalysisContext method,
        IReadOnlyDictionary<LocalVariable, IReadOnlyList<Instruction>> allDefinitions) =>
        type is { FullName: "System.Boolean" }
            ? TryClaimBoolean(local, method, allDefinitions) && SetTypeIfUnknown(local, type)
            : SetTypeIfUnknown(local, type);

    private static bool IsObjectSlotType(TypeAnalysisContext? type) =>
        type?.FullName == "System.Object";

    // Whether every read of this local sits in a position where a System.Object value is
    // both legal and semantics-preserving: only stores into object-typed slots and
    // object-typed parameters/returns qualify. Any other use makes the Boolean claim the
    // safer emission - the disagreeing producers then keep their named diagnostics.
    private static bool AllUsesObjectCompatible(LocalVariable local, MethodAnalysisContext method,
        HashSet<LocalVariable> visiting)
    {
        if (!visiting.Add(local))
            return false;
        var result = true;
        foreach (var user in method.ControlFlowGraph!.Instructions)
            for (var i = 0; i < user.Operands.Count; i++)
            {
                var operand = user.Operands[i];
                if (!ContainsLocal(operand, local))
                    continue;
                // The destination position writes the local; it is not a use. A local
                // nested inside a compound destination is read (a host, base or index).
                if (ReferenceEquals(user.Destination, local) && ReferenceEquals(operand, local))
                    continue;
                if (!UseIsObjectCompatible(user, i, operand, local, method, visiting))
                {
                    result = false;
                    break;
                }
            }
        visiting.Remove(local);
        return result;
    }

    private static bool UseIsObjectCompatible(Instruction user, int operandIndex, IOperand operand,
        LocalVariable local, MethodAnalysisContext method, HashSet<LocalVariable> visiting)
    {
        switch (user.OpCode)
        {
            case OpCode.Move:
                // Only a bare-local source reaching a plain slot can carry the object
                // honestly; compound source operands and destination shapes are reads.
                return operandIndex > 0 && ReferenceEquals(operand, local)
                    && SlotAcceptsObjectValue(user.Operands[0], method, visiting);
            case OpCode.Phi:
                return ReferenceEquals(operand, local)
                    && SlotAcceptsObjectValue(user.Operands[0], method, visiting);
            case OpCode.Call or OpCode.CallVoid:
            {
                if (user.Operands.OfType<MethodAnalysisContext>().FirstOrDefault() is not { } target)
                    return false;
                var paramIndex = user.OpCode == OpCode.Call
                    ? (target.IsStatic ? 2 : 3)
                    : (target.IsStatic ? 1 : 2);
                if (operandIndex < paramIndex || !ReferenceEquals(operand, local))
                    return false;
                var paramPosition = operandIndex - paramIndex;
                return paramPosition < target.Parameters.Count
                    && IsObjectSlotType(target.Parameters[paramPosition].ParameterType);
            }
            case OpCode.Return:
                return ReferenceEquals(operand, local) && IsObjectSlotType(method.ReturnType);
            default:
                return false;
        }
    }

    // Whether a slot written by a Move/Phi destination can receive the object's values:
    // object-typed slots directly; an untyped local delegates to its own uses.
    private static bool SlotAcceptsObjectValue(IOperand slot, MethodAnalysisContext method,
        HashSet<LocalVariable> visiting) => slot switch
    {
        LocalVariable { Type: { } slotType } => IsObjectSlotType(slotType),
        LocalVariable untyped => AllUsesObjectCompatible(untyped, method, visiting),
        FieldReference field => IsObjectSlotType(field.Field.FieldType),
        SelectedFieldReference selected => IsObjectSlotType(selected.FieldType),
        ArrayAccess { Array.Type: SzArrayTypeAnalysisContext { ElementType: { } element } } =>
            IsObjectSlotType(element),
        _ => false,
    };

    // Whether the value this operand can carry is provably a flag or a same-width integer.
    // Recurses through copy and merge definitions; cycles fail closed.
    private static bool BooleanClaimSatisfied(IOperand operand,
        IReadOnlyDictionary<LocalVariable, IReadOnlyList<Instruction>> allDefinitions,
        HashSet<LocalVariable> visiting)
    {
        switch (operand)
        {
            case LocalVariable { Type: { } type }:
                return BooleanSlotTypeSatisfied(type);
            case LocalVariable local:
                if (!visiting.Add(local))
                    return false;
                var consistent = allDefinitions.TryGetValue(local, out var defs)
                    && defs.All(def => !DefBreaksBooleanClaim(def, allDefinitions, visiting));
                visiting.Remove(local);
                return consistent;
            case FieldReference field:
                return BooleanSlotTypeSatisfied(field.Field.FieldType);
            case ArrayElementFieldReference elementField:
                return BooleanSlotTypeSatisfied(elementField.Field.FieldType);
            case ArrayAccess { Array.Type: SzArrayTypeAnalysisContext { ElementType: { } elementType } }:
                return BooleanSlotTypeSatisfied(elementType);
            case Immediate { Value: >= int.MinValue and <= uint.MaxValue }:
            case ArrayLength:
                return true;
            case Instruction instruction:
                return !DefBreaksBooleanClaim(instruction, allDefinitions, visiting);
            default:
                return false;
        }
    }

    // Whether this definition can produce a value with no legal crossing into a
    // System.Boolean slot.
    private static bool DefBreaksBooleanClaim(Instruction def,
        IReadOnlyDictionary<LocalVariable, IReadOnlyList<Instruction>> allDefinitions,
        HashSet<LocalVariable> visiting)
    {
        switch (def.OpCode)
        {
            // A comparison or boolean-logic result is exactly the 0/1 flag the slot wants;
            // integer arithmetic on satisfied operands yields a same-width integer.
            case >= OpCode.CheckEqual and <= OpCode.CheckLessOrEqual:
            case OpCode.Not or OpCode.And or OpCode.Or or OpCode.Xor or OpCode.Negate:
            case OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide
                or OpCode.Modulo or OpCode.ShiftLeft or OpCode.ShiftRight:
            case OpCode.Move or OpCode.Phi:
                return def.Operands.Skip(1).Any(operand => !BooleanClaimSatisfied(operand, allDefinitions, visiting));
            case OpCode.Call or OpCode.CallVoid or OpCode.IndirectCall or OpCode.Newobj:
                var callee = def.Operands.OfType<MethodAnalysisContext>().FirstOrDefault();
                return !BooleanSlotTypeSatisfied(callee?.ReturnType);
            default:
                return true;
        }
    }

    private static bool IsGuardOnlyResult(LocalVariable local, Instruction producer, MethodAnalysisContext method)
        => IsGuardOnlyResult(local, producer, method, new HashSet<LocalVariable>());

    private static bool IsGuardOnlyResult(LocalVariable local, Instruction producer, MethodAnalysisContext method, HashSet<LocalVariable> active)
    {
        // Mixed native pointer/zero phis can flow types backwards into a receiver.
        // Permit only direct branches and logical-Not chains ending in branches:
        // no copy/phi/arithmetic escapes, incompatible known types, or cycles.
        if (!active.Add(local))
            return false;
        var reachesGuard = false;
        foreach (var user in method.ControlFlowGraph!.Instructions)
        {
            if (ReferenceEquals(user, producer))
                continue;
            foreach (var operand in user.Operands)
            {
                if (!ContainsLocal(operand, local))
                    continue;
                if (user.OpCode == OpCode.ConditionalJump && ReferenceEquals(operand, local))
                {
                    reachesGuard = true;
                    continue;
                }
                if (user.OpCode == OpCode.Not && user.Operands is [LocalVariable next, var input]
                    && ReferenceEquals(input, local) && ReferenceEquals(operand, input)
                    && (next.Type == null || next.Type.FullName == "System.Boolean")
                    && IsGuardOnlyResult(next, user, method, active))
                {
                    reachesGuard = true;
                    continue;
                }
                if (user.OpCode is OpCode.And or OpCode.Or or OpCode.Xor
                    && user.Destination is LocalVariable combined
                    && user.Sources.All(source => ReferenceEquals(source, local)
                        || source is LocalVariable { Type.FullName: "System.Boolean" }
                        || source is Immediate { Value: 0 or 1 })
                    && (combined.Type == null || combined.Type.FullName == "System.Boolean")
                    && (combined.Type?.FullName == "System.Boolean"
                        || IsGuardOnlyResult(combined, user, method, active)))
                {
                    reachesGuard = true;
                    continue;
                }
                return false;
            }
        }
        active.Remove(local);
        return reachesGuard;
    }

    public static void ResolveLateGeneratedTypes(MethodAnalysisContext method)
    {
        var int32 = method.AppContext.SystemTypes.SystemInt32Type;
        var changed = true;

        while (changed)
        {
            changed = false;
            foreach (var instruction in method.ControlFlowGraph!.Instructions)
            {
                if (instruction.OpCode is OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.VectorMin or OpCode.VectorMax
                    or OpCode.Divide or OpCode.Modulo or OpCode.Negate)
                    changed |= PropagateArithmetic(instruction, method);

                if (instruction.OpCode == OpCode.Move
                    && instruction.Operands is [LocalVariable destination, ArrayLength])
                    changed |= SetTypeIfUnknown(destination, int32);

                foreach (var access in instruction.Operands.OfType<ArrayAccess>())
                    if (access.Index is LocalVariable index)
                        changed |= SetTypeIfUnknown(index, int32);

                foreach (var access in instruction.Operands.OfType<ArrayElementFieldReference>())
                    if (access.Index is LocalVariable index)
                        changed |= SetTypeIfUnknown(index, int32);

                if (instruction.OpCode is OpCode.CheckGreater or OpCode.CheckLess
                    or OpCode.CheckGreaterOrEqual or OpCode.CheckLessOrEqual)
                {
                    var left = instruction.Operands[1];
                    var right = instruction.Operands[2];
                    if (left is LocalVariable leftLocal)
                        changed |= SetTypeIfUnknown(leftLocal,
                            IntegerResultType(right, method) ?? IntegerImmediateType(right, method));
                    if (right is LocalVariable rightLocal)
                        changed |= SetTypeIfUnknown(rightLocal,
                            IntegerResultType(left, method) ?? IntegerImmediateType(left, method));
                }
            }
        }

        // Same kind-splitting as in ResolveTypesAndFields, applied to the copies
        // SSA teardown and copy coalescing leave behind.
        SplitScalarOperandViews(method);
        VectorLanePacking.SurrenderPackedArgs(method);

        // The `arr == null`/`arr + 32` arm pairs of `new Span(arr)` only become
        // visible after SSA teardown produces the edge copies.
        RecoverArrayBackedSpanStores(method);
    }

    private static bool PropagateBooleanResult(Instruction instruction, MethodAnalysisContext method,
        IReadOnlyDictionary<LocalVariable, IReadOnlyList<Instruction>> allDefinitions)
    {
        if (instruction.OpCode is not (OpCode.And or OpCode.Or or OpCode.Xor)
            || instruction.Destination is not LocalVariable { Type: null } destination
            || instruction.Sources.Count == 0
            || instruction.Sources.Any(source => source is not LocalVariable { Type.FullName: "System.Boolean" }))
            return false;

        return SetTypeRespectingBooleanClaim(destination, method.AppContext.SystemTypes.SystemBooleanType, method,
            allDefinitions);
    }

    // A local assigned a float/double literal (a lifted rodata constant load) is that float type
    private static void SeedFloatLiterals(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move || instruction.Operands[0] is not LocalVariable destination)
                continue;

            destination.Type = instruction.Operands[1] switch
            {
                FloatLiteral => method.AppContext.SystemTypes.SystemSingleType,
                DoubleLiteral => method.AppContext.SystemTypes.SystemDoubleType,
                _ => destination.Type,
            };
        }
    }

    private static void SeedNativeIntegerWidths(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.NativeIntegerWidthBits == 32 && instruction.Destination is LocalVariable destination)
                SetTypeIfUnknown(destination, method.AppContext.SystemTypes.SystemInt32Type);
        }
    }

    private static void SeedNativeFloatWidths(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.Destination is not LocalVariable destination)
                continue;
            if (instruction.NativeFloatWidthBits == 32)
                SetTypeIfUnknown(destination, method.AppContext.SystemTypes.SystemSingleType);
            else if (instruction.NativeFloatWidthBits == 64)
                SetTypeIfUnknown(destination, method.AppContext.SystemTypes.SystemDoubleType);
        }
    }

    // Preserve numeric result types without guessing pointer arithmetic or mixed widths.
    private static bool PropagateArithmetic(Instruction instruction, MethodAnalysisContext method)
    {
        // A negate on a whole-vector operand lowers to VectorN.op_UnaryNegation. Fill
        // only - a seeded scalar destination is an honest lane view the operand
        // splitter reads as vector.x.
        if (instruction.OpCode is OpCode.Negate
            && instruction.Operands is [LocalVariable { Type: null } negatedDestination, var negatedOperand]
            && UnityVectorOperandType(negatedOperand) is { } negatedVectorType)
        {
            negatedDestination.Type = negatedVectorType;
            return true;
        }

        if (instruction.Operands is not [LocalVariable destination, var left, var right])
            return false;

        // Lane-wise min/max are like add/subtract: no `VectorN min scalar` form
        // exists, so a mixed pair is scalar lane math, not a vector op.
        if (instruction.OpCode is OpCode.VectorMin or OpCode.VectorMax
            && UnityVectorOperandType(left) is { } leftMinVector
            && leftMinVector.FullName == UnityVectorOperandType(right)?.FullName)
        {
            if (destination.Type == leftMinVector)
                return false;
            destination.Type = leftMinVector;
            return true;
        }

        // A binop on a whole-vector operand lowers to the vector operator
        // (op_Addition/op_Subtraction/op_Multiply/op_Division): the result register
        // holds the vector even when a consumer views it as a scalar. Fill only -
        // a seeded scalar destination is an honest lane view the operand splitter
        // reads as vector.x. Add/Subtract have no `VectorN + scalar` form, so a
        // mixed pair is scalar lane math (`fadd s0,s1,s2`), not a vector op -
        // both operands must prove the same VectorN before the result claims it.
        // Divide has no `float / VectorN`; Multiply keeps its `VectorN op float`
        // forms.
        if (instruction.OpCode is OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide
            && destination.Type == null)
        {
            var leftVectorType = UnityVectorOperandType(left);
            var rightVectorType = UnityVectorOperandType(right);
            var binopVectorType = instruction.OpCode switch
            {
                OpCode.Add or OpCode.Subtract
                    when leftVectorType != null
                        && leftVectorType.FullName == rightVectorType?.FullName
                    => leftVectorType,
                OpCode.Divide => leftVectorType,
                OpCode.Multiply => leftVectorType ?? rightVectorType,
                _ => null,
            };
            if (binopVectorType != null)
            {
                destination.Type = binopVectorType;
                return true;
            }
        }

        // `Int32 = Int32 op x`: an integer result whose other operand has that same type fixes an
        // untyped operand to it (the native op ran at that width). This is what types a loop
        // counter that only ever meets immediates and a typed division.
        if (instruction.OpCode is OpCode.Add or OpCode.Subtract or OpCode.Multiply or OpCode.Divide or OpCode.Modulo
            && IntegerResultType(destination, method) is { } resultType)
        {
            var typed = false;
            if (left is LocalVariable { Type: null } untypedLeft && !ReferenceEquals(untypedLeft, destination)
                && (IntegerResultType(right, method) ?? IntegerImmediateType(right, method)) == resultType)
                typed |= SetTypeIfUnknown(untypedLeft, resultType);
            if (right is LocalVariable { Type: null } untypedRight && !ReferenceEquals(untypedRight, destination)
                && (IntegerResultType(left, method) ?? IntegerImmediateType(left, method)) == resultType)
                typed |= SetTypeIfUnknown(untypedRight, resultType);
            if (typed)
                return true;
        }

        if (destination.Type != null)
            return false;

        if ((FloatOperandType(left, method) ?? FloatOperandType(right, method)) is { } floatType)
            return SetTypeIfUnknown(destination, floatType);

        var integerType = IntegerResultType(left, method) ?? IntegerResultType(right, method)
            ?? IntegerImmediateType(left, method) ?? IntegerImmediateType(right, method);
        if (integerType == null)
            return false;

        bool Compatible(IOperand operand) => operand is Immediate immediate
            ? integerType.FullName == "System.Int64" || immediate.Value is >= int.MinValue and <= uint.MaxValue
            : IntegerResultType(operand, method) == integerType;

        if (!Compatible(left) || !Compatible(right))
            return false;

        var changed = SetTypeIfUnknown(destination, integerType);
        return changed;
    }

    private static TypeAnalysisContext? UnityVectorOperandType(IOperand operand)
    {
        var type = operand switch
        {
            LocalVariable local => local.Type,
            FieldReference field => field.Field.FieldType,
            SelectedFieldReference selected => selected.FieldType,
            _ => null,
        };
        return type?.FullName is "UnityEngine.Vector2" or "UnityEngine.Vector3" or "UnityEngine.Vector4" ? type : null;
    }

    private static TypeAnalysisContext? IntegerImmediateType(IOperand operand, MethodAnalysisContext method) =>
        operand is Immediate immediate
            ? immediate.Value is >= int.MinValue and <= uint.MaxValue
                ? method.AppContext.SystemTypes.SystemInt32Type
                : method.AppContext.SystemTypes.SystemInt64Type
            : null;

    internal static bool ContainsLocal(IOperand? operand, LocalVariable local) => operand switch
    {
        LocalVariable value => ReferenceEquals(value, local),
        MemoryOperand memory => ContainsLocal(memory.Base, local) || ContainsLocal(memory.Index, local),
        AddressOf address => ContainsLocal(address.Target, local),
        ReferenceCast referenceCast => ReferenceEquals(referenceCast.Value, local),
        FieldReference field => ReferenceEquals(field.Local, local),
        SelectedFieldReference selected => ReferenceEquals(selected.Selector, local)
            || selected.Choices.Any(c => ReferenceEquals(c.Field.Local, local)),
        ArrayAccess array => ReferenceEquals(array.Array, local) || ContainsLocal(array.Index, local),
        ArrayElementFieldReference field => ReferenceEquals(field.Array, local) || ContainsLocal(field.Index, local),
        ArrayLength length => ReferenceEquals(length.Array, local),
        _ => false,
    };

    // A copy between locals that can never hold each other's value - a register or stack slot
    // merging unrelated managed references across paths - has no legal managed store: emitting it
    // produces an invalid stloc, and forwarding the source into a typed position such as a field
    // receiver produces an invalid ldflda. The destination is left at default instead. This is the
    // same bit-pattern rule SsaForm.Remove applies to phi edges; the check is symmetric so either
    // direction of the relationship is sufficient to permit the copy.
    //
    // A copy whose destination is a pointer local (T& or T*) is exempt when the source is the
    // same kind of pointer, whatever the element type: the copied value is an address, so
    // forwarding it into address-position uses is representable - each use re-emits the
    // address from the source rather than needing a typed slot - and a mismatched source
    // reaching the IL emitter is converted into a typed scratch cell with a decompiler-issue
    // note rather than an invalid stloc. Managed pointers are invariant in CIL (a &U slot
    // cannot receive a &T value) so in strict form copies between pointer locals of
    // different element types stay illegal, as does any copy from a class source, which
    // would turn a resolvable managed-pointer access into a raw object+offset store under
    // [dest + off] memory bases. Pass allowByRefReinterpret at every site whose outcome is
    // forwarding (the source reaches the uses); keep the strict form where the copy itself
    // is emitted or the local sits under an address-of or field access.
    internal static bool NoLegalManagedCopy(LocalVariable destination, LocalVariable source, bool allowByRefReinterpret = false) =>
        destination.Type is { IsValueType: false } destinationType
        && source.Type is { IsValueType: false } sourceType
        && !(allowByRefReinterpret && SamePointerKind(destinationType, sourceType))
        && !sourceType.IsAssignableTo(destinationType)
        && !destinationType.IsAssignableTo(sourceType);

    private static bool SamePointerKind(TypeAnalysisContext destinationType, TypeAnalysisContext sourceType) =>
        (destinationType is ByRefTypeAnalysisContext or PointerTypeAnalysisContext)
        && destinationType.GetType() == sourceType.GetType();

    // An integer operand makes the result an integer. Excludes bool operands so flag logic stays boolean.
    private static bool PropagateIntegerResult(Instruction instruction, MethodAnalysisContext method)
    {
        if (instruction.Operands[0] is not LocalVariable { Type: null } destination)
            return false;

        TypeAnalysisContext? integerType = null;
        for (var i = 1; i < instruction.Operands.Count; i++)
        {
            var operandType = IntegerResultType(instruction.Operands[i], method)
                ?? IntegerImmediateType(instruction.Operands[i], method);
            if (operandType == null)
                continue;

            // A wide immediate is still a width-bearing operand. Selecting the
            // first local's type loses that fact for native bitwise lowering.
            if (operandType.FullName == "System.Int64")
            {
                integerType = operandType;
                break;
            }

            integerType ??= operandType;
        }

        return integerType != null && SetTypeIfUnknown(destination, integerType);
    }

    private static TypeAnalysisContext? IntegerResultType(IOperand operand, MethodAnalysisContext method)
    {
        var type = operand switch
        {
            LocalVariable { Type: { } localType } => localType,
            FieldReference field => field.Field.FieldType,
            SelectedFieldReference selected => selected.FieldType,
            _ => null,
        };

        return type?.FullName switch
        {
            "System.Byte" or "System.SByte" or "System.Int16" or "System.UInt16"
                or "System.Int32" or "System.UInt32" or "System.Char" => method.AppContext.SystemTypes.SystemInt32Type,
            "System.Int64" or "System.UInt64" => method.AppContext.SystemTypes.SystemInt64Type,
            _ => null,
        };
    }

    private static TypeAnalysisContext? FloatOperandType(IOperand operand, MethodAnalysisContext method) =>
        operand switch
        {
            FloatLiteral => method.AppContext.SystemTypes.SystemSingleType,
            DoubleLiteral => method.AppContext.SystemTypes.SystemDoubleType,
            LocalVariable { Type: { FullName: "System.Single" } single } => single,
            LocalVariable { Type: { FullName: "System.Double" } @double } => @double,
            FieldReference { Field.FieldType.FullName: "System.Single" } field => field.Field.FieldType,
            FieldReference { Field.FieldType.FullName: "System.Double" } field => field.Field.FieldType,
            SelectedFieldReference { FieldType.FullName: "System.Single" } selected => selected.FieldType,
            SelectedFieldReference { FieldType.FullName: "System.Double" } selected => selected.FieldType,
            _ => null,
        };

    private static bool PropagateMove(Instruction move, MethodAnalysisContext method, int pointerSize,
        TypeAnalysisContext systemInt32Type,
        IReadOnlyDictionary<LocalVariable, Instruction> definitions,
        IReadOnlyDictionary<LocalVariable, IReadOnlyList<Instruction>> allDefinitions)
    {
        var destination = move.Operands[0];
        var source = move.Operands[1];

        // Move local, local: copy a known type in whichever direction is missing it.
        if (destination is LocalVariable destLocal && source is LocalVariable sourceLocal)
        {
            if (destLocal.Type?.FullName == "System.Object"
                && sourceLocal.Type is { IsValueType: false } sourceType
                && sourceType.FullName != "System.Object")
            {
                destLocal.Type = sourceType;
                return true;
            }
            return SetTypeRespectingBooleanClaim(destLocal, sourceLocal.Type, method, allDefinitions)
                || SetTypeRespectingBooleanClaim(sourceLocal, destLocal.Type, method, allDefinitions);
        }

        // Move local, field: a field load types its result with the field's type. This is the edge
        // that lets the loaded value go on to be the base of a further field access.
        if (destination is LocalVariable loadDest && source is FieldReference loadField)
        {
            var fieldType = loadField.Field.FieldType;
            if (loadDest.Type?.FullName == fieldType.FullName)
                return false;
            if (fieldType.FullName == "System.Boolean")
                return TryClaimBoolean(loadDest, method, allDefinitions)
                    && SetTypeIfUnknown(loadDest, fieldType);
            loadDest.Type = fieldType;
            return true;
        }

        if (destination is LocalVariable selectedDest && source is SelectedFieldReference selectedField)
        {
            if (selectedDest.Type?.FullName == selectedField.FieldType.FullName)
                return false;
            if (selectedField.FieldType.FullName == "System.Boolean")
                return TryClaimBoolean(selectedDest, method, allDefinitions)
                    && SetTypeIfUnknown(selectedDest, selectedField.FieldType);
            selectedDest.Type = selectedField.FieldType;
            return true;
        }

        // Move field, local: a field store types the stored value with the field's type.
        // A synthesized lane-pack store is exempt: the source supplies one lane of
        // a register-spread aggregate, so its honest type is whatever its own
        // producer proves (often the whole vector type). Smearing the lane field's
        // scalar type onto it would retype the register's other uses scalar and
        // turn a spellable whole vector into a diagnosed coercion.
        if (destination is FieldReference storeField && source is LocalVariable storeSource
            && !VectorLanePacking.IsPackLocal(storeField.Local))
            return SetTypeRespectingBooleanClaim(storeSource, storeField.Field.FieldType, method, allDefinitions);

        // ArrayLength is emitted as ldlen/conv.i4, so its result is always Int32 when the
        // source is a recovered managed array. Do not infer this from arbitrary references.
        if (destination is LocalVariable lengthDestination
            && source is ArrayLength { Array.Type: SzArrayTypeAnalysisContext })
            return SetTypeIfUnknown(lengthDestination, systemInt32Type);

        // An element of T[] is a T, whether we loaded it (reference arrays) or only computed its address
        if (destination is LocalVariable { Type: null } elementDest
            && source is MemoryOperand { Base: LocalVariable { Type: SzArrayTypeAnalysisContext { ElementType: { } elementType } } } elementAccess
            && (elementAccess.Index != null || elementAccess.Addend >= 4L * pointerSize))
            return SetTypeIfUnknown(elementDest, elementType);

        // A load at the array data offset through pointer arithmetic is also an element load:
        // the base proves `array + scaled index` rather than naming the array local directly.
        // ArrayRecovery rewrites the same shape into an ArrayAccess later, but only after type
        // propagation, so resolve the array through the copy/pointer def chain here. Reference
        // elements only - a whole pointer-sized load is exactly one element for them.
        if (destination is LocalVariable { Type: null } pointerElementDest
            && source is MemoryOperand { Index: null, Scale: 0, Addend: var pointerAddend, Base: { } pointerBase }
            && pointerAddend == 4L * pointerSize
            && PointerArithmeticElementType(pointerBase, definitions, []) is { IsValueType: false } pointerElementType)
            return SetTypeIfUnknown(pointerElementDest, pointerElementType);

        // Move local, [byref]: dereferencing a managed pointer to a reference type yields that referent
        // (a struct byref accesses fields directly with no deref, so this only fires for class referents).
        if (destination is LocalVariable { Type: null } derefDest
            && source is MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable { Type: ByRefTypeAnalysisContext { ElementType: { IsValueType: false } referent } } })
            return SetTypeIfUnknown(derefDest, referent);

        // Move local, [obj]: offset 0 of a reference-typed value is its klass pointer.
        if (destination is LocalVariable { Type: null } klassDest
            && source is MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable { Type: { } baseType } }
            && baseType is not (RuntimeClassTypeAnalysisContext or StaticFieldStorageTypeAnalysisContext or RuntimeMethodInfoAnalysisContext or RuntimeFieldInfoAnalysisContext or ByRefTypeAnalysisContext)
            && !baseType.IsValueType)
            return SetTypeIfUnknown(klassDest, new RuntimeClassTypeAnalysisContext(baseType, baseType.DeclaringAssembly));

        return false;
    }

    // Whether `operand` resolves, through single-definition Move and Add (pointer arithmetic)
    // chains, to a local carrying a managed array type - and if so its element type. Mirrors the
    // proof ArrayRecovery.DerivedElementAccess applies to the same `Add(array, scaled index)`
    // shape when it later rewrites the access.
    private static TypeAnalysisContext? PointerArithmeticElementType(IOperand operand,
        IReadOnlyDictionary<LocalVariable, Instruction> definitions, HashSet<LocalVariable> visiting)
    {
        if (operand is not LocalVariable local || !visiting.Add(local))
            return null;

        if (local.Type is SzArrayTypeAnalysisContext { ElementType: { } elementType })
            return elementType;

        if (!definitions.TryGetValue(local, out var definition) || definition == null)
            return null;

        return definition switch
        {
            { OpCode: OpCode.Move, Operands: [_, var moveSource] }
                => PointerArithmeticElementType(moveSource, definitions, visiting),
            { OpCode: OpCode.Add, Operands: [_, var left, var right] }
                => PointerArithmeticElementType(left, definitions, visiting)
                    ?? PointerArithmeticElementType(right, definitions, visiting),
            _ => null,
        };
    }

    // The type an operand proves for typing flows - a local's own type or the
    // field type a field read carries.
    private static TypeAnalysisContext? OperandType(IOperand operand) => operand switch
    {
        LocalVariable { Type: { } type } => type,
        FieldReference field => field.Field.FieldType,
        SelectedFieldReference selected => selected.FieldType,
        _ => null,
    };

    // A phi is a copy from each predecessor's value, so types flow both ways across it - mirroring
    // the bidirectional Move copies it decays into once SSA is destroyed.
    private static bool PropagatePhi(Instruction phi, MethodAnalysisContext method,
        IReadOnlyDictionary<LocalVariable, Instruction> definitions,
        IReadOnlyDictionary<LocalVariable, IReadOnlyList<Instruction>> allDefinitions)
    {
        if (phi.Operands[0] is not LocalVariable destination)
            return false;

        var changed = false;

        if (destination.Type?.FullName == "System.Object")
        {
            var concrete = phi.Operands.Skip(1).OfType<LocalVariable>()
                .Select(input => input.Type)
                .Where(type => type is { IsValueType: false } && type.FullName != "System.Object")
                .GroupBy(type => type!.FullName).Select(group => group.First()).ToArray();
            if (concrete is [{ } only]
                && phi.Operands.Skip(1).OfType<LocalVariable>()
                    .All(input => input.Type == null || input.Type.FullName is "System.Object" || input.Type.FullName == only.FullName))
            {
                destination.Type = only;
                changed = true;
            }
        }

        // Forward: an untyped phi result takes the type of any typed input - except a
        // Boolean, which a phi may only claim when every input proves a flag or a 4-byte
        // integer. A phi merging a 0/1 flag on one edge with a reference, pointer or wider
        // value on another is a register holding unrelated contents across paths, not a
        // bool slot: claiming System.Boolean manufactures a truthiness conversion the
        // binary never made on every disagreeing edge.
        if (destination.Type == null)
        {
            for (var i = 1; i < phi.Operands.Count; i++)
            {
                if (OperandType(phi.Operands[i]) is { } inputType)
                {
                    if (inputType.FullName != "System.Boolean"
                        || TryClaimBoolean(destination, method, allDefinitions))
                        changed = SetTypeIfUnknown(destination, inputType);
                    break;
                }
            }
        }

        // Backward: a typed phi result types each of its still-untyped inputs - except inputs
        // that are themselves produced by a copy or a merge. Those locals carry the value their
        // producer proves; a register reused upstream for an unrelated value (e.g. a loop
        // backedge delivering a collected list where the joined type is `this`) must not be
        // retyped to this phi's joined type - that asserts a type the binary never proves and
        // emits impossible `as` conversions downstream.
        if (destination.Type != null)
        {
            for (var i = 1; i < phi.Operands.Count; i++)
            {
                if (phi.Operands[i] is LocalVariable input
                    && !(definitions.TryGetValue(input, out var inputDefinition)
                        && inputDefinition.OpCode is OpCode.Move or OpCode.Phi))
                    changed |= SetTypeIfUnknown(input, destination.Type);
            }
        }

        return changed;
    }

    private static bool PropagateFromCallParameters(MethodAnalysisContext method, bool allowCanonicalCallTypes)
    {
        var changed = false;

        // A lea and the call it's passed to are still separate here. The address only gets folded into the
        // call later, so an argument's address-of has to be found through the local carrying it.
        var addressesOf = new Dictionary<LocalVariable, LocalVariable>();
        var copiesOf = new Dictionary<LocalVariable, LocalVariable>();
        var defined = new HashSet<LocalVariable>(method.ParameterLocals);
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.Destination is LocalVariable destination)
                defined.Add(destination);
            if (instruction.OpCode == OpCode.Move
                && instruction.Operands[0] is LocalVariable pointer
                && instruction.Operands[1] is AddressOf { Target: LocalVariable pointee })
                addressesOf[pointer] = pointee;
            else if (instruction is { OpCode: OpCode.Move, Operands: [LocalVariable copy, LocalVariable copied] })
                copiesOf[copy] = copied;
        }

        LocalVariable? Addressed(IOperand operand) => operand switch
        {
            AddressOf { Target: LocalVariable direct } => direct,
            LocalVariable local when addressesOf.TryGetValue(local, out var indirect) => indirect,
            _ => null
        };

        // An address carried through copies, as a saved `&enumerator` reloaded for the finally's
        // `Dispose` is (a register, a frame cell, a register again).
        bool CarriesAddress(LocalVariable local)
        {
            for (var depth = 0; depth < 8; depth++)
            {
                if (addressesOf.ContainsKey(local))
                    return true;
                if (!copiesOf.TryGetValue(local, out local!))
                    return false;
            }
            return false;
        }

        var addressUses = new Dictionary<LocalVariable, int>();
        foreach (var call in method.ControlFlowGraph.Instructions.Where(instruction => instruction.IsCall))
        foreach (var operand in call.Operands)
            if (Addressed(operand) is { } cell)
                addressUses[cell] = addressUses.GetValueOrDefault(cell) + 1;

        foreach (var instruction in method.ControlFlowGraph.Instructions)
        {
            if (!instruction.IsCall)
                continue;

            if (instruction.Operands[0] is not MethodAnalysisContext calledMethod)
                continue;

            var deferGenericSlots = !allowCanonicalCallTypes
                && MetadataResolver.ErasedGenericArgumentCount(calledMethod) > 0;
            var definition = (calledMethod as ConcreteGenericMethodAnalysisContext)?.BaseMethodContext ?? calledMethod;

            var thisParamIndex = instruction.OpCode == OpCode.CallVoid ? 1 : 2;

            // Return value: a constructor yields its declaring type, otherwise the declared return type.
            if (instruction.Destination is LocalVariable returnValue
                && (!deferGenericSlots || definition.Name is not (".ctor" or ".cctor")
                    && !definition.ReturnType.HasAnyGenericParameters()))
            {
                var producedType = calledMethod.Name is ".ctor" or ".cctor" ? calledMethod.DeclaringType : calledMethod.ReturnType;

                if (producedType != method.AppContext.SystemTypes.SystemVoidType)
                {
                    // A proven generic producer wins over a type inferred backwards from
                    // another use (e.g. Object.op_Inequality consuming a T result).
                    // Hidden struct returns also need their storage uses rewritten by
                    // SharpenHiddenReturnBuffers; leave their type change to that pass.
                    if (calledMethod is ConcreteGenericMethodAnalysisContext
                        && returnValue.HiddenReturnBuffer == null
                        && definition.ReturnType.HasAnyGenericParameters()
                        && MetadataResolver.ErasedGenericArgumentCount(calledMethod) == 0
                        && returnValue.Type?.FullName != producedType?.FullName)
                    {
                        returnValue.Type = producedType;
                        changed = true;
                    }
                    else
                        changed |= SetTypeIfUnknown(returnValue, producedType);
                }
            }


            // Call operands
            // 0. Target
            // 1. ReturnValue
            // 2. thisParam
            // ... parameters

            // CallVoid operands
            // 0. Target
            // 1. thisParam
            // ... parameters
            // 'this' param
            // A value type's instance method takes the address of its receiver: a register that
            // carries `&value` through copies is that address, not the value (`Dispose(&enumerator)`
            // from a frame cell saved for the finally).
            if (!deferGenericSlots && !calledMethod.IsStatic
                && instruction.Operands[thisParamIndex] is LocalVariable thisParam)
            {
                changed |= SetTypeIfUnknown(thisParam,
                    calledMethod.DeclaringType is { IsValueType: true } receiverValue && CarriesAddress(thisParam)
                        ? new ByRefTypeAnalysisContext(receiverValue)
                        : calledMethod.DeclaringType);
            }

            // Value type instance method, first arg is address of value, but we need to type the value
            if (!deferGenericSlots && !calledMethod.IsStatic
                && Addressed(instruction.Operands[thisParamIndex]) is { } addressedReceiver
                && calledMethod.DeclaringType is { IsValueType: true } valueType)
            {
                changed |= SetTypeIfUnknown(addressedReceiver, valueType);
            }

            // Remaining arguments map positionally onto the callee's declared parameters.
            var paramOffset = calledMethod.IsStatic ? 1 : 2;
            if (instruction.OpCode == OpCode.Call) // Skip the return value operand
                paramOffset += 1;

            for (var i = paramOffset; i < instruction.Operands.Count; i++)
            {
                var parameterIndex = i - paramOffset;
                if (parameterIndex > calledMethod.Parameters.Count - 1) // Probably MethodInfo*
                    continue;

                if (deferGenericSlots && definition.Parameters[parameterIndex].ParameterType.HasAnyGenericParameters())
                    continue;
                var parameterType = calledMethod.Parameters[parameterIndex].ParameterType;

                if (parameterType is ByRefTypeAnalysisContext { ElementType: { } referencedType }
                    && Addressed(instruction.Operands[i]) is { } referenced)
                {
                    // An out cell with no other producer is defined by this call, not by
                    // the weaker parameter type of a later consumer. Do not retype a
                    // caller parameter or storage that already has a definition.
                    var producedOut = calledMethod is ConcreteGenericMethodAnalysisContext
                        && definition.Parameters[parameterIndex].ParameterType.HasAnyGenericParameters()
                        && calledMethod.Parameters[parameterIndex].Attributes.HasFlag(ParameterAttributes.Out)
                        && MetadataResolver.ErasedGenericArgumentCount(calledMethod) == 0
                        && !defined.Contains(referenced)
                        && addressUses.GetValueOrDefault(referenced) == 1;
                    if ((referenced.Type == method.AppContext.SystemTypes.SystemObjectType || producedOut)
                        && referencedType != method.AppContext.SystemTypes.SystemObjectType
                        && referenced.Type?.FullName != referencedType.FullName)
                    {
                        referenced.Type = referencedType;
                        changed = true;
                    }
                    else
                        changed |= SetTypeIfUnknown(referenced, referencedType);
                    continue;
                }

                if (instruction.Operands[i] is LocalVariable local)
                    changed |= SetTypeIfUnknown(local, parameterType);
            }
        }

        return changed;
    }

    private static void PropagateFromParameters(MethodAnalysisContext method)
    {
        // 'this'
        if (!method.IsStatic)
        {
            var thisLocal = method.ParameterLocals.FirstOrDefault(p => p.IsThis);
            if (thisLocal != null)
                thisLocal.Type = method.DeclaringType is { GenericParameters.Count: > 0 } generic
                    ? new GenericInstanceTypeAnalysisContext(generic, generic.GenericParameters)
                    : method.DeclaringType;
        }

        if (method.ParameterLocals.FirstOrDefault(p => p.IsMethodInfo) is { } methodInfoLocal && method.DeclaringType is { } owner)
            methodInfoLocal.Type = new RuntimeMethodInfoAnalysisContext(method, owner.DeclaringAssembly);

        if (method.Parameters.Count == 0)
            return;

        // Normal params. Match each local to its parameter by the name it was
        // given - the same identity EmittedLocalType and ParameterForLocal use -
        // because a parameter whose register never produced a local leaves no
        // slot to count, and positional re-mapping then shifts every later
        // local onto the preceding parameter's type.
        foreach (var local in method.ParameterLocals)
        {
            if (local.IsThis || local.IsMethodInfo || local.Name == null)
                continue;

            if (method.Parameters.FirstOrDefault(p => p.ParameterName == local.Name) is { } parameter)
                local.Type = parameter.ParameterType;
        }
    }

    private static void PropagateFromReturn(MethodAnalysisContext method)
    {
        var returns = method.ControlFlowGraph!.Instructions.Where(i => i.OpCode == OpCode.Return);

        foreach (var instruction in returns)
        {
            if (instruction.Operands.Count == 1 && instruction.Operands[0] is LocalVariable local)
                local.Type = method.ReturnType;
        }
    }

    /// <summary>
    /// A scalarized register view (a `Vn`/`Vn.Sk` local) names a window of a physical
    /// SIMD register, so unrelated lifetimes share the register name: a vector binop
    /// writes the whole register on one lifetime while a scalar convert or lane sync
    /// writes a lane view on a sibling. The type fixpoint only ever fills, so when a
    /// sibling's scalar seed reaches a vector def site first - through an integer
    /// operand, a phi merge with a scalar-typed version, or a lane-width write - the
    /// def site's version locks in a type that cannot represent the vector result it
    /// actually holds. Give that def site's lifetime its own vector-typed local and
    /// retarget all of its uses; scalar consumers then read the lane-0 field through
    /// <see cref="SplitScalarOperandViews"/>.
    /// </summary>
    private static void SplitVectorBinopDefSites(MethodAnalysisContext method)
    {
        var instructions = method.ControlFlowGraph!.Instructions;

        foreach (var instruction in instructions)
        {
            if (instruction.OpCode is not (OpCode.Add or OpCode.Subtract or OpCode.Multiply
                    or OpCode.Divide or OpCode.VectorMin or OpCode.VectorMax)
                || instruction.Operands is not [LocalVariable destination, var left, var right]
                || !IsRegisterViewName(destination.Register.Name)
                || destination.Register.Version < 0
                || !IsScalarLaneType(destination.Type))
                continue;
            // Negate is excluded deliberately: `fneg s8, s0` is a scalar lane op whose
            // register-view destination is honestly scalar, and its ISIL is
            // indistinguishable from a vector `fneg v0.4s`.
            // A register-view operand can never be the vector evidence: its type
            // comes from the same fill-only register-window typing this pass
            // exists to fix, so a `Vn`/`Vn.Sk` local carrying a VectorN type may
            // be a sibling lifetime's smear rather than a real vector. Evidence
            // must come from outside the register windows (a spilled `stack_`
            // local or a field typed VectorN) or structurally: a `Vn.Sk` lane
            // operand only exists on the vector-element form
            // (`fmul v0.4s, v4.4s, v0.s[i]`) - scalar forms read whole register
            // views only (`fmul s0, s1, s2` normalizes S registers to `Vn`).
            // For Add/Subtract (and the lane-wise VectorMin/VectorMax) every
            // operand must be a proven vector: `VectorN + scalar`/`scalar +
            // VectorN` is not a legal managed operator, so an Add mixing a
            // scalar-typed or unproven operand with a vector-typed one is scalar
            // lane math (`fadd s0,s1,s2`) whose source local merely carries a
            // vector type. Multiply has both `VectorN op float` directions, so a
            // single vector operand is evidence enough; Divide has no
            // `float / VectorN`, so the left operand must be the vector.
            // `VectorN op VectorM` is legal only for N == M - different widths
            // mean a scalar lane op whose operands carry unrelated types.
            var leftVector = VectorOperandEvidence(left, method);
            var rightVector = VectorOperandEvidence(right, method);
            var leftIsElement = IsLaneViewOperand(left);
            var rightIsElement = IsLaneViewOperand(right);
            var provableVectorOp = instruction.OpCode switch
            {
                OpCode.Multiply => (leftVector ?? rightVector) != null
                    || (leftIsElement && UnityVectorOperandType(right) != null)
                    || (rightIsElement && UnityVectorOperandType(left) != null),
                OpCode.Divide => leftVector != null
                    || (rightIsElement && UnityVectorOperandType(left) != null),
                _ => leftVector != null && rightVector != null,
            };
            if (!provableVectorOp || (leftVector != null && rightVector != null
                    && leftVector.FullName != rightVector.FullName))
                continue;
            var vectorType = leftVector ?? rightVector
                ?? UnityVectorOperandType(left) ?? UnityVectorOperandType(right);
            if (vectorType is null)
                continue;

            var split = new LocalVariable($"{destination.Name}_vec",
                new Register(null,
                    $"VEC_{destination.Register.Name}_{destination.Register.Version}"),
                vectorType);
            method.Locals.Add(split);
            instruction.SetOperand(0, split);

            // Every other operand position holding the old local reads this def
            // site's value, so the whole lifetime retargets to the vector local.
            // A `Vn.Sk` destination names one lane view of the register the
            // vector op wrote whole: scalar slots take that lane's field, and
            // only a slot that expects the whole vector takes the local itself.
            var laneIndex = SingleLaneIndex(destination.Register.Name);
            var laneLeaf = laneIndex >= 0
                ? VectorLanePacking.VectorLanes(vectorType) is { } lanes && laneIndex < lanes.Length
                    ? new FieldReference(lanes[laneIndex], split, 0)
                    : (IOperand?)null
                : null;
            foreach (var other in instructions)
            for (var operandIndex = 0; operandIndex < other.Operands.Count; operandIndex++)
            {
                var operand = other.Operands[operandIndex];
                if (laneLeaf != null && operand is LocalVariable local
                    && ReferenceEquals(local, destination)
                    && !SlotExpectsVector(other, operandIndex, method))
                {
                    other.SetOperand(operandIndex, laneLeaf);
                    continue;
                }
                if (ReplaceLocal(operand, destination, split) is { } rewritten)
                    other.SetOperand(operandIndex, rewritten);
            }
        }
    }

    /// <summary>
    /// The `k` in a `Vn.Sk` lane-view name - the Single lane this view reads of
    /// its register - or -1 for a whole-register name or a non-Single lane
    /// width.
    /// </summary>
    private static int SingleLaneIndex(string? name)
    {
        if (name is null || !IsLaneViewName(name))
            return -1;
        var dot = name.IndexOf('.');
        if (name[dot + 1] != 'S')
            return -1;
        var index = 0;
        for (var i = dot + 2; i < name.Length && char.IsDigit(name[i]); i++)
            index = index * 10 + (name[i] - '0');
        return index;
    }

    /// <summary>
    /// Whether an operand slot expects the whole vector value, where a
    /// lane-viewed local retargets to the `_vec` local itself instead of one
    /// lane leaf: a `Move` destination typed vector, a vector call argument, a
    /// vector `ret`.
    /// </summary>
    private static bool SlotExpectsVector(Instruction use, int operandIndex,
        MethodAnalysisContext method)
    {
        // Phi inputs name the def site's register, not a lane view of it.
        if (use.OpCode == OpCode.Phi)
            return true;
        var expected = use.OpCode switch
        {
            OpCode.Move when operandIndex == 1 => use.Operands[0] switch
            {
                LocalVariable local => local.Type,
                FieldReference field => field.Field.FieldType,
                _ => null,
            },
            OpCode.Return => method.ReturnType,
            OpCode.Call when operandIndex >= 2 =>
                VectorLanePacking.ResolveCallee(method.AppContext, use.Operands[1])
                    ?.Parameters.ElementAtOrDefault(operandIndex - 2)?.ParameterType,
            OpCode.CallVoid or OpCode.IndirectCall when operandIndex >= 1 =>
                VectorLanePacking.ResolveCallee(method.AppContext, use.Operands[0])
                    ?.Parameters.ElementAtOrDefault(operandIndex - 1)?.ParameterType,
            _ => null,
        };
        return expected?.FullName is "UnityEngine.Vector2" or "UnityEngine.Vector3"
            or "UnityEngine.Vector4" or "UnityEngine.Quaternion";
    }

    /// <summary>
    /// The vector type this operand proves for a binop. A register-view local's
    /// own type is never evidence: it is produced by the same fill-only
    /// register-window typing whose smear this pass repairs, so a vector-typed
    /// register view can be a scalar `fmul s` operand wearing a sibling
    /// lifetime's type. The operand it copies from is a different matter -
    /// `fmul s0, s1, s2` where the source local was defined by a Move of a
    /// vector-typed operand carries that operand's type as real evidence.
    /// </summary>
    private static TypeAnalysisContext? VectorOperandEvidence(IOperand operand,
        MethodAnalysisContext method)
    {
        if (operand is not LocalVariable local || !IsRegisterViewName(local.Register.Name))
            return UnityVectorOperandType(operand);
        TypeAnalysisContext? evidence = null;
        var hasMoveDef = false;
        foreach (var definition in method.ControlFlowGraph!.Instructions)
        {
            if (!ReferenceEquals(definition.Destination, local))
                continue;
            if (definition.OpCode != OpCode.Move || definition.Operands.Count < 2)
                return null;
            hasMoveDef = true;
            var sourceType = UnityVectorOperandType(definition.Operands[1]);
            if (sourceType != null && evidence != null
                && evidence.FullName != sourceType.FullName)
                return null;
            evidence ??= sourceType;
        }
        return hasMoveDef ? evidence : null;
    }

    /// <summary>
    /// A `Vn.Sk` lane operand is produced only by a vector-element operand
    /// (`vN.s[i]`), which scalar forms never carry - its presence is structural
    /// proof the lifted instruction was the vector form, independent of types.
    /// </summary>
    private static bool IsLaneViewOperand(IOperand operand)
        => operand is LocalVariable local && IsLaneViewName(local.Register.Name);

    private static bool IsLaneViewName(string? name)
        => name is { Length: >= 4 } && name[0] == 'V' && name.Contains('.')
            && IsRegisterViewName(name);

    // Scalarized SIMD register views are named "Vn" (whole register) or "Vn.Lk"
    // (lane k of register n in element width L). Both view the same physical
    // register, so scalar lifetimes can smear onto a vector def that shares it.
    private static bool IsRegisterViewName(string? name)
    {
        if (name is null || name.Length < 2 || name[0] != 'V' || !char.IsDigit(name[1]))
            return false;

        var i = 1;
        while (i < name.Length && char.IsDigit(name[i]))
            i++;
        if (i == name.Length)
            return true;
        if (name[i] != '.' || i + 1 >= name.Length || name[i + 1] is not ('B' or 'H' or 'S' or 'D'))
            return false;
        i += 2;
        var digitStart = i;
        while (i < name.Length && char.IsDigit(name[i]))
            i++;
        return i > digitStart && i == name.Length;
    }

    // Rebuilds an operand tree with every occurrence of `from` replaced by `to`.
    // Returns null when `from` does not occur, so callers only SetOperand on a hit.
    private static IOperand? ReplaceLocal(IOperand? operand, LocalVariable from, LocalVariable to)
    {
        switch (operand)
        {
            case null:
                return null;
            case LocalVariable local:
                return ReferenceEquals(local, from) ? to : null;
            case MemoryOperand memory:
            {
                var replacedBase = ReplaceLocal(memory.Base, from, to);
                var replacedIndex = ReplaceLocal(memory.Index, from, to);
                if (replacedBase == null && replacedIndex == null)
                    return null;
                memory.Base = replacedBase ?? memory.Base;
                memory.Index = replacedIndex ?? memory.Index;
                return memory;
            }
            case AddressOf address:
                return ReplaceLocal(address.Target, from, to) is { } target
                    ? new AddressOf(target)
                    : null;
            case ReferenceCast cast:
                return ReferenceEquals(cast.Value, from)
                    ? new ReferenceCast(to, cast.Type, cast.NullOnFailure)
                    : null;
            case FieldReference field:
                return ReferenceEquals(field.Local, from)
                    ? new FieldReference(field.Field, to, field.Offset, field.Containers,
                        field.AccessSize)
                    : null;
            case SelectedFieldReference selected:
            {
                var selector = ReferenceEquals(selected.Selector, from) ? to : null;
                if (selector == null && selected.Choices.All(choice =>
                        !ReferenceEquals(choice.Field.Local, from)))
                    return null;
                var choices = selected.Choices.Select(choice => ReferenceEquals(choice.Field.Local, from)
                        ? (choice.Value,
                            new FieldReference(choice.Field.Field, to, choice.Field.Offset,
                                choice.Field.Containers, choice.Field.AccessSize))
                        : choice)
                    .ToList();
                return new SelectedFieldReference(selector ?? selected.Selector, choices);
            }
            case ArrayAccess access:
            {
                var replacedIndex = ReplaceLocal(access.Index, from, to);
                if (!ReferenceEquals(access.Array, from) && replacedIndex == null)
                    return null;
                return new ArrayAccess(ReferenceEquals(access.Array, from) ? to : access.Array,
                    replacedIndex ?? access.Index);
            }
            case ArrayElementFieldReference elementField:
            {
                var replacedIndex = ReplaceLocal(elementField.Index, from, to);
                if (!ReferenceEquals(elementField.Array, from) && replacedIndex == null)
                    return null;
                return new ArrayElementFieldReference(
                    ReferenceEquals(elementField.Array, from) ? to : elementField.Array,
                    replacedIndex ?? elementField.Index, elementField.Field);
            }
            case ArrayLength length:
                return ReferenceEquals(length.Array, from) ? new ArrayLength(to) : null;
            default:
                return null;
        }
    }

    // A lifted register is a bag of bytes the lifter tracks as one whole, but each
    // scalar use of it only touches the low lane: `fneg s8, s0` reads 32 bits of v0
    // and `mov w8, w0` copies 32 bits of x0, never the whole vector register. Once
    // locals are typed, an operand position whose required stack kind is a scalar
    // (I4/I8/F/native-int) cannot honestly read a local whose type is a different
    // stack kind (a value-type aggregate). Split that use off the register's
    // whole-value local: the slot the operation sees is the aggregate's lane-0
    // field. The same applies to a scalar store into an aggregate-typed register:
    // `fmov s0, s8` defines the low lane alone, so the store's slot is that field.
    private static void SplitScalarOperandViews(MethodAnalysisContext method)
    {
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            switch (instruction.OpCode)
            {
                case OpCode.Move:
                    SplitMoveOperandViews(method, instruction);
                    break;
                case OpCode.Negate or OpCode.Not
                    or OpCode.Add or OpCode.Subtract or OpCode.Multiply
                    or OpCode.Divide or OpCode.Modulo
                    or OpCode.And or OpCode.Or or OpCode.Xor
                    or OpCode.ShiftLeft or OpCode.ShiftRight:
                    SplitScalarSources(method, instruction);
                    break;
                case OpCode.CheckEqual or OpCode.CheckNotEqual
                    or OpCode.CheckGreater or OpCode.CheckGreaterOrEqual
                    or OpCode.CheckLess or OpCode.CheckLessOrEqual:
                    SplitScalarComparisonSources(method, instruction);
                    break;
                case OpCode.Convert:
                    // A numeric conversion reads only the low lane of its source
                    // register: `fcvtzs x10, s0` reads `point.x`, `scvtf s0, w0`
                    // reads the low int. The lifter's recorded source width and
                    // floatness name the lane; anything wider stays whole.
                    if (instruction.ConversionSourceWidthBits is { } sourceBits
                        && ScalarLaneType(method, sourceBits,
                            instruction.ConversionFromFloat) is { } convertLane)
                        SplitScalarSources(method, instruction, convertLane);
                    break;
            }
        }
    }

    private static void SplitMoveOperandViews(MethodAnalysisContext method, Instruction instruction)
    {
        if (instruction.Operands.Count < 2)
            return;

        // A store through a scalar-typed field slot sees the same low-lane view
        // a scalar local does, so a register-view source splits to its lane-0
        // field here too.
        if (instruction.Operands[0] is FieldReference { Field.FieldType: { } fieldType } destinationField
            && IsScalarLaneType(fieldType))
        {
            // A lane split would let the emitter collapse the slot into a
            // member store on a by-ref parameter (`param.x` on `out Vector3
            // param`): a single proven lane is a legal write, but leaves the
            // parameter's sibling members unassigned - CS0177 where control
            // kept the unspellable-leaf diagnostic. Without per-lane
            // definite-assignment proof for the whole destination, the
            // destination keeps the diagnostic.
            if (!ReceiverIsByRefParameter(destinationField.Local, method))
                SplitScalarSources(method, instruction, fieldType);
            return;
        }

        if (instruction.Operands[0] is not LocalVariable destination)
            return;

        if (IsScalarLaneType(destination.Type))
        {
            SplitScalarSources(method, instruction);
            return;
        }

        // The destination is an aggregate while the source is a scalar: only the low
        // lane is being defined, so the slot written is that lane's field, emitted
        // as a field store on the local.
        if (destination.Type is { IsValueType: true } destinationType
            && instruction.Operands[1] is LocalVariable { Type: { } sourceType }
            && IsScalarLaneType(sourceType)
            && LaneZeroField(destinationType, sourceType) is { } lane)
            instruction.SetOperand(0, new FieldReference(lane, destination, 0));
    }

    private static void SplitScalarSources(MethodAnalysisContext method, Instruction instruction)
    {
        if (instruction.Operands[0] is not LocalVariable destination
            || !IsScalarLaneType(destination.Type))
            return;
        SplitScalarSources(method, instruction, destination.Type!);
    }

    // A `ref`/`out` parameter's local is byref-typed and sits in the parameter
    // list. Before copy coalescing, stores often spell it through a per-edge
    // alias local (`v25`) that every definition copies from the same source -
    // the shape ByrefAliasForwarding later rewrites to the parameter.
    private static bool ReceiverIsByRefParameter(LocalVariable local, MethodAnalysisContext method)
    {
        if (local.Type is not ByRefTypeAnalysisContext)
            return false;
        var seen = new HashSet<LocalVariable>();
        for (var current = local; seen.Add(current);)
        {
            if (method.ParameterLocals.Any(p => p.Register.Number == current.Register.Number))
                return true;
            if (UniformByrefAliasSource(current, method) is not { } source)
                return false;
            current = source;
        }
        return false;
    }

    // The single byref local every definition of `local` copies from, when all
    // of them are Move copies of the same source; null otherwise.
    private static LocalVariable? UniformByrefAliasSource(LocalVariable local, MethodAnalysisContext method)
    {
        LocalVariable? source = null;
        foreach (var instruction in method.ControlFlowGraph!.Instructions)
        {
            if (instruction.OpCode != OpCode.Move
                || instruction.Destination is not LocalVariable destination
                || !ReferenceEquals(destination, local))
                continue;
            if (instruction.Operands.Count < 2
                || instruction.Operands[1] is not LocalVariable operand
                || operand.Type is not ByRefTypeAnalysisContext
                || (source != null && !ReferenceEquals(source, operand)))
                return null;
            source = operand;
        }
        return source;
    }

    private static void SplitScalarSources(MethodAnalysisContext method, Instruction instruction, TypeAnalysisContext laneType)
    {
        for (var i = 1; i < instruction.Operands.Count; i++)
            if (LaneOperand(instruction.Operands[i], laneType, method) is { } lane)
                instruction.SetOperand(i, lane);
    }

    private static void SplitScalarComparisonSources(MethodAnalysisContext method, Instruction instruction)
    {
        // A comparison's operand pair shares one stack kind, which the flag-typed
        // destination does not reveal; take it from whichever side is already
        // scalar - a typed local, or the literal's own family. An integer
        // immediate names no lane: the whole-packed compare it sits in is the
        // packed-fields pass's to read.
        if (instruction.Operands.Count < 3)
            return;
        var left = instruction.Operands[1];
        var right = instruction.Operands[2];

        var laneType = left is LocalVariable { Type: { } leftType } && IsScalarLaneType(leftType) ? leftType
            : right is LocalVariable { Type: { } rightType } && IsScalarLaneType(rightType) ? rightType
            : ScalarLiteralLaneType(left, method) ?? ScalarLiteralLaneType(right, method);
        if (laneType == null)
            return;

        if (LaneOperand(right, laneType, method) is { } rightLane)
            instruction.SetOperand(2, rightLane);
        if (LaneOperand(left, laneType, method) is { } leftLane)
            instruction.SetOperand(1, leftLane);
    }

    // The stack type a scalar literal compares at: a float literal proves the
    // float lane, anything else proves nothing.
    private static TypeAnalysisContext? ScalarLiteralLaneType(IOperand operand,
        MethodAnalysisContext method)
        => operand switch
        {
            FloatLiteral => method.AppContext.SystemTypes.SystemSingleType,
            DoubleLiteral => method.AppContext.SystemTypes.SystemDoubleType,
            _ => null,
        };

    // The stack type a native read of `bits` of a register lane carries.
    private static TypeAnalysisContext? ScalarLaneType(MethodAnalysisContext method,
        int bits, bool isFloat)
        => bits switch
        {
            32 => isFloat ? method.AppContext.SystemTypes.SystemSingleType
                : method.AppContext.SystemTypes.SystemInt32Type,
            64 => isFloat ? method.AppContext.SystemTypes.SystemDoubleType
                : method.AppContext.SystemTypes.SystemInt64Type,
            _ => null,
        };

    private static IOperand? LaneOperand(IOperand operand, TypeAnalysisContext laneType,
        MethodAnalysisContext method)
    {
        // A scalar view of a 128-bit vector constant is its first element:
        // `fneg s1, s0` with `movi v0.4s, #x` reads lane S0 = X.
        if (operand is Vector128Literal literal)
            return new FloatLiteral(literal.X);

        // A scalar read of a resolved aggregate host (a struct field or a
        // register-view local) sees the host's lane-0 field: `ldr s0, [vec]`
        // reads `vec`'s first lane.
        if (operand is FieldReference { Field.FieldType: { } fieldType } fieldRef
            && fieldType.IsValueType && !IsScalarLaneType(fieldType)
            && LaneZeroField(fieldType, laneType) is { } nestedLane)
        {
            // A read on a receiver that can only spell as raw metadata (an
            // Il2CppClass/static-fields pointer or metadata handle)
            // defaults at the slot; projecting a lane off it would just move
            // the default onto the member, so the operand stays whole for the
            // emitter's referent-level fallback. A static member's receiver is
            // never consumed (ldsfld ignores it), so a metadata-internal holder
            // does not veto the lane split.
            if (!fieldRef.Field.IsStatic && !ManagedLaneReceiver(fieldRef))
                return null;
            // The aggregate becomes the innermost container of the nested
            // reference, so it is the hop the emission pass spells `ldflda`
            // on. For a compiler-generated backing field that hop only
            // survives when the decompiler-facing rewrite can reach the
            // getter (inside the accessor's own body it never can - the
            // rewrite would recurse); otherwise the scalar stays as the
            // whole-aggregate read its own diagnostic names.
            if (MetadataResolver.IsCompilerGeneratedBackingField(fieldRef.Field)
                && !MetadataResolver.BackingAccessorVisible(fieldRef.Field, method,
                    store: false))
                return null;
            return new FieldReference(nestedLane, fieldRef.Local, fieldRef.Offset,
                [.. fieldRef.Containers, fieldRef.Field], fieldRef.AccessSize);
        }

        if (operand is not LocalVariable { Type: { } aggregateType } local
            || !aggregateType.IsValueType || IsScalarLaneType(aggregateType)
            || LaneZeroField(aggregateType, laneType) is not { } lane
            || !LaneValueSpellable(local, method))
            return null;

        return new FieldReference(lane, local, 0);
    }

    // The lane read only spells when the host local does. A local whose
    // definitions all move in an operand the emitter cannot spell (a field
    // read on a metadata-internal receiver, a raw pointer expression, an
    // unmanaged load) defaults at the slot; splitting a store's source would
    // only move the default onto the member (`referent.lane = default(T).lane`),
    // so the whole operand is kept for the referent-level fallback control
    // emits. A non-Move definition spells the local directly and reads fine.
    private static bool LaneValueSpellable(LocalVariable local, MethodAnalysisContext method)
    {
        var seen = new HashSet<LocalVariable>();
        var work = new Stack<LocalVariable>();
        work.Push(local);
        while (work.Count > 0)
        {
            var current = work.Pop();
            if (!seen.Add(current))
                continue;
            foreach (var instruction in method.ControlFlowGraph!.Instructions)
            {
                if (!ReferenceEquals(instruction.Destination, current))
                    continue;
                // A call whose callee cannot be invoked assigns no managed
                // value - the lane would read a default where control keeps
                // the whole operand (and its own named diagnostic).
                if (instruction.OpCode is OpCode.Call or OpCode.IndirectCall
                    && VectorLanePacking.ResolveCallee(method.AppContext,
                        instruction.Operands[0]) is { } callee
                    && !IlGenerator.CalleeUsableFrom(callee, method))
                    return false;
                if (instruction.OpCode != OpCode.Move
                    || instruction.Operands.Count < 2)
                    continue;
                switch (instruction.Operands[1])
                {
                    case LocalVariable copy when ReferenceEquals(copy, current):
                        break;
                    case LocalVariable copy:
                        work.Push(copy);
                        break;
                    // A field read spells only when the member path itself can be
                    // named from this method. A static member emits ldsfld -
                    // its receiver is unused, so a metadata-internal holder (the
                    // Il2CppStaticFields block) does not veto it; an instance
                    // read still needs a managed receiver and a usable member.
                    case FieldReference field
                        when (field.Field.IsStatic || ManagedLaneReceiver(field))
                        && SpellableField(field, method):
                    // Loads materialize the local either as the resolved read or
                    // as their own named diagnostic; either way `local.lane`
                    // reads a real declared local.
                    case MemoryOperand or ArrayAccess or ArrayElementFieldReference
                        or ArrayLength or AddressOf or ReferenceCast
                        or SelectedFieldReference:
                    // Constants, callee/type operands and literals always emit a
                    // concrete value.
                    case Immediate or FloatLiteral or DoubleLiteral or StringLiteral
                        or TypeAnalysisContext or MethodAnalysisContext
                        or Vector128Literal:
                        break;
                    default:
                        return false;
                }
            }
        }
        return true;
    }

    // The emitter's own predicate, minus the emitted-token gate: analysis runs
    // before fields gain their AsmResolver definitions, so requiring the token
    // here would call every field unspellable.
    private static bool SpellableField(FieldReference field, MethodAnalysisContext method)
        => IlGenerator.FieldReferenceUsableFrom(field, method, requireToken: false);

    // A field read spells only when its receiver does. Reads through metadata
    // internals (the Il2CppClass/static-fields block or a runtime metadata
    // handle) and through raw pointers spell as IntPtr, which no member access
    // can name.
    private static bool ManagedLaneReceiver(FieldReference field)
        => field.Local?.Type is not (StaticFieldStorageTypeAnalysisContext
            or RuntimeClassTypeAnalysisContext
            or RuntimeMethodInfoAnalysisContext
            or RuntimeFieldInfoAnalysisContext
            or PointerTypeAnalysisContext);

    // A ldfld/stfld or instance-call receiver emits `&host` for a value-type
    // host (ldloca on a host-typed local) or a host-assignable reference
    // otherwise. `&` consumption needs the exact element type; a reference
    // receiver accepts any subtype.
    internal static bool ReceiverSatisfied(TypeAnalysisContext? producedType, TypeAnalysisContext? host)
    {
        if (host == null || producedType == null)
            return false;
        var carried = producedType is ByRefTypeAnalysisContext { ElementType: { } pointee }
            ? pointee
            : producedType;
        return host.IsValueType
            ? carried.FullName == host.FullName
              // `this` on a generic value type emits `&T<TArgs>` - the member's
              // declaring type is the open generic, which the instantiation's
              // own definition satisfies (B<int> is-a B).
              || carried is GenericInstanceTypeAnalysisContext { GenericType: { } definition }
                 && definition.FullName == host.FullName
            : carried.IsAssignableTo(host);
    }

    // The forward-gate view of the receiver contract: only a proven mismatch
    // blocks substitution. An untyped slot emits System.Object and an erased
    // generic parameter nothing concrete, so neither disproves the register
    // held the host - the copy keeps upstream's forwarding for those.
    internal static bool ReceiverProvenMismatched(TypeAnalysisContext? producedType,
        TypeAnalysisContext? host)
    {
        if (host == null || producedType == null)
            return false;
        var carried = producedType is ByRefTypeAnalysisContext { ElementType: { } pointee }
            ? pointee
            : producedType;
        if (carried.FullName == "System.Object" || carried is GenericParameterTypeAnalysisContext)
            return false;
        return !ReceiverSatisfied(producedType, host);
    }

    // Copy propagation (Simplifier, after SSA removal) forwards `Move`-copy
    // destinations to their source local inside operands, so the slot a local
    // ends up emitted through is its single-Move-definition source's slot, not
    // its own. Following that chain gives the type a receiver position will
    // actually carry.
    internal static TypeAnalysisContext? EmittedSlotLocalType(LocalVariable local,
        MethodAnalysisContext method)
    {
        // EmittedLocalType needs the application context; analysis-level callers
        // without one cannot disprove a receiver type.
        if (method.AppContext == null)
            return null;
        var visited = new HashSet<LocalVariable>();
        while (visited.Add(local))
        {
            var definitions = method.ControlFlowGraph!.Instructions
                .Where(instruction => ReferenceEquals(instruction.Destination, local)).ToList();
            if (definitions is not [{ OpCode: OpCode.Move, Operands: [_, { } source, ..] }])
                break;
            switch (source)
            {
                case LocalVariable sourceLocal:
                    local = sourceLocal;
                    continue;
                // A loaded field/selected-field value carries that value's type
                // regardless of a transient slot annotation on the local.
                case FieldReference fieldReference:
                    return fieldReference.Field.FieldType;
                case SelectedFieldReference selected:
                    return selected.FieldType;
                default:
                    goto done;
            }
        }
        done:
        return IlGenerator.EmittedLocalType(local, method);
    }

    // The type a FieldReference's receiver must supply: the owner of the first
    // container in a chained access (`v.a.b` needs `a`'s owner - the leaf field's
    // declaring type applies only to a flat reference).
    internal static TypeAnalysisContext? ReceiverHost(FieldReference field)
        => field.Containers is [{ } firstContainer, ..]
            ? firstContainer.DeclaringType
            : field.Field.DeclaringType;

    // A call operand's slot contract: a non-static call's `this` must emit the
    // callee's declaring type (`&T` for value types, an assignable reference
    // otherwise), and a byref parameter must emit exactly its element type -
    // `ref`/`out`/`in` slots are invariant. Concrete emitted types that break
    // the contract prove the forward wrong; untyped slots (uncomputable,
    // System.Object, generic parameter) are the unproven case copy propagation
    // is allowed to keep forwarding.
    internal static bool CallOperandProvenMismatched(Instruction instruction, int operandIndex,
        LocalVariable replacement, MethodAnalysisContext? method)
    {
        if (method == null
            || instruction.OpCode is not (OpCode.Call or OpCode.CallVoid)
            || instruction.Operands[0] is not MethodAnalysisContext callee)
            return false;
        var baseIndex = instruction.OpCode == OpCode.Call ? 2 : 1;
        if (!callee.IsStatic)
        {
            if (operandIndex == baseIndex)
                return ReceiverProvenMismatched(EmittedSlotLocalType(replacement, method),
                    callee.DeclaringType);
            baseIndex++;
        }
        var parameterIndex = operandIndex - baseIndex;
        if (parameterIndex < 0 || parameterIndex >= callee.Parameters.Count
            || callee.Parameters[parameterIndex].ParameterType
                is not ByRefTypeAnalysisContext { ElementType: { } element })
            return false;
        return ReceiverProvenMismatched(EmittedSlotLocalType(replacement, method), element);
    }

    // The low lane of an aggregate local is its publicly visible offset-0 field of
    // the scalar's exact type - `Vector3.x` for a Single view, a leading int for an
    // I4 view. A private or mismatched field is no lane the operand could honestly
    // name, so the operand stays whole and the emitter keeps its diagnostic.
    private static FieldAnalysisContext? LaneZeroField(TypeAnalysisContext aggregateType,
        TypeAnalysisContext laneType)
        => aggregateType.Fields.FirstOrDefault(field => !field.IsStatic
            && field.Offset == 0
            && field.Visibility == FieldAttributes.Public
            && (ReferenceEquals(field.FieldType, laneType) || field.FieldType.FullName == laneType.FullName));

    // The CLR stack kinds a scalar register lane can carry: a `w`/`s` lane-0 view
    // sees 4 bytes, a `d`/`x` view sees 8.
    private static bool IsScalarLaneType(TypeAnalysisContext? type)
        => type is { IsValueType: true } && type.FullName is "System.Int32" or "System.UInt32"
            or "System.Int64" or "System.UInt64" or "System.IntPtr" or "System.UIntPtr"
            or "System.Single" or "System.Double";
}
