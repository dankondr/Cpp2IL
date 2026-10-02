using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using Cpp2IL.Core.Extensions;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Logging;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

// Recovery cluster: an inlined member's member accesses (castle-recovery#217).
// The C++ compiler inlines small constructors, accessors and factories across
// assemblies; what remains is a field store (or read) the caller cannot legally
// express - `x.hiddenValue = v`, `awaiter.task = task`, `v60.zeroVector.x` -
// which emission has to drop as "Inaccessible field store". When the declaring
// type exposes an accessible member whose own lifted body is exactly that
// access, the access is that member called in place: the field set a group of
// stores covers matches a ctor's parameter-written fields, a setter's single
// write, a factory's produced value, or a getter's returned field.
internal static class InlinedMemberRecovery
{
    // What one slot in a member's produced field set traces back to.
    private abstract record ProducedSource;
    private sealed record ParamSource(int Index) : ProducedSource;
    private sealed record ThisSource : ProducedSource;
    private sealed record ThisFieldSource(FieldAnalysisContext Field) : ProducedSource;
    private sealed record ConstSource(object? Value) : ProducedSource;
    private sealed record UnknownSource : ProducedSource;

    private sealed class BodySummary
    {
        // Fields the member's lifted body writes on its produced object -
        // `this` for a .ctor / void member, the returned local for a producer.
        public readonly Dictionary<FieldKey, (FieldAnalysisContext Field, ProducedSource Source)> Stores = new();
        // `return <static field>` (get_zero-style) or `return this.F`.
        public FieldAnalysisContext? ReturnsStaticField;
        public FieldAnalysisContext? ReturnsInstanceField;
    }

    private readonly record struct FieldKey(string Name, string OwnerName)
    {
        public static FieldKey Of(FieldAnalysisContext field) =>
            new(field.Name, GenericDef(field.DeclaringType)?.FullName ?? "");

        public static TypeAnalysisContext? GenericDef(TypeAnalysisContext? type) =>
            type is GenericInstanceTypeAnalysisContext instance ? instance.GenericType : type;
    }

    // Match preference: a member writing exactly the stored fields beats a
    // produced value beats a constructor (which rewrites the whole object).
    private enum MemberKind { InstanceWriter, ReceiverBoundProducer, StaticProducer, Constructor }

    private sealed class Match
    {
        public required MethodAnalysisContext Member;
        public required MemberKind Kind;
        public IOperand? Receiver;
        public required List<IOperand> Args;
    }

    private sealed class SummaryResult
    {
        public BodySummary? Summary;
    }

    private static readonly ConcurrentDictionary<MethodAnalysisContext, SummaryResult> Summaries = new();

    // Members whose summary is mid-build on this thread: recursive asks through
    // an inner .ctor return nothing, so member cycles cannot recurse forever.
    [ThreadStatic]
    private static HashSet<MethodAnalysisContext>? s_summarizing;

    // What the pass-1 extraction of a member body captured, at the fixed
    // pipeline point where AnalyzeCore calls CaptureBodyFacts. Summaries are
    // built from these facts, never from the live block list, so a body read
    // mid-recovery cannot yield a different summary than one read later.
    internal sealed class BodyFacts
    {
        public LocalVariable? ThisLocal;
        public readonly Dictionary<LocalVariable, int> ParamIndex = new();
        public readonly Dictionary<LocalVariable, IOperand> Definitions = new();
        public readonly List<(FieldReference Destination, IOperand Source)> RawStores = new();
        public readonly List<(LocalVariable Receiver, List<IOperand> Args,
            MethodAnalysisContext Ctor)> CtorCalls = new();
        public readonly List<IOperand> Returns = new();
        public bool Rejected;
    }

    // Snapshot the body's summary inputs. AnalyzeCore calls this at a fixed
    // point for every method, suppressed (forced) or not, so fact content
    // cannot depend on which thread lifted the body.
    internal static void CaptureBodyFacts(MethodAnalysisContext body)
    {
        if (body.MemberBodyFacts != null || body.ControlFlowGraph == null)
            return;
        var facts = new BodyFacts
        {
            ThisLocal = body.ParameterLocals.FirstOrDefault(p => p.IsThis),
        };
        foreach (var (l, i) in body.ParameterLocals.Where(p => !p.IsThis && !p.IsMethodInfo)
                     .Select((l, i) => (l, i)))
            facts.ParamIndex[l] = i;

        foreach (var instruction in body.ControlFlowGraph.Blocks.SelectMany(b => b.Instructions))
        {
            switch (instruction.OpCode)
            {
                case OpCode.Nop or OpCode.Jump or OpCode.ShiftStack:
                    break;
                case OpCode.Return:
                    if (instruction.Operands.Count > 0)
                        facts.Returns.Add(instruction.Operands[0]);
                    break;
                case OpCode.Newobj when instruction.Operands is [LocalVariable allocated, ..]:
                    facts.Definitions[allocated] = allocated;
                    break;
                case OpCode.Move when instruction.Operands is [LocalVariable d, var s]:
                    facts.Definitions[d] = s;
                    break;
                case OpCode.Move when instruction.Operands is [FieldReference f, var s2]:
                    facts.RawStores.Add((f, s2));
                    break;
                case OpCode.CallVoid when instruction.Operands is
                    [MethodAnalysisContext { Name: ".ctor" }, ..]:
                case OpCode.Call when instruction.Operands is
                    [MethodAnalysisContext { Name: ".ctor" }, ..]:
                {
                    var target = (MethodAnalysisContext)instruction.Operands[0];
                    var receiverIndex = instruction.OpCode == OpCode.CallVoid ? 1 : 2;
                    var args = instruction.Operands.Skip(receiverIndex + 1).ToList();
                    if (Unwrap(instruction.Operands[receiverIndex]) is LocalVariable receiver)
                        facts.CtorCalls.Add((receiver, args, target));
                    else
                        facts.Rejected = true;
                    break;
                }
                default:
                    facts.Rejected = true;
                    break;
            }
        }
        body.MemberBodyFacts = facts;
    }

    public static int Run(MethodAnalysisContext method)
    {
        if (method.ControlFlowGraph == null)
            return 0;

        var rewrites = 0;
        for (var round = 0; round < 16; round++)
        {
            var progress = false;
            foreach (var block in method.ControlFlowGraph.Blocks)
            {
                // Member lookups analyze candidate bodies: a member that cannot
                // be proven costs its access a rewrite, never the method itself.
                try
                {
                    progress |= RewriteReads(block, method);
                    progress |= RewriteStores(block, method);
                }
                catch (Exception e) when (e is not OutOfMemoryException)
                {
                    method.AddWarning($"Inlined member recovery skipped a block: {e.Message}");
                }
            }
            if (!progress)
                break;
            rewrites++;
        }
        return rewrites;
    }

    // ------------------------------------------------------------------ reads

    private static bool RewriteReads(Block block, MethodAnalysisContext context)
    {
        var changed = false;
        var cached = new Dictionary<string, LocalVariable>();

        for (var index = 0; index < block.Instructions.Count; index++)
        {
            var instruction = block.Instructions[index];
            for (var i = 0; i < instruction.Operands.Count; i++)
            {
                // A Move's destination is a store - the store logic owns it.
                if (instruction.OpCode == OpCode.Move && i == 0)
                    continue;
                if (instruction.Operands[i] is not FieldReference field)
                    continue;

                TypeAnalysisContext? holderType;
                FieldAnalysisContext readOf;
                IReadOnlyList<FieldAnalysisContext> suffix;
                IOperand? receiverOperand;

                if (field.Local.Type is StaticFieldStorageTypeAnalysisContext storage)
                {
                    // [statics.sf..]: the first link is the static member on the
                    // real owner; the getter body's `return sf` names the same one.
                    holderType = storage.OwnerType;
                    if (field.Containers.Count == 0)
                    {
                        readOf = field.Field;
                        suffix = [];
                    }
                    else
                    {
                        readOf = field.Containers[0];
                        suffix = field.Containers.Skip(1).Append(field.Field).ToList();
                    }
                    // Only a static the caller cannot name was reached through an
                    // inlined accessor; a nameable one is read as it stands.
                    if (IlGenerator.FieldUsableFrom(readOf, context, requireToken: false))
                        continue;
                    receiverOperand = null;
                }
                else
                {
                    // The first link the caller cannot name becomes the accessor
                    // call; everything before it is that accessor's receiver.
                    var links = field.Containers.Append(field.Field).ToList();
                    var bad = links.FindIndex(c =>
                        !IlGenerator.FieldUsableFrom(c, context, requireToken: false));
                    if (bad < 0)
                        continue;
                    readOf = links[bad];
                    suffix = links.Skip(bad + 1).ToList();
                    if (bad == 0)
                        receiverOperand = field.Local;
                    else
                    {
                        receiverOperand = new FieldReference(field.Containers[bad - 1], field.Local,
                            field.Offset, field.Containers.Take(bad - 1).ToList());
                        if (!IlGenerator.FieldReferenceUsableFrom((FieldReference)receiverOperand,
                                context, requireToken: false))
                            continue;
                    }
                    holderType = readOf.DeclaringType;
                }

                if (holderType == null)
                    continue;

                // A read through a `T&` slot dereferences it: the accessor
                // receiver would be `ldloc` on the slot, which emission
                // cannot spell - the read stays diagnosed.
                if (receiverOperand != null && IsAddressSlot(receiverOperand, context))
                    continue;

                var getter = FindReturnedFieldAccessor(holderType, readOf, context,
                    staticAccess: receiverOperand == null);
                // A method is never its own inlined accessor: that rewrite is a
                // self-call. Instantiations share a definition, so compare that.
                if (getter == null
                    || receiverOperand == null && DefinitionOf(getter) == DefinitionOf(context))
                    continue;

                // The full name carries the holder and its instantiation:
                // `Vector2.get_zero` and `Vector3.get_zero`, or `Gen<int>.Get`
                // and `Gen<string>.Get`, never share a result.
                var key = $"{getter.FullName}|{receiverOperand}";
                if (!cached.TryGetValue(key, out var produced))
                {
                    produced = FreshLocal(context, $"inl_{block.ID}_{index}_{i}",
                        getter.ReturnType ?? readOf.FieldType);
                    List<IOperand> operands = [getter, produced];
                    if (receiverOperand != null)
                    {
                        var receiver = ReceiverOperand(receiverOperand, getter.DeclaringType);
                        if (receiver == null)
                            continue;
                        operands.Add(receiver);
                    }
                    block.Instructions.Insert(index, new Instruction(-1, OpCode.Call, operands));
                    index++;
                    cached[key] = produced;
                }

                instruction.SetOperand(i, suffix.Count == 0
                    ? produced
                    : new FieldReference(field.Field, produced, field.Offset,
                        suffix.Count > 1 ? suffix.Take(suffix.Count - 1).ToList() : [],
                        field.AccessSize));
                changed = true;
            }
        }
        return changed;
    }

    // The unique accessible member of the holder whose body is `return <field>` -
    // a getter over a private instance field, or `get_zero`-style over a static.
    private static MethodAnalysisContext? FindReturnedFieldAccessor(TypeAnalysisContext holderType,
        FieldAnalysisContext readOf, MethodAnalysisContext context, bool staticAccess)
    {
        MethodAnalysisContext? found = null;
        foreach (var candidate in MembersOn(holderType))
        {
            if (candidate.Parameters.Count != 0 || candidate.IsStatic != staticAccess)
                continue;
            if (!IlGenerator.CalleeUsableFrom(candidate, context))
                continue;
            var summary = Summarize(candidate, context);
            var returned = staticAccess ? summary?.ReturnsStaticField : summary?.ReturnsInstanceField;
            if (returned == null || !SameField(returned, readOf))
                continue;
            if (found != null)
                return null; // ambiguous
            found = candidate;
        }
        return found;
    }

    // ----------------------------------------------------------------- stores

    private static bool RewriteStores(Block block, MethodAnalysisContext context)
    {
        var instructions = block.Instructions;
        var changed = false;

        for (var i = 0; i < instructions.Count; i++)
        {
            if (instructions[i].OpCode != OpCode.Move
                || instructions[i].Operands is not [FieldReference first, ..]
                || IlGenerator.FieldReferenceUsableFrom(first, context, writeAccess: true,
                    requireToken: false))
                continue;

            // The group is the run of stores into the same accessed object -
            // the same local reached through the same container path. Stores
            // through a different path (`sm.u.m_task` vs `sm.state`) name a
            // different object and must not join this one.
            var group = new List<(Instruction Instruction, FieldReference Destination)>();
            var j = i;
            while (j < instructions.Count)
            {
                var current = instructions[j];
                if (current.OpCode == OpCode.Nop)
                {
                    j++;
                    continue;
                }
                if (current.OpCode != OpCode.Move
                    || current.Operands is not [FieldReference next, ..]
                    || !ReferenceEquals(next.Local, first.Local)
                    || !SamePath(next.Containers, first.Containers))
                    break;
                group.Add((current, next));
                j++;
            }

            var prefix = (IReadOnlyList<FieldAnalysisContext>)first.Containers;
            if (TryRewriteGroup(block, group, prefix, context))
                changed = true;
            i++;
        }
        return changed;
    }

    // Emission cannot push a `T&`-typed slot as a `&T` receiver or write a
    // whole struct through it with `Move`: `ldloc` on the slot is never
    // generated, so any replacement that would need one must stay diagnosed.
    // The same holds for address slots - locals the native code uses as raw
    // pointers (MemoryOperand stores, `T*` types). Writing a struct value to
    // one binds the emitted local's type to the struct and breaks every
    // pointer-shaped use of it (conv/cpblk), so the access stays diagnosed.
    private static bool IsAddressSlot(IOperand operand, MethodAnalysisContext context)
    {
        var local = operand switch
        {
            LocalVariable l => l,
            FieldReference f => f.Local,
            _ => null,
        };
        if (local == null)
            return false;
        if (local.Type is ByRefTypeAnalysisContext or PointerTypeAnalysisContext)
            return true;
        if (operand is FieldReference reference
            && (reference.Field.FieldType is ByRefTypeAnalysisContext
                || reference.Containers.Any(c => c.FieldType is ByRefTypeAnalysisContext)))
            return true;
        return context.ControlFlowGraph?.Instructions.Any(instruction =>
            instruction.Operands.Any(o => MemoryOperandUses(o, local))
            || (instruction.OpCode is OpCode.MemorySet or OpCode.MemoryCopy or OpCode.MemoryMove
                && instruction.Operands.Count > 0
                && OperandIsLocal(instruction.Operands[0], local))
            || (instruction.OpCode is OpCode.Call or OpCode.CallVoid
                && instruction.Operands[0] is not MethodAnalysisContext
                && instruction.Operands.Skip(1).Any(o => OperandIsLocal(o, local)))) == true;
    }

    private static bool MemoryOperandUses(IOperand operand, LocalVariable local) =>
        operand is MemoryOperand memory
            && (OperandIsLocal(memory.Base, local) || OperandIsLocal(memory.Index, local));

    private static bool OperandIsLocal(IOperand? operand, LocalVariable local) => operand switch
    {
        LocalVariable l => ReferenceEquals(l, local),
        FieldReference f => ReferenceEquals(f.Local, local),
        AddressOf a => OperandIsLocal(a.Target, local),
        _ => false,
    };

    private static bool SamePath(IReadOnlyList<FieldAnalysisContext> a,
        IReadOnlyList<FieldAnalysisContext> b) =>
        a.Count == b.Count && a.Zip(b).All(pair => ReferenceEquals(pair.First, pair.Second));

    private static bool TryRewriteGroup(Block block,
        List<(Instruction Instruction, FieldReference Destination)> group,
        IReadOnlyList<FieldAnalysisContext> prefix, MethodAnalysisContext context)
    {
        var local = group[0].Destination.Local;
        var accessedType = prefix.Count == 0
            ? local.Type is StaticFieldStorageTypeAnalysisContext storage
                ? storage.OwnerType
                : local.Type
            : prefix[^1].FieldType;
        // A store through a return buffer or a byref local writes the
        // element type's fields.
        while (accessedType is WrappedTypeAnalysisContext wrapped)
            accessedType = wrapped.ElementType;
        if (accessedType == null)
            return false;
        var leafType = FieldKey.GenericDef(accessedType) ?? accessedType;

        // Dead stores: a covering ctor call on the same object directly after
        // the run overwrites every field the run set (pre-ctor zero fills).
        if (TryDeadStoresBeforeCtor(block, group, prefix, context))
            return true;

        // Every store zero, transitively covering the accessed type's fields.
        if (group.All(g => IsZero(g.Instruction.Operands[1]))
            && CoversAllFields(leafType, group.Select(g => g.Destination).ToList(), prefix))
        {
            var destination = PrefixOperand(local, prefix, group[0].Destination);
            if (!IsAddressSlot(destination, context)
                && (destination is not FieldReference collapsed
                    || IlGenerator.FieldReferenceUsableFrom(collapsed, context,
                        writeAccess: true, requireToken: false)))
            {
                EmitReplacement(block, group,
                    new Instruction(-1, OpCode.Move, destination, new Immediate(0)));
                return true;
            }
        }

        // Lane copy: every leaf field stored once, each from the same lane of
        // the same base operand - `x._dateData = e._dateData` collapses to `x = e`.
        if (TryLaneCopy(block, group, prefix, accessedType, context))
            return true;

        // Member match: the unique accessible member of the accessed type (or
        // of a stored operand's type) whose produced field set is exactly the
        // group's leaf set.
        return TryMemberMatch(block, group, prefix, accessedType, leafType, context);
    }

    private static bool TryDeadStoresBeforeCtor(Block block,
        List<(Instruction Instruction, FieldReference Destination)> group,
        IReadOnlyList<FieldAnalysisContext> prefix, MethodAnalysisContext context)
    {
        var index = block.Instructions.IndexOf(group[^1].Instruction) + 1;
        while (index < block.Instructions.Count && block.Instructions[index].OpCode == OpCode.Nop)
            index++;
        if (index >= block.Instructions.Count
            || block.Instructions[index].OpCode != OpCode.CallVoid
            || block.Instructions[index].Operands is not [MethodAnalysisContext ctor, ..]
            || ctor.Name != ".ctor")
            return false;

        var local = group[0].Destination.Local;
        var receiver = block.Instructions[index].Operands.Count > 1
            ? block.Instructions[index].Operands[1] : null;
        var onThisObject = receiver switch
        {
            LocalVariable l => prefix.Count == 0 && ReferenceEquals(l, local),
            AddressOf { Target: LocalVariable l } => prefix.Count == 0 && ReferenceEquals(l, local),
            FieldReference f => prefix.Count > 0 && ReferenceEquals(f.Local, local)
                && SameField(f.Field, prefix[^1])
                && f.Containers.SequenceEqual(prefix.SkipLast(1)),
            AddressOf { Target: FieldReference f } => prefix.Count > 0
                && ReferenceEquals(f.Local, local)
                && SameField(f.Field, prefix[^1])
                && f.Containers.SequenceEqual(prefix.SkipLast(1)),
            _ => false,
        };
        if (!onThisObject)
            return false;

        var summary = Summarize(ctor, context);
        if (summary == null)
            return false;

        var dead = group.Where(g => summary.Stores.ContainsKey(PrefixLevelKey(g.Destination, prefix)))
            .Select(g => g.Instruction).ToList();
        if (dead.Count == 0)
            return false;
        foreach (var instruction in dead)
            NopOut(instruction);
        return true;
    }

    private static FieldKey PrefixLevelKey(FieldReference destination,
        IReadOnlyList<FieldAnalysisContext> prefix) =>
        FieldKey.Of(destination.Containers.Count > prefix.Count
            ? destination.Containers[prefix.Count]
            : destination.Field);

    private static bool CoversAllFields(TypeAnalysisContext type,
        IReadOnlyList<FieldReference> destinations,
        IReadOnlyList<FieldAnalysisContext> prefix)
    {
        foreach (var field in type.Fields.Where(f => !f.IsStatic))
        {
            if (destinations.Any(d => d.Containers.Count == prefix.Count
                    && SameField(d.Field, field)))
                continue;
            var deeper = prefix.Append(field).ToList();
            if (!field.FieldType.IsValueType
                || !destinations.Any(d => Prefixes(d.Containers, deeper))
                || !CoversAllFields(FieldKey.GenericDef(field.FieldType) ?? field.FieldType,
                    destinations, deeper))
                return false;
        }
        return true;
    }

    private static bool Prefixes(IReadOnlyList<FieldAnalysisContext> containers,
        IReadOnlyList<FieldAnalysisContext> prefix) =>
        containers.Count >= prefix.Count
        && containers.Take(prefix.Count).Zip(prefix).All(pair => ReferenceEquals(pair.First, pair.Second));

    private static bool TryLaneCopy(Block block,
        List<(Instruction Instruction, FieldReference Destination)> group,
        IReadOnlyList<FieldAnalysisContext> prefix,
        TypeAnalysisContext accessedType, MethodAnalysisContext context)
    {
        if (group.Any(g => g.Instruction.Operands[1] is not FieldReference))
            return false;
        var sources = group.Select(g => (FieldReference)g.Instruction.Operands[1]).ToList();
        var baseLocal = sources[0].Local;
        var baseContainers = sources[0].Containers;
        if (sources.Any(s => !ReferenceEquals(s.Local, baseLocal)
                || !s.Containers.SequenceEqual(baseContainers)))
            return false;

        // Every leaf field of the accessed type, copied once from the same lane.
        var instanceFields = accessedType.Fields.Where(f => !f.IsStatic).ToList();
        if (instanceFields.Count == 0 || group.Count != instanceFields.Count)
            return false;
        foreach (var field in instanceFields)
        {
            var index = group.FindIndex(g => g.Destination.Containers.Count == prefix.Count
                && SameField(g.Destination.Field, field));
            if (index < 0 || !SameField(sources[index].Field, field))
                return false;
        }

        var sourceOperand = baseContainers.Count == 0
            ? (IOperand)baseLocal
            : new FieldReference(baseContainers[^1], baseLocal, group[0].Destination.Offset,
                baseContainers.Take(baseContainers.Count - 1).ToList());
        if (sourceOperand is FieldReference sourceField
            && !IlGenerator.FieldReferenceUsableFrom(sourceField, context, requireToken: false))
            return false;

        var destination = PrefixOperand(group[0].Destination.Local, prefix, group[0].Destination);
        if (IsAddressSlot(destination, context)
            || (destination is FieldReference destinationField
                && !IlGenerator.FieldReferenceUsableFrom(destinationField, context,
                    writeAccess: true, requireToken: false)))
            return false;

        EmitReplacement(block, group, new Instruction(-1, OpCode.Move, destination, sourceOperand));
        return true;
    }

    private static bool TryMemberMatch(Block block,
        List<(Instruction Instruction, FieldReference Destination)> group,
        IReadOnlyList<FieldAnalysisContext> prefix,
        TypeAnalysisContext accessedType, TypeAnalysisContext leafType,
        MethodAnalysisContext context)
    {
        var leaves = new Dictionary<FieldKey, (FieldAnalysisContext Field, IOperand Source,
            Instruction Instruction)>();
        foreach (var (instruction, destination) in group)
            leaves[FieldKey.Of(destination.Field)] =
                (destination.Field, instruction.Operands[1], instruction);
        if (leaves.Count == 0)
            return false;

        var local = group[0].Destination.Local;
        var receiverBase = PrefixOperand(local, prefix, group[0].Destination);
        // A store through a `T&` slot is a dereference: a member call would
        // need `ldloc` on the slot as the `&T` receiver, which emission
        // cannot spell (it fabricates `ldloca` of a fresh local instead).
        // The access stays diagnosed rather than emitting a wrong call.
        if (IsAddressSlot(receiverBase, context))
            return false;

        // One member covering the whole store set - the inlined constructor
        // or compound accessor.
        if (MatchLeaves(leaves, accessedType, prefix, local, leafType, context) is { } whole)
        {
            var insertions = new List<Instruction>();
            if (AppendMatchEmit(insertions, whole, receiverBase, receiverBase,
                    prefix.Count == 0, accessedType, block, context))
            {
                EmitReplacement(block, group, insertions.ToArray());
                return true;
            }
        }

        // Each store is its own access: `rect.x = a; rect.y = b` is set_x
        // plus set_y. A store with no unique member keeps its diagnostic.
        if (leaves.Count < 2)
            return false;
        var perLeaf = new List<Instruction>();
        var covered = new List<Instruction>();
        foreach (var leaf in leaves)
        {
            var single = new Dictionary<FieldKey, (FieldAnalysisContext Field, IOperand Source,
                Instruction Instruction)> { [leaf.Key] = leaf.Value };
            var at2 = perLeaf.Count;
            if (MatchLeaves(single, accessedType, prefix, local, leafType, context) is not { } match
                || !AppendMatchEmit(perLeaf, match, receiverBase,
                    leaf.Value.Instruction.Operands[0], false,
                    leaf.Value.Field.FieldType ?? accessedType, block, context))
            {
                perLeaf.RemoveRange(at2, perLeaf.Count - at2);
                continue;
            }
            covered.Add(leaf.Value.Instruction);
        }
        if (covered.Count == 0)
            return false;
        var at = block.Instructions.IndexOf(group[0].Instruction);
        if (at < 0)
            return false;
        block.Instructions.InsertRange(at, perLeaf);
        foreach (var instruction in covered)
            NopOut(instruction);
        return true;
    }

    // Returns the unique best member whose lifted body is exactly the store
    // set, or null when none binds or the best is ambiguous.
    private static Match? MatchLeaves(
        Dictionary<FieldKey, (FieldAnalysisContext Field, IOperand Source, Instruction Instruction)> leaves,
        TypeAnalysisContext accessedType, IReadOnlyList<FieldAnalysisContext> prefix,
        LocalVariable local, TypeAnalysisContext leafType, MethodAnalysisContext context)
    {
        var wanted = leaves.ToDictionary(p => p.Key, p => (p.Value.Field, p.Value.Source));
        var candidates = new List<Match>();
        // A method is never its own inlined member: a factory that builds its result in place
        // matches its own stores, and that rewrite is a self-call.
        foreach (var member in MembersOn(accessedType))
            if (DefinitionOf(member) != DefinitionOf(context)
                && TryBind(member, wanted, prefix, local, leafType, context) is { } bound)
                candidates.Add(bound);

        // Factories: a member on a stored operand's own type returning the
        // accessed type - `task.GetAwaiter()`. Only the single-store shape can
        // name the operand unambiguously.
        if (wanted.Count == 1)
        {
            var sourceType = OperandObjectType(wanted.Values.First().Source);
            if (sourceType != null)
                foreach (var member in MembersOn(sourceType))
                    if (!member.IsStatic && DefinitionOf(member) != DefinitionOf(context)
                        && TryBind(member, wanted, prefix, local, leafType, context) is { } bound)
                        candidates.Add(bound);
        }

        if (candidates.Count == 0)
        {
            Logger.VerboseNewline(
                $"Inlined member recovery: {context.Name}: no member of {accessedType.FullName} covers [{string.Join(",", wanted.Keys.Select(k => k.Name))}]",
                "Analysis");
            return null;
        }
        if (candidates.Count > 1)
            Logger.VerboseNewline(
                $"Inlined member recovery: {context.Name}: {candidates.Count} member matches for {accessedType.FullName}",
                "Analysis");
        var best = candidates.GroupBy(m => m.Kind).MinBy(g => g.Key)!;
        return best.Count() == 1 ? best.First() : null;
    }

    // Emit the call replacing a match. `receiverBase` is the accessed object
    // (`bounds` for `bounds.m_XMin`); `destination` is the slot that keeps a
    // produced value (the accessed object for a whole-set match, the leaf
    // field for a per-leaf match). `bareObject` is true when the accessed
    // object is the local itself, so a constructor runs on it directly.
    private static bool AppendMatchEmit(List<Instruction> insertions, Match match,
        IOperand receiverBase, IOperand destination, bool bareObject,
        TypeAnalysisContext accessedType, Block block, MethodAnalysisContext context)
    {
        switch (match.Kind)
        {
            case MemberKind.InstanceWriter:
            {
                var receiver = ReceiverOperand(match.Receiver ?? receiverBase,
                    match.Member.DeclaringType);
                if (receiver == null)
                    return false;
                insertions.Add(new Instruction(-1, OpCode.CallVoid,
                    [match.Member, receiver, ..match.Args]));
                return true;
            }
            case MemberKind.Constructor when bareObject && accessedType.IsValueType
                && receiverBase is LocalVariable:
                insertions.Add(new Instruction(-1, OpCode.CallVoid,
                    [match.Member, receiverBase, ..match.Args]));
                return true;
            case MemberKind.Constructor:
            {
                var produced = FreshLocal(context, $"inl_ctor_{block.ID}_{insertions.Count}",
                    accessedType);
                if (!accessedType.IsValueType)
                    insertions.Add(new Instruction(-1, OpCode.Newobj, produced, accessedType));
                insertions.Add(new Instruction(-1, OpCode.CallVoid,
                    [match.Member, produced, ..match.Args]));
                return AppendStore(insertions, destination, produced, context);
            }
            default: // produced value into the slot - factories and statics
            {
                var produced = FreshLocal(context, $"inl_prod_{block.ID}_{insertions.Count}",
                    match.Member.ReturnType ?? accessedType);
                List<IOperand> call = [match.Member, produced];
                if (match.Receiver != null)
                {
                    var receiver = ReceiverOperand(match.Receiver, match.Member.DeclaringType);
                    if (receiver == null)
                        return false;
                    call.Add(receiver);
                }
                call.AddRange(match.Args);
                insertions.Add(new Instruction(-1, OpCode.Call, call));
                return AppendStore(insertions, destination, produced, context);
            }
        }
    }

    private static bool AppendStore(List<Instruction> insertions, IOperand destination,
        IOperand value, MethodAnalysisContext context)
    {
        if (IsAddressSlot(destination, context))
            return false;
        if (destination is FieldReference destinationField
            && !IlGenerator.FieldReferenceUsableFrom(destinationField, context,
                writeAccess: true, requireToken: false))
            return false;
        insertions.Add(new Instruction(-1, OpCode.Move, destination, value));
        return true;
    }

    private static Match? TryBind(MethodAnalysisContext member,
        Dictionary<FieldKey, (FieldAnalysisContext Field, IOperand Source)> leaves,
        IReadOnlyList<FieldAnalysisContext> prefix, LocalVariable local,
        TypeAnalysisContext leafType, MethodAnalysisContext context)
    {
        if (member.Name == ".cctor")
            return null;
        var isCtor = member.Name == ".ctor" && !member.IsStatic
            && SameDef(member.DeclaringType, leafType);
        var returnsLeaf = member.ReturnType != null
            && SameDef(member.ReturnType, leafType);
        var declaresOnLeaf = SameDef(member.DeclaringType, leafType);
        var isVoid = member.ReturnType == null || member.ReturnType.FullName is "System.Void";
        var instanceWriter = !member.IsStatic && !isCtor && declaresOnLeaf && isVoid;
        var factory = !member.IsStatic && !isCtor && !declaresOnLeaf && returnsLeaf;
        var staticProducer = member.IsStatic && returnsLeaf;
        if (!isCtor && !instanceWriter && !factory && !staticProducer)
            return null;
        if (!IlGenerator.CalleeUsableFrom(member, context))
            return null;

        var summary = Summarize(member, context);
        if (summary == null)
        {
            DiagnoseReject(context, member, "no usable body");
            return null;
        }
        if (summary.Stores.Count != leaves.Count
            || !leaves.Keys.All(summary.Stores.ContainsKey))
        {
            DiagnoseReject(context, member,
                $"produces [{string.Join(",", summary.Stores.Keys.Select(k => k.Name))}], wanted [{string.Join(",", leaves.Keys.Select(k => k.Name))}]");
            return null;
        }

        var args = new IOperand?[member.Parameters.Count];
        IOperand? receiver = null;
        foreach (var (key, produced) in summary.Stores)
        {
            var callerOperand = leaves[key].Source;
            switch (produced.Source)
            {
                case ParamSource param:
                    if (param.Index >= args.Length || args[param.Index] != null
                        || !ImmediateCompatible(member.Parameters[param.Index].ParameterType,
                            callerOperand))
                        return null;
                    args[param.Index] = callerOperand;
                    break;
                case ThisSource:
                    if (receiver != null)
                        return null;
                    receiver = callerOperand;
                    break;
                case ThisFieldSource thisField:
                {
                    if (receiver != null || callerOperand is not FieldReference sourceField
                        || !SameField(sourceField.Field, thisField.Field))
                        return null;
                    receiver = sourceField.Containers.Count == 0
                        ? sourceField.Local
                        : new FieldReference(sourceField.Containers[^1], sourceField.Local,
                            sourceField.Offset,
                            sourceField.Containers.Take(sourceField.Containers.Count - 1).ToList());
                    break;
                }
                case ConstSource constant:
                    if (!ConstEquals(callerOperand, constant.Value))
                        return null;
                    break;
                case UnknownSource:
                    return null;
            }
        }
        if (args.Any(a => a == null))
            return null;

        var kind = isCtor ? MemberKind.Constructor
            : instanceWriter ? MemberKind.InstanceWriter
            : factory ? MemberKind.ReceiverBoundProducer
            : MemberKind.StaticProducer;
        if (kind == MemberKind.ReceiverBoundProducer && receiver == null)
            return null;
        if (kind == MemberKind.InstanceWriter && receiver == null)
            receiver = PrefixOperand(local, prefix, null);

        return new Match { Member = member, Kind = kind, Receiver = receiver,
            Args = args.Select(a => a!).ToList() };
    }

    private static bool SameDef(TypeAnalysisContext? a, TypeAnalysisContext? b) =>
        FieldKey.GenericDef(a)?.FullName == FieldKey.GenericDef(b)?.FullName;

    // --------------------------------------------------------------- operands

    private static IOperand PrefixOperand(LocalVariable local,
        IReadOnlyList<FieldAnalysisContext> prefix, FieldReference? sample) =>
        prefix.Count == 0
            ? local
            : new FieldReference(prefix[^1], local, sample?.Offset ?? 0,
                prefix.Count > 1 ? prefix.Take(prefix.Count - 1).ToList() : []);

    private static IOperand? ReceiverOperand(IOperand operand, TypeAnalysisContext? declaringType) =>
        operand switch
        {
            LocalVariable l => declaringType is { IsValueType: true }
                && l.Type is not ByRefTypeAnalysisContext ? new AddressOf(l) : l,
            FieldReference f => declaringType is { IsValueType: true }
                && f.Field.FieldType is not ByRefTypeAnalysisContext ? new AddressOf(f) : f,
            _ => null,
        };

    private static TypeAnalysisContext? OperandObjectType(IOperand operand) =>
        operand switch
        {
            LocalVariable local => local.Type,
            FieldReference field => field.Field.FieldType,
            ReferenceCast cast => OperandObjectType(cast.Value),
            AddressOf address => OperandObjectType(address.Target),
            _ => null,
        };

    private static void DiagnoseReject(MethodAnalysisContext context,
        MethodAnalysisContext member, string reason)
    {
        if (member.IsStatic)
            return;
        Logger.VerboseNewline($"Inlined member recovery: {context.Name}: {member.FullName} - {reason}",
            "Analysis");
    }

    private static bool IsZero(IOperand operand) =>
        operand is Immediate { Value: 0 } or FloatLiteral { Value: 0f } or DoubleLiteral { Value: 0d };

    // A literal only flows into a parameter slot when the slot is numeric or
    // boolean - `new ObscuredInt(0)`, not `new Rect(0)` - or when it is the
    // null literal into a reference slot.
    private static bool ImmediateCompatible(TypeAnalysisContext? parameterType, IOperand operand)
    {
        if (operand is not (Immediate or FloatLiteral or DoubleLiteral))
        {
            // A bound operand lands in the member's parameter slot verbatim:
            // it must already be of the slot's type family, not just not a
            // literal. `OperandObjectType` follows casts and `&` targets.
            var sourceType = OperandObjectType(operand);
            if (parameterType == null || sourceType == null)
                return true;
            return SameDef(sourceType, parameterType)
                || sourceType.IsAssignableTo(parameterType)
                || sourceType.IsValueType && parameterType.IsValueType
                    && sourceType.Type == parameterType.Type;
        }
        return (operand is Immediate { Value: 0 } && parameterType?.IsValueType == false)
        || parameterType?.Type is LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_I1
            or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_U1
            or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_I2
            or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_U2
            or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_I4
            or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_U4
            or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_I8
            or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_U8
            or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_R4
            or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_R8
            or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_BOOLEAN
            or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_CHAR
            or LibCpp2IL.BinaryStructures.Il2CppTypeEnum.IL2CPP_TYPE_ENUM;
    }

    private static bool ConstEquals(IOperand operand, object? value) =>
        (operand, value) switch
        {
            (Immediate i, long l) => i.Value == l,
            (Immediate i, bool b) => i.Value == (b ? 1 : 0),
            (FloatLiteral f, float f2) => f.Value == f2,
            (DoubleLiteral d, double d2) => d.Value == d2,
            _ => false,
        };

    private static bool SameField(FieldAnalysisContext a, FieldAnalysisContext b) =>
        FieldKey.Of(a) == FieldKey.Of(b);

    private static object DefinitionOf(MethodAnalysisContext method)
    {
        var open = (method as ConcreteGenericMethodAnalysisContext)?.BaseMethodContext ?? method;
        return (object?)open.Definition ?? open;
    }

    private static LocalVariable FreshLocal(MethodAnalysisContext method, string name,
        TypeAnalysisContext? type)
    {
        var local = new LocalVariable(name, new Register(null, name), type);
        method.Locals.Add(local);
        return local;
    }

    private static void NopOut(Instruction instruction)
    {
        instruction.OpCode = OpCode.Nop;
        instruction.SetOperands();
    }

    private static void EmitReplacement(Block block,
        List<(Instruction Instruction, FieldReference Destination)> group,
        params Instruction[] replacement)
    {
        var index = block.Instructions.IndexOf(group[0].Instruction);
        if (index < 0)
            return;
        block.Instructions.InsertRange(index, replacement);
        foreach (var (instruction, _) in group)
            NopOut(instruction);
    }

    private static IEnumerable<MethodAnalysisContext> MembersOn(TypeAnalysisContext type)
    {
        var instance = type as GenericInstanceTypeAnalysisContext;
        var owner = instance?.GenericType ?? type;
        // Snapshot: nested analyses of candidate bodies can inject members.
        foreach (var member in owner.Methods.ToArray())
            yield return instance != null
                ? member.MakeConcreteGenericMethod(instance.GenericArguments, [])
                : member;
    }

    // ---------------------------------------------------------- body summaries

    private static BodySummary? Summarize(MethodAnalysisContext candidate,
        MethodAnalysisContext context)
    {
        if (Summaries.TryGetValue(candidate, out var cached))
            return cached.Summary;

        var inFlight = s_summarizing ??= new HashSet<MethodAnalysisContext>();
        if (!inFlight.Add(candidate))
            return null;

        try
        {
            return Summaries.GetOrAdd(candidate,
                new SummaryResult { Summary = BuildSummary(candidate, context) }).Summary;
        }
        catch
        {
            return null;
        }
        finally
        {
            inFlight.Remove(candidate);
        }
    }

    // The body the summary reads, with facts present. Only method monitors
    // acquired through Monitor.TryEnter are ever held by a caller of this -
    // waiting on one is what would let two workers hold-and-wait each other,
    // so a mid-analysis body is a pending ask, not a blocking one.
    private static MethodAnalysisContext? EnsureBody(MethodAnalysisContext candidate,
        MethodAnalysisContext context)
    {
        var body = candidate;
        try
        {
            // The shared ref->concrete map is a plain dictionary mutated by
            // parallel analyses; a torn enumeration just means no variant.
            if (body.UnderlyingPointer == 0 && candidate is ConcreteGenericMethodAnalysisContext concrete)
                foreach (var variant in context.AppContext.ConcreteGenericMethodsByRef.Values)
                    if (variant.BaseMethodContext == (concrete.BaseMethodContext ?? candidate)
                        && variant.UnderlyingPointer != 0)
                    {
                        body = variant;
                        break;
                    }
        }
        catch (InvalidOperationException)
        {
        }

        if (body.MemberBodyFacts != null)
            return body;
        if (body.ControlFlowGraph == null && body.UnderlyingPointer == 0)
            return null;

        // Facts only exist once the body's AnalyzeCore ends, so reaching the
        // monitor means the body is still inside it - and a body inside
        // AnalyzeCore never runs this pass, so it can never be waiting on this
        // worker. Waiting out that lift cannot wait-cycle, and once it lands
        // every asker sees the same facts in the same state.
        Monitor.Enter(body);
        try
        {
            if (body.ControlFlowGraph == null)
                body.AnalyzeForMemberSummary();
            // Bodies never lifted through AnalyzeCore - test fixtures and
            // other synthetic contexts - still get their facts, on this same
            // thread where the live block list cannot be mutating.
            if (body.MemberBodyFacts == null)
                CaptureBodyFacts(body);
        }
        catch
        {
            return null;
        }
        finally
        {
            Monitor.Exit(body);
        }
        return body.MemberBodyFacts != null ? body : null;
    }

    private static BodySummary? BuildSummary(MethodAnalysisContext candidate,
        MethodAnalysisContext context)
    {
        var facts = EnsureBody(candidate, context)?.MemberBodyFacts;
        if (facts == null || facts.Rejected)
            return null;

        var thisLocal = facts.ThisLocal;
        if (thisLocal == null)
            Logger.VerboseNewline(
                $"Inlined member recovery: {candidate.FullName}: no this-local",
                "Analysis");
        var paramIndex = facts.ParamIndex;
        var definitions = facts.Definitions;
        var returns = facts.Returns;

        // Produced roots: `this` for a ctor/writer, the returned value for a
        // producer; a freshly allocated local counts as produced too.
        var isCtor = candidate.Name == ".ctor" && !candidate.IsStatic;
        var roots = new HashSet<LocalVariable>();
        foreach (var r in returns)
            if (Chase(r, definitions) is { } root)
                roots.Add(root);
        if (isCtor && thisLocal != null)
            roots.Add(thisLocal);
        else if (!isCtor && roots.Count == 0 && thisLocal != null
                 && candidate.ReturnType?.FullName is "System.Void")
            roots.Add(thisLocal); // instance void writers produce `this`

        var summary = new BodySummary();
        var okay = true;
        foreach (var (destination, source) in facts.RawStores)
        {
            if (!roots.Contains(destination.Local) || destination.Containers.Count != 0)
            {
                okay = false;
                break;
            }
            summary.Stores[FieldKey.Of(destination.Field)] =
                (destination.Field, Classify(source, definitions, paramIndex, thisLocal, 0));
        }
        foreach (var (receiver, args, ctor) in facts.CtorCalls)
        {
            if (!roots.Contains(receiver))
            {
                okay = false;
                break;
            }
            var inner = Summarize(ctor, context);
            if (inner == null)
            {
                okay = false;
                break;
            }
            foreach (var (key, stored) in inner.Stores)
                summary.Stores[key] = (stored.Field, Substitute(stored.Source, args,
                    definitions, paramIndex, thisLocal));
        }
        if (!okay)
            return null;

        // A `return this.F` / `return <static>` shape: produced reads, not stores.
        if (summary.Stores.Count == 0 && returns.Count == 1)
        {
            var source = returns[0] is LocalVariable returned
                && definitions.TryGetValue(returned, out var defined)
                    ? defined
                    : returns[0];
            if (source is FieldReference { Containers.Count: 0 } fieldRead
                && thisLocal != null && ReferenceEquals(fieldRead.Local, thisLocal))
                summary.ReturnsInstanceField = fieldRead.Field;
            else if (source is FieldReference staticRead
                     && (staticRead.Local.Type is StaticFieldStorageTypeAnalysisContext
                         || staticRead.Field.IsStatic))
                summary.ReturnsStaticField = staticRead.Field.IsStatic
                    ? staticRead.Field
                    : staticRead.Containers.Count > 0 ? staticRead.Containers[0] : staticRead.Field;
        }

        // A struct result is also assembled lane-wise into the return
        // aggregate: `ret.x <- tmp.x; ret.y <- statics.sf.y` returns the whole
        // `root.prefix` value when every store into the returned local copies
        // one lane of a shared field path on a shared root.
        if (summary.ReturnsInstanceField == null && summary.ReturnsStaticField == null
            && returns.Count == 1 && returns[0] is LocalVariable returnedLocal
            && returnedLocal.Type?.IsValueType == true
            && TraceReturnedValue(facts, returnedLocal, thisLocal) is { } trace)
        {
            var (root, prefix) = trace;
            if (thisLocal != null && ReferenceEquals(root, thisLocal))
                summary.ReturnsInstanceField = prefix[^1];
            else if (root.Type is StaticFieldStorageTypeAnalysisContext)
                summary.ReturnsStaticField = prefix[^1];
        }
        return summary;
    }

    // Resolve every raw store into `returned` to `(root, prefix + lane)` and
    // keep the common `(root, prefix)`: all lanes of the returned value must
    // come from the same field path on the same root. A lane that stops at a
    // different root, skips a field, or has no field source is not a
    // whole-value return and yields null.
    private static (LocalVariable Root, List<FieldAnalysisContext> Prefix)? TraceReturnedValue(
        BodyFacts facts, LocalVariable returned, LocalVariable? thisLocal)
    {
        LocalVariable? root = null;
        List<FieldAnalysisContext>? prefix = null;
        var lanes = new List<FieldReference>();
        foreach (var (destination, source) in facts.RawStores)
        {
            if (!ReferenceEquals(destination.Local, returned))
                continue;
            lanes.Add(destination);
            var resolved = TraceFieldPath(source, facts.Definitions);
            if (resolved == null)
                return null;
            var (resolvedRoot, path) = resolved.Value;
            var lanePath = destination.Containers.Append(destination.Field).ToList();
            if (path.Count <= lanePath.Count
                || !lanePath.Select((f, i) => (f, i)).All(pair =>
                    SameField(path[path.Count - lanePath.Count + pair.i], pair.f)))
                return null;
            var candidatePrefix = path.Take(path.Count - lanePath.Count).ToList();
            if (candidatePrefix.Count == 0)
                return null; // `return <root>` is not a member access
            if (root == null)
            {
                root = resolvedRoot;
                prefix = candidatePrefix;
            }
            else if (!ReferenceEquals(root, resolvedRoot)
                     || !SamePath(candidatePrefix, prefix!))
                return null;
        }
        if (root == null || prefix == null)
            return null;
        var leafType = FieldKey.GenericDef(prefix[^1].FieldType) ?? prefix[^1].FieldType;
        if (leafType == null || !CoversAllFields(leafType, lanes, []))
            return null;
        return (root, prefix);
    }

    // Walk a store's source down to `(rootLocal, fieldPath)` by folding a
    // `local.field` read into the field path `local` was defined by. A local
    // whose definition is not a field path is the root itself (a statics
    // block, `this`, a parameter).
    private static (LocalVariable Root, List<FieldAnalysisContext> Path)? TraceFieldPath(
        IOperand source, Dictionary<LocalVariable, IOperand> definitions)
    {
        var path = new List<FieldAnalysisContext>();
        var current = source;
        for (var guard = 0; guard < 16; guard++)
        {
            switch (current)
            {
                case FieldReference field:
                    path.InsertRange(0, field.Containers.Append(field.Field));
                    current = field.Local;
                    break;
                case LocalVariable local when definitions.TryGetValue(local, out var def)
                    && def is LocalVariable or FieldReference:
                    current = def;
                    break;
                case LocalVariable local:
                    return (local, path);
                default:
                    return null;
            }
        }
        return null;
    }

    private static IOperand Unwrap(IOperand operand) =>
        operand is AddressOf address ? address.Target : operand;

    private static LocalVariable? Chase(IOperand operand,
        Dictionary<LocalVariable, IOperand> definitions)
    {
        var seen = new HashSet<LocalVariable>();
        var current = operand as LocalVariable;
        while (current != null && definitions.TryGetValue(current, out var source)
               && source is LocalVariable next && seen.Add(current))
            current = next;
        return current;
    }

    private static ProducedSource Classify(IOperand source,
        Dictionary<LocalVariable, IOperand> definitions,
        Dictionary<LocalVariable, int> paramIndex, LocalVariable? thisLocal, int depth)
    {
        if (depth > 4)
            return new UnknownSource();
        switch (source)
        {
            case LocalVariable local:
                if (thisLocal != null && ReferenceEquals(local, thisLocal))
                    return new ThisSource();
                if (paramIndex.TryGetValue(local, out var index))
                    return new ParamSource(index);
                if (definitions.TryGetValue(local, out var def)
                    && def is not LocalVariable { Name: "__newobj__" })
                    return Classify(def, definitions, paramIndex, thisLocal, depth + 1);
                return new UnknownSource();
            case FieldReference { Containers.Count: 0 } field
                when thisLocal != null && ReferenceEquals(field.Local, thisLocal):
                return new ThisFieldSource(field.Field);
            case Immediate immediate:
                return new ConstSource(immediate.Value);
            case FloatLiteral f:
                return new ConstSource(f.Value);
            case DoubleLiteral d:
                return new ConstSource(d.Value);
            default:
                return new UnknownSource();
        }
    }

    private static ProducedSource Substitute(ProducedSource source, List<IOperand> callArgs,
        Dictionary<LocalVariable, IOperand> definitions,
        Dictionary<LocalVariable, int> paramIndex, LocalVariable? thisLocal) =>
        source switch
        {
            ParamSource param when param.Index < callArgs.Count =>
                Classify(callArgs[param.Index], definitions, paramIndex, thisLocal, 0),
            _ => source,
        };
}
