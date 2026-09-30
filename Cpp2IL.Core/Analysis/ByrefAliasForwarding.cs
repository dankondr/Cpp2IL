using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Post-SSA alias elimination for managed-pointer locals.
///
/// Phi lowering writes an edge copy into the joined local on every incoming edge; when those
/// copies all spell the same managed-pointer operand (a ref parameter, an address-take, a field
/// or element access), the joined local is not a distinct reference - it is the same alias
/// re-spelled per path. <see cref="Simplifier"/> cannot forward it because the local has several
/// definitions, so it survives into emission, where every store becomes a `ref` bind against a
/// `ref` parameter or another alias: a `ref` local's rebind to a `ref` parameter cannot be
/// expressed in C# (the parameter may escape only through return).
///
/// For such locals every use can read the shared root operand directly - the slot never carried
/// a different address - so this pass rewrites each use to the root and removes the local and
/// its copies. The bar is deliberately strict: every source outside a connected alias component
/// must name the same root operand (otherwise the member's value is path-dependent and the local
/// is real), and every use of a member must sit in a position that can take the root's operand
/// shape.
/// </summary>
internal static class ByrefAliasForwarding
{
    public static void Run(MethodAnalysisContext method)
    {
        var graph = method.ControlFlowGraph;
        if (graph == null)
            return;

        // A copy whose source and destination spell the same cell emits a bare
        // `v = v` the decompiler prints as an unassigned self-read. `[v+0]` and
        // `v` spell the same cell for a non-managed-pointer local - the load
        // and store shortcuts already treat it that way - so the move is a
        // no-op and goes out here.
        var removedCopies = false;
        foreach (var block in graph.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                if (instruction.OpCode == OpCode.Move
                    && SameCell(instruction.Operands[0], instruction.Operands[1]))
                {
                    instruction.OpCode = OpCode.Nop;
                    instruction.SetOperands();
                    removedCopies = true;
                }
            }
        }

        // Map every local to its defining instructions. A candidate is defined only by Move
        // copies - any other definition means the slot carries a computed value, not an alias.
        var definitions = new Dictionary<LocalVariable, List<Instruction>>();
        foreach (var block in graph.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                if (instruction.Destination is not LocalVariable destination)
                    continue;
                if (!definitions.TryGetValue(destination, out var list))
                    definitions[destination] = list = [];
                list.Add(instruction);
            }
        }

        // A call can clobber a register implicitly (an address-taken slot it writes
        // through) - a rewrite of that register is a definition this pass cannot see.
        var clobberedRegisters = new HashSet<string?>();
        foreach (var block in graph.Blocks)
            foreach (var instruction in block.Instructions)
                if (instruction.ImplicitDefinition is { } clobbered)
                    clobberedRegisters.Add(clobbered.Name);

        var parameterLocals = new HashSet<LocalVariable>(method.ParameterLocals);
        var candidates = new HashSet<LocalVariable>();
        foreach (var (local, defs) in definitions)
        {
            if (local.Type is not ByRefTypeAnalysisContext
                || parameterLocals.Contains(local)
                || clobberedRegisters.Contains(local.Register.Name)
                || defs.Exists(def => def.OpCode != OpCode.Move))
                continue;
            candidates.Add(local);
        }

        if (candidates.Count == 0)
            return;

        // Group alias components: two candidates belong together when one's copy sources the
        // other, so each member's value is whatever the component's outside sources are.
        var parent = candidates.ToDictionary(local => local, local => local);
        LocalVariable Find(LocalVariable local)
        {
            while (parent[local] != local)
            {
                parent[local] = parent[parent[local]];
                local = parent[local];
            }

            return local;
        }

        foreach (var local in candidates)
        {
            foreach (var def in definitions[local])
            {
                if (def.Operands[1] is not LocalVariable source || !candidates.Contains(source))
                    continue;
                var a = Find(local);
                var b = Find(source);
                if (a != b)
                    parent[a] = b;
            }
        }

        var removedAny = false;
        foreach (var component in candidates.GroupBy(Find))
        {
            var members = component.ToHashSet();

            IOperand? root = null;
            var singleRoot = true;
            foreach (var member in members)
            {
                foreach (var def in definitions[member])
                {
                    var source = def.Operands[1];
                    if (source is LocalVariable sourceLocal && members.Contains(sourceLocal))
                        continue;
                    if (root == null)
                        root = source;
                    else if (!root.Equals(source))
                    {
                        singleRoot = false;
                        break;
                    }
                }

                if (!singleRoot)
                    break;
            }

            if (!singleRoot || root == null || !IsForwardableRoot(root))
                continue;

            // A member forwards only when every one of its uses can take the root's operand
            // shape; a member whose own cell is read (&member) keeps its slot.
            var forwarded = members
                .Where(member => CanForwardAllUses(graph, member, root, definitions[member]))
                .ToList();

            foreach (var local in forwarded)
            {
                foreach (var block in graph.Blocks)
                {
                    foreach (var instruction in block.Instructions)
                    {
                        if (definitions[local].Contains(instruction))
                            continue;
                        for (var i = 0; i < instruction.Operands.Count; i++)
                            SubstituteOperand(instruction, i, local, root);
                    }
                }

                foreach (var def in definitions[local])
                {
                    def.OpCode = OpCode.Nop;
                    def.SetOperands();
                }

                method.Locals.Remove(local);
                removedAny = true;
            }
        }

        // Candidates the component walk could not forward fall into two
        // recoverable classes the single-root rule cannot see:
        //
        // - a local rebound to *different* roots on different paths (`r = &a`
        //   on one edge, `r = &b` on another) - the join is real, but every
        //   individual use is still reached by exactly one binding, so each
        //   use reads its reaching pointee directly;
        // - a uniform `r = &x` alias whose uses sit in compound positions -
        //   the root operand `&x` cannot substitute `x.field`, but the
        //   pointee `x` can.
        //
        // Either way the emitted alternative is a `ref` local retargeted
        // between pointees - legal IL, illegal C# (a `ref` cannot rebind to a
        // narrower scope, and binding an out parameter reads it unassigned).
        // Resolving the uses removes the local outright. A use reached by
        // bindings to different pointees vetoes the local: its value really
        // is path-dependent and it stays a `ref` slot.
        var remaining = candidates.Where(method.Locals.Contains).ToHashSet();
        var progress = true;
        while (progress)
        {
            progress = false;
            foreach (var local in remaining.ToList())
            {
                if (TryResolvePerUse(graph, local, definitions[local], remaining))
                {
                    foreach (var def in definitions[local])
                    {
                        def.OpCode = OpCode.Nop;
                        def.SetOperands();
                    }
                    method.Locals.Remove(local);
                    remaining.Remove(local);
                    removedCopies = true;
                    progress = true;
                }
            }
        }

        if (removedAny || removedCopies)
        {
            graph.RemoveNops();
            graph.RemoveEmptyBlocks();
        }
    }

    // The cell an operand writes or reads as a whole: the local itself, or a
    // zero-offset memory form over a non-managed-pointer local (which the
    // emitter already spells as that local's slot). Byref bases spell a
    // dereference, not the cell.
    private static LocalVariable? CellOf(IOperand operand) => operand switch
    {
        LocalVariable local => local,
        MemoryOperand { Index: null, Addend: 0, Scale: 0, Base: LocalVariable { Type: not ByRefTypeAnalysisContext } cell }
            => cell,
        _ => null,
    };

    private static bool SameCell(IOperand a, IOperand b) =>
        CellOf(a) is { } cell && ReferenceEquals(cell, CellOf(b));

    // Every definition of `local` must classify into a root the uses can
    // substitute, and every use must be reached only by defs agreeing on one
    // root. On success each use is substituted and true is returned; on any
    // failure nothing is rewritten.
    private static bool TryResolvePerUse(ISILControlFlowGraph graph, LocalVariable local,
        List<Instruction> defs, HashSet<LocalVariable> candidates)
    {
        // &local binds name the pointee; a copied pointer names another slot's
        // alias value; anything else forwardable is an opaque pointer only
        // bare uses can take. A source naming a surviving candidate chains
        // the resolution - the local is retried after that candidate's uses
        // are substituted.
        var roots = new (IOperand? pointer, LocalVariable? pointee)[defs.Count];
        for (var i = 0; i < defs.Count; i++)
        {
            switch (defs[i].Operands[1])
            {
                case AddressOf { Target: LocalVariable pointee } bind
                    when !candidates.Contains(pointee) && !ReferenceEquals(pointee, local):
                    roots[i] = (bind, pointee);
                    break;
                case LocalVariable source
                    when !candidates.Contains(source) && !ReferenceEquals(source, local):
                    roots[i] = (source, source);
                    break;
                case { } other when IsForwardableRoot(other)
                    && !LocalVariables.ContainsLocal(other, local):
                    roots[i] = (other, null);
                    break;
                default:
                    return false;
            }
        }

        var defSet = new HashSet<Instruction>(defs);
        var rootIndex = defs.Select((d, i) => (d, i)).ToDictionary(x => x.d, x => x.i);

        // Reaching definitions per block: a def in a block shadows every
        // earlier reaching def, so out[b] is the block's last def when it has
        // one. Iterate the union over predecessors to a fixpoint.
        var blocks = graph.Blocks;
        var reachingIn = new Dictionary<Block, HashSet<Instruction>>(blocks.Count);
        var reachingOut = new Dictionary<Block, HashSet<Instruction>>(blocks.Count);
        foreach (var block in blocks)
        {
            reachingIn[block] = [];
            reachingOut[block] = [];
        }
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var block in blocks)
            {
                var next = new HashSet<Instruction>();
                foreach (var predecessor in block.Predecessors)
                    next.UnionWith(reachingOut[predecessor]);
                if (!next.SetEquals(reachingIn[block]))
                {
                    reachingIn[block] = next;
                    changed = true;
                }
                Instruction? lastDef = null;
                foreach (var instruction in block.Instructions)
                    if (defSet.Contains(instruction))
                        lastDef = instruction;
                var outSet = lastDef != null ? [lastDef] : new HashSet<Instruction>(next);
                if (!outSet.SetEquals(reachingOut[block]))
                {
                    reachingOut[block] = outSet;
                    changed = true;
                }
            }
        }

        // Validate every use: the defs reaching it must agree on one root, and
        // the position must take that root's shape. Substitutions are applied
        // only after the whole local validates.
        var substitutions = new List<(Instruction instruction, int index, IOperand? compound, IOperand pointer)>();
        foreach (var block in blocks)
        {
            var reaching = reachingIn[block];
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                var instruction = block.Instructions[i];
                if (defSet.Contains(instruction))
                {
                    // A def's own source may still read the local (&local or a
                    // compound over it) - that is a use at this point, resolved
                    // against the defs reaching *before* it.
                    if (!LocalVariables.ContainsLocal(instruction.Operands[1], local))
                    {
                        reaching = [instruction];
                        continue;
                    }
                }
                else if (!instruction.Operands.Any(operand => LocalVariables.ContainsLocal(operand, local)))
                {
                    continue;
                }

                if (reaching.Count == 0)
                    return false; // a read no binding can reach - the local stays a ref slot

                var reachingRoots = reaching.Select(d => roots[rootIndex[d]]).ToList();
                var pointerRoot = reachingRoots[0].pointer;
                var pointeeRoot = reachingRoots[0].pointee;
                if (reachingRoots.Any(r => !RootEquals(r.pointer, pointerRoot)))
                    return false; // path-dependent bindings - a real ref variable

                for (var operandIndex = 0; operandIndex < instruction.Operands.Count; operandIndex++)
                {
                    var operand = instruction.Operands[operandIndex];
                    if (!LocalVariables.ContainsLocal(operand, local))
                        continue;
                    if (instruction.OpCode == OpCode.Move && operandIndex == 0
                        && ReferenceEquals(operand, local) && defSet.Contains(instruction))
                        continue; // the binding side of its own def
                    if (ReferenceEquals(operand, local))
                    {
                        if (pointerRoot == null)
                            return false;
                        substitutions.Add((instruction, operandIndex, null, pointerRoot));
                        continue;
                    }
                    if (pointeeRoot == null || !CanSubstitute(operand, local, pointeeRoot))
                        return false;
                    substitutions.Add((instruction, operandIndex, pointeeRoot, pointeeRoot));
                }

                if (defSet.Contains(instruction))
                    reaching = [instruction];
            }
        }

        foreach (var (instruction, index, compound, pointer) in substitutions)
        {
            if (compound != null)
                SubstituteOperand(instruction, index, local, compound);
            else
                instruction.SetOperand(index, pointer);
        }

        return true;

        static bool RootEquals(IOperand? a, IOperand? b) =>
            a == null ? b == null : a.Equals(b);
    }

    // Operands that can sit anywhere a `ref`-typed operand can: a local emits a load of the
    // named cell, and address/element expressions re-emit their address computation. A literal
    // cannot (a `ref` never binds a constant), a call result needs a materialized slot - the
    // very ref local this pass removes - and registers or stack offsets cannot be spelled at all.
    private static bool IsForwardableRoot(IOperand operand) => operand switch
    {
        LocalVariable or AddressOf or FieldReference or SelectedFieldReference
            or ArrayAccess or ArrayElementFieldReference or MemoryOperand
            or ArrayLength or ReferenceCast => true,
        _ => false,
    };

    private static bool CanForwardAllUses(ISILControlFlowGraph graph, LocalVariable local,
        IOperand root, List<Instruction> memberDefs)
    {
        var defSet = new HashSet<Instruction>(memberDefs);
        foreach (var block in graph.Blocks)
        {
            foreach (var instruction in block.Instructions)
            {
                if (defSet.Contains(instruction))
                    continue;
                for (var i = 0; i < instruction.Operands.Count; i++)
                {
                    var operand = instruction.Operands[i];
                    if (LocalVariables.ContainsLocal(operand, local) && !CanSubstitute(operand, local, root))
                        return false;
                }
            }
        }

        return true;
    }

    private static bool CanSubstitute(IOperand operand, LocalVariable local, IOperand root) =>
        operand switch
        {
            // The bare alias value forwards anywhere an operand can go.
            _ when ReferenceEquals(operand, local) => true,

            // Compound reads of the alias (a memory base or index, a field receiver, an
            // array element) read through the same pointer, so they take the root - but
            // only when it is a local, the shape those positions require.
            MemoryOperand or FieldReference or SelectedFieldReference
                or ArrayAccess or ArrayElementFieldReference or ArrayLength or ReferenceCast
                => root is LocalVariable,

            // &local is the local's own cell, not its value: forwarding would name a
            // different storage location, so the member keeps its slot. Compound targets
            // forward their inner locals like any other operand.
            AddressOf address => !ReferenceEquals(address.Target, local)
                && CanSubstituteAddressTarget(address.Target, local, root),

            _ => false,
        };

    private static bool CanSubstituteAddressTarget(IOperand target, LocalVariable local, IOperand root) =>
        target switch
        {
            LocalVariable targetLocal => !ReferenceEquals(targetLocal, local),
            MemoryOperand or FieldReference or SelectedFieldReference
                or ArrayAccess or ArrayElementFieldReference or ArrayLength or ReferenceCast
                => root is LocalVariable,
            AddressOf nested => CanSubstituteAddressTarget(nested.Target, local, root),
            _ => false,
        };

    private static void SubstituteOperand(Instruction instruction, int index, LocalVariable local,
        IOperand root)
    {
        var operand = instruction.Operands[index];
        switch (operand)
        {
            case LocalVariable _ when ReferenceEquals(operand, local):
                instruction.SetOperand(index, root);
                break;
            case MemoryOperand memory when root is LocalVariable replacement:
                if (memory.Base is LocalVariable baseLocal && ReferenceEquals(baseLocal, local))
                    memory.Base = replacement;
                if (memory.Index is LocalVariable indexLocal && ReferenceEquals(indexLocal, local))
                    memory.Index = replacement;
                instruction.SetOperand(index, memory);
                break;
            case FieldReference field when ReferenceEquals(field.Local, local)
                && root is LocalVariable replacement:
                field.Local = replacement;
                break;
            case SelectedFieldReference selected when root is LocalVariable replacement:
                if (ReferenceEquals(selected.Selector, local))
                    selected.Selector = replacement;
                foreach (var choice in selected.Choices)
                    if (ReferenceEquals(choice.Field.Local, local))
                        choice.Field.Local = replacement;
                break;
            case ArrayAccess access when root is LocalVariable replacement:
                if (ReferenceEquals(access.Array, local))
                    access.Array = replacement;
                if (access.Index is LocalVariable accessIndex && ReferenceEquals(accessIndex, local))
                    access.Index = replacement;
                break;
            case ArrayElementFieldReference element when root is LocalVariable replacement:
                if (ReferenceEquals(element.Array, local))
                    element.Array = replacement;
                if (element.Index is LocalVariable elementIndex && ReferenceEquals(elementIndex, local))
                    element.Index = replacement;
                break;
            case ArrayLength length when ReferenceEquals(length.Array, local)
                && root is LocalVariable replacement:
                length.Array = replacement;
                break;
            case ReferenceCast cast when ReferenceEquals(cast.Value, local)
                && root is LocalVariable replacement:
                instruction.SetOperand(index, new ReferenceCast(replacement, cast.Type, cast.NullOnFailure));
                break;
            case AddressOf address:
                SubstituteInAddressTarget(address, local, root);
                break;
        }
    }

    private static void SubstituteInAddressTarget(AddressOf address, LocalVariable local, IOperand root)
    {
        if (root is not LocalVariable replacement)
            return;
        switch (address.Target)
        {
            case MemoryOperand memory:
                if (memory.Base is LocalVariable baseLocal && ReferenceEquals(baseLocal, local))
                    memory.Base = replacement;
                if (memory.Index is LocalVariable indexLocal && ReferenceEquals(indexLocal, local))
                    memory.Index = replacement;
                address.Target = memory; // MemoryOperand is a struct, write the copy back
                break;
            case FieldReference field when ReferenceEquals(field.Local, local):
                field.Local = replacement;
                break;
            case SelectedFieldReference selected:
                if (ReferenceEquals(selected.Selector, local))
                    selected.Selector = replacement;
                foreach (var choice in selected.Choices)
                    if (ReferenceEquals(choice.Field.Local, local))
                        choice.Field.Local = replacement;
                break;
            case ArrayAccess access:
                if (ReferenceEquals(access.Array, local))
                    access.Array = replacement;
                if (access.Index is LocalVariable accessIndex && ReferenceEquals(accessIndex, local))
                    access.Index = replacement;
                break;
            case ArrayElementFieldReference element:
                if (ReferenceEquals(element.Array, local))
                    element.Array = replacement;
                if (element.Index is LocalVariable elementIndex && ReferenceEquals(elementIndex, local))
                    element.Index = replacement;
                break;
            case ArrayLength length when ReferenceEquals(length.Array, local):
                length.Array = replacement;
                break;
            case ReferenceCast cast when ReferenceEquals(cast.Value, local):
                address.Target = new ReferenceCast(replacement, cast.Type, cast.NullOnFailure);
                break;
            case AddressOf nested:
                SubstituteInAddressTarget(nested, local, root);
                break;
        }
    }
}
