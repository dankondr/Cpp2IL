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

        if (removedAny)
        {
            graph.RemoveNops();
            graph.RemoveEmptyBlocks();
        }
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
