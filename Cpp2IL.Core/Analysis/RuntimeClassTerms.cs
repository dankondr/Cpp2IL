using System.Collections.Generic;
using System.Linq;
using Cpp2IL.Core.Graphs;
using Cpp2IL.Core.ISIL;
using Cpp2IL.Core.Model.Contexts;

namespace Cpp2IL.Core.Analysis;

/// <summary>
/// Per-CFG definition index for operands that are NOT single-assignment: after SSA removal a
/// register-versioned local can have several definitions merging at a join, and even inside SSA
/// form phi-less merges of a reused name occur. Recognisers query defs relative to a use site -
/// <see cref="ReachingDef"/> for the unique def still live there, <see cref="MergeSources"/> for
/// the per-edge defs of a local that is an implicit phi.
/// </summary>
public sealed class DefUseIndex
{
    private readonly ISILControlFlowGraph _cfg;
    private readonly Dictionary<LocalVariable, List<Instruction>> _defs = new();
    private readonly Dictionary<Instruction, Block> _home = new();
    private readonly Dictionary<Instruction, int> _indexInBlock = new();
    private DominatorInfo? _dominators;

    public DefUseIndex(ISILControlFlowGraph cfg, DominatorInfo? dominators = null)
    {
        _cfg = cfg;
        _dominators = dominators;
        foreach (var block in cfg.Blocks)
            for (var i = 0; i < block.Instructions.Count; i++)
            {
                var instruction = block.Instructions[i];
                _home[instruction] = block;
                _indexInBlock[instruction] = i;
                if (instruction.Destination is LocalVariable destination)
                    (_defs.TryGetValue(destination, out var list) ? list : _defs[destination] = []).Add(instruction);
            }
    }

    public DominatorInfo Dominators => _dominators ??= new DominatorInfo(_cfg);

    public Block? HomeOf(Instruction instruction) =>
        _home.TryGetValue(instruction, out var block) ? block : null;

    /// <summary>Every instruction assigning the local, in program order per block.</summary>
    public IReadOnlyList<Instruction> DefinitionsOf(LocalVariable local) =>
        _defs.TryGetValue(local, out var list) ? list : [];

    /// <summary>
    /// The definition of <paramref name="local"/> live at <paramref name="use"/>: the latest def
    /// earlier in the use's block, or the def in the nearest dominator block. Null when no def
    /// reaches the use, or when different defs reach it on different edges - that is an implicit
    /// phi, for which <see cref="MergeSources"/> enumerates the inputs.
    /// </summary>
    public Instruction? ReachingDef(LocalVariable local, Instruction use)
    {
        if (DefinitionsOf(local) is not { Count: > 0 } defs || !_home.TryGetValue(use, out var useBlock))
            return null;
        if (defs.Count == 1)
            return defs[0];

        Instruction? inBlock = null;
        Instruction? dominating = null;
        var dominatingDepth = -1;
        foreach (var def in defs)
        {
            var defBlock = _home[def];
            if (defBlock == useBlock)
            {
                if (_indexInBlock[def] < _indexInBlock[use]
                    && (inBlock == null || _indexInBlock[def] > _indexInBlock[inBlock]))
                    inBlock = def;
            }
            else if (Dominators.Dominates(defBlock, useBlock))
            {
                var depth = DominatorDepth(defBlock);
                if (depth > dominatingDepth)
                {
                    dominating = def;
                    dominatingDepth = depth;
                }
            }
        }

        return inBlock ?? dominating;
    }

    /// <summary>
    /// The definition of <paramref name="local"/> live when control leaves <paramref name="edge"/>:
    /// the last def in the edge block, else the nearest strictly dominating def.
    /// </summary>
    public Instruction? ReachingDefOnEdge(LocalVariable local, Block edge)
    {
        if (DefinitionsOf(local) is not { Count: > 0 } defs)
            return null;

        Instruction? inEdge = null;
        Instruction? dominating = null;
        var dominatingDepth = -1;
        foreach (var def in defs)
        {
            var defBlock = _home[def];
            if (defBlock == edge)
            {
                if (inEdge == null || _indexInBlock[def] > _indexInBlock[inEdge])
                    inEdge = def;
            }
            else if (Dominators.Dominates(defBlock, edge))
            {
                var depth = DominatorDepth(defBlock);
                if (depth > dominatingDepth)
                {
                    dominating = def;
                    dominatingDepth = depth;
                }
            }
        }

        return inEdge ?? dominating;
    }

    /// <summary>
    /// The defs of <paramref name="local"/> reaching <paramref name="use"/> on different
    /// predecessor edges - the inputs of an implicit phi. Returns (edge, def) pairs aligned with
    /// <see cref="Block.Predecessors"/>; null when the use is fed by a single reaching def or an
    /// edge's def cannot be resolved.
    /// </summary>
    public List<(Block Edge, Instruction Def)>? MergeSources(LocalVariable local, Instruction use)
    {
        if (!_home.TryGetValue(use, out var useBlock))
            return null;

        // An explicit phi at the top of the use's block: map each operand to its edge.
        if (ReachingDef(local, use) is { OpCode: OpCode.Phi } phi)
        {
            var result = new List<(Block, Instruction)>();
            for (var i = 0; i < useBlock.Predecessors.Count && i + 1 < phi.Operands.Count; i++)
            {
                if (phi.Operands[i + 1] is not LocalVariable input
                    || ReachingDefOnEdge(input, useBlock.Predecessors[i]) is not { } edgeDef)
                    return null;
                result.Add((useBlock.Predecessors[i], edgeDef));
            }
            return result.Count >= 2 ? result : null;
        }

        var sources = new List<(Block, Instruction)>();
        foreach (var predecessor in useBlock.Predecessors)
            if (ReachingDefOnEdge(local, predecessor) is { } edgeDef)
                sources.Add((predecessor, edgeDef));

        return sources.Count >= 2 ? sources : null;
    }

    private int DominatorDepth(Block block)
    {
        var depth = 0;
        var current = block;
        var visited = new HashSet<Block>();
        while (visited.Add(current)
               && Dominators.ImmediateDominators.TryGetValue(current, out var idom)
               && idom != null)
        {
            depth++;
            current = idom;
        }
        return depth;
    }
}

/// <summary>
/// Reads off an <c>Il2CppClass&lt;K&gt;*</c> value are named terms: <c>[klass + cctorFinished]</c>
/// is <c>initialised(K)</c>, <c>[klass + typeHierarchyDepth]</c> is <c>depth(K)</c>,
/// <c>[klass + vtable + 16n]</c> is <c>vtable(K, n)</c>, and so on. A copy or a phi whose inputs
/// are the same class pointer is the same class pointer, so the term survives the value's SSA
/// plumbing - matchers consume the term, not the instruction shape.
/// </summary>
public static class RuntimeClassTerms
{
    /// <summary>
    /// The K for an operand holding an Il2CppClass&lt;K&gt;*: a typed class local, a
    /// <c>typeof(T)</c>/runtime-class producer, an <c>[instance]</c> klass load, or a copy /
    /// phi / multi-def merge whose inputs are all the same class pointer.
    /// </summary>
    public static TypeAnalysisContext? RepresentedClass(IOperand operand, DefUseIndex index,
        Instruction? use = null)
    {
        var visited = new HashSet<IOperand>();
        return Represented(operand, use);

        TypeAnalysisContext? Represented(IOperand operand, Instruction? use)
        {
            switch (operand)
            {
                case RuntimeClassTypeAnalysisContext runtimeClass:
                    return runtimeClass.RepresentedType;
                case TypeAnalysisContext type:
                    return type;
                case LocalVariable { Type: RuntimeClassTypeAnalysisContext { RepresentedType: { } typed } }:
                    return typed;
                case LocalVariable local when visited.Add(local):
                {
                    var definition = use == null ? SoleDefinition(local) : index.ReachingDef(local, use);
                    if (definition is { OpCode: OpCode.Move, Operands: [_, var source] })
                        return Represented(source, definition);

                    if (definition is { OpCode: OpCode.Phi } phi)
                    {
                        TypeAnalysisContext? merged = null;
                        foreach (var input in phi.Operands.Skip(1).OfType<LocalVariable>())
                        {
                            var inputClass = Represented(input, null);
                            if (inputClass == null || merged != null && !SameType(merged, inputClass))
                                return null;
                            merged = inputClass;
                        }
                        return merged;
                    }

                    // A phi-less merge (several defs of one local reaching a use on different
                    // edges) is the same class pointer iff every edge def is.
                    if (use != null && index.MergeSources(local, use) is { } sources)
                    {
                        TypeAnalysisContext? merged = null;
                        foreach (var (_, sourceDef) in sources)
                        {
                            if (sourceDef is not { OpCode: OpCode.Move, Operands: [_, var sourceOperand] })
                                return null;
                            var inputClass = Represented(sourceOperand, sourceDef);
                            if (inputClass == null || merged != null && !SameType(merged, inputClass))
                                return null;
                            merged = inputClass;
                        }
                        return merged;
                    }

                    return null;
                }
                case MemoryOperand { Index: null, Scale: 0, Addend: 0, Base: LocalVariable instance }:
                    // A klass load [instance + 0]: the class pointer for the instance's own type.
                    return instance.Type;
                default:
                    return null;
            }
        }

        Instruction? SoleDefinition(LocalVariable local)
        {
            var defs = index.DefinitionsOf(local);
            return defs.Count == 1 ? defs[0] : null;
        }
    }

    /// <summary>A resolved <c>[classPtr + offset]</c> read: the field it names, or the vtable slot.</summary>
    public readonly record struct FieldRead(
        LocalVariable ClassLocal,
        TypeAnalysisContext? Class,
        Il2CppClassUsefulOffsets.Il2CppClassField? Field,
        int? VTableSlot,
        MemoryOperand Load);

    /// <summary>
    /// If <paramref name="operand"/> is a load at an Il2CppClass field offset off a class pointer,
    /// return the named field it reads (or the vtable slot it indexes).
    /// </summary>
    public static FieldRead? TryRead(IOperand operand, float metadataVersion, bool is32Bit,
        DefUseIndex? index = null, Instruction? use = null)
    {
        if (operand is not MemoryOperand { Index: null, Scale: 0, Base: LocalVariable classLocal } load)
            return null;

        TypeAnalysisContext? klass = null;
        if (index != null)
            klass = RepresentedClass(classLocal, index, use);

        if (Il2CppClassUsefulOffsets.TryGetField((uint)load.Addend, metadataVersion, is32Bit,
                out var field, out _))
            return new FieldRead(classLocal, klass, field, null, load);

        var slot = Il2CppClassUsefulOffsets.GetVTableSlot(load.Addend, metadataVersion, is32Bit);
        return slot == null ? null : new FieldRead(classLocal, klass, null, slot, load);
    }

    public static bool SameType(TypeAnalysisContext left, TypeAnalysisContext right) =>
        ReferenceEquals(left, right)
        || left.FullName == right.FullName
        && ReferenceEquals(left.DeclaringAssembly, right.DeclaringAssembly);
}
