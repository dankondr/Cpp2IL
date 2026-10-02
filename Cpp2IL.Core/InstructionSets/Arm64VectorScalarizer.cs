using System;
using System.Collections.Generic;
using Cpp2IL.Core.ISIL;
using Disarm;
using Disarm.InternalDisassembly;

namespace Cpp2IL.Core.InstructionSets;

/// <summary>
/// Scalarizes lane-wise integer SIMD chains that would otherwise surface as
/// "DUP vector broadcast is not supported" plus a tail of UNIMPLEMENTED
/// instructions, or as whole-register pseudo-ops that silently miscompute
/// individual lanes.
///
/// For every SIMD register the pass tracks four 32-bit lane windows. A window
/// is proven when an ISIL local exists holding exactly that window's bits: an
/// element local like "V0.S1" written by INS/DUP/lane ops, a 64-bit element
/// local like "V0.D0" covering two windows, the whole register local when it
/// holds a plain scalar (FMOV/LDR/MOVI), or a constant.
///
/// A lane-wise op folds into scalar ISIL on those operands only when every
/// consumed window of every vector input is proven; wraparound, lane width and
/// signedness are preserved because each emitted op carries the lane's real
/// bit width. Opaque or unsupported vector ops leave the corresponding
/// windows unproven. At a branch target the incoming edges merge window by
/// window — a window survives only when every converted predecessor proves
/// it, materialized into its canonical element register, while a backward
/// edge leaves everything unproven. At an unproven consumption the pass
/// emits an explicit NotImplemented diagnostic instead of guessing.
///
/// Whole-vector loads (LDR/LDUR/LDP of V registers) are dual provenance: the
/// caller's normal path materializes the register local, and plainly
/// offset-addressed forms additionally materialize each 32-bit window as an
/// element local — so lane ops on freshly loaded vectors fold to real scalar
/// math, while full-width stores keep reading the register local.
/// Registers that never acquired lane state (LD1 results, UnityVector4
/// results, float pipelines, stack-addressed vectors) fall through to the
/// caller's normal path so previously emitted IL is unchanged. BIC/BIF/BSL
/// bit-select forms are likewise left alone so the existing Vector4
/// comparison recovery keeps working.
/// </summary>
internal sealed class Arm64VectorScalarizer
{
    /// <summary>
    /// One proven 32-bit window of a vector register: the window's value is the
    /// low 32 bits of <see cref="Operand"/> shifted right by <see cref="BitOffset"/>.
    /// </summary>
    private readonly record struct LaneSlice(IOperand Operand, int BitOffset);

    private sealed class VectorState
    {
        /// <summary>Slots[i] covers register bits [32*i, 32*i+32); null = unproven.</summary>
        public readonly LaneSlice?[] Slots = new LaneSlice?[4];

        /// <summary>
        /// The whole-register local currently holds this register's value:
        /// set by whole-vector loads (LDR/LDUR/LDP/LD1 of V registers) whose
        /// normal-path emission materializes it, cleared by any lane-level
        /// write. Lets a full-width store fall back to the register read.
        /// </summary>
        public bool Whole
        {
            get => _whole;
            set
            {
                _whole = value;
                if (!value)
                    LoadMemory = null;
            }
        }
        private bool _whole;

        /// <summary>
        /// The memory a whole-register load copied this register's value from,
        /// when the load was a plain offset-addressed LDR/LDUR/LDP/LD1. Lets a
        /// later store of the same register emit a memory-to-memory copy, which
        /// resolves the aggregate on both sides instead of reading a
        /// lane-typed local at the destination's width.
        /// </summary>
        public MemoryOperand? LoadMemory;

        /// <summary>
        /// Any lane window write invalidates the load provenance: the register
        /// no longer holds exactly what that memory held.
        /// </summary>
        public void SetSlot(int slot, LaneSlice? slice)
        {
            Slots[slot] = slice;
            SlotConstants[slot] = slice is { } s && IsSlotConstant(s) ? SlotConstantBits(s) : null;
            LoadMemory = null;
            Loaded = false;
        }

        /// <summary>
        /// Sets a slot to a slice whose runtime value is a known constant —
        /// e.g. a canonical element register just written with a literal.
        /// </summary>
        public void SetConstantSlot(int slot, LaneSlice slice, ulong constantBits)
        {
            Slots[slot] = slice;
            SlotConstants[slot] = constantBits;
            LoadMemory = null;
            Loaded = false;
        }

        /// <summary>
        /// The 32-bit constant the slot provably holds on this path: the
        /// slice's own literal, or the constant its canonical element
        /// register was last written with. Null for an unproven or
        /// non-constant slot.
        /// </summary>
        public ulong? WindowConstant(int slot)
            => Slots[slot] != null ? SlotConstants[slot] : null;

        /// <summary>
        /// Constant bits parallel to <see cref="Slots"/>: canonicalization
        /// rewrites a literal lane into its element register, and merges
        /// canonicalize proven slots, so the literal travels here instead —
        /// a wide zero/constant store still sees the real bits.
        /// </summary>
        public readonly ulong?[] SlotConstants = new ulong?[4];

        /// <summary>
        /// The register's normalized name ("V0"), set when the state is
        /// created — lets a consumer recover the whole-register local when
        /// <see cref="Whole"/> says it is current.
        /// </summary>
        public string? Name;

        /// <summary>
        /// The register local's current materialization came from a memory
        /// load on every path reaching this point: its lane slices spell
        /// windows of that load, so a store of the register resolves as the
        /// covered fields — not as one wide value the load happened to pack.
        /// </summary>
        public bool Loaded;

        /// <summary>
        /// Low bits of the register local that provably hold this register's
        /// current value on every path reaching the state's point: 128 for a
        /// whole-vector load, the scalar width for an FMOV/LDR of S or D, 32
        /// after the scalar-view sync Move, 0 for lane-built vectors. A read
        /// of the register local wider than this is either undefined (no
        /// write on some path) or wrong (a lane-only value). Reads are gated
        /// on it so an unwritten lane stays diagnosed instead of silently
        /// mislifting.
        /// </summary>
        public int MaterializedBits;

        public VectorState Clone()
        {
            var clone = new VectorState
            {
                Whole = Whole, Name = Name, LoadMemory = LoadMemory,
                MaterializedBits = MaterializedBits, Loaded = Loaded
            };
            Array.Copy(Slots, clone.Slots, Slots.Length);
            Array.Copy(SlotConstants, clone.SlotConstants, SlotConstants.Length);
            return clone;
        }
    }

    private readonly Dictionary<string, VectorState> _vectors = new();
    /// <summary>
    /// Registers whose tracked state was dropped by an opaque control-flow
    /// event (a call's clobber, an undecodable write). An untracked register
    /// may still read its local — a caller-emitted write or an argument's
    /// provenance defined it — but a clobbered one would read a stale value
    /// with no diagnostic, so untracked reads are refused for these names.
    /// </summary>
    private readonly HashSet<string> _clobbered = new();

    /// <summary>
    /// Per-name <see cref="VectorState.MaterializedBits"/> snapshotted at
    /// instruction start. A write inside the instruction (a claimed
    /// destination) updates the live value for the <i>next</i> instruction's
    /// reads; reads in the same instruction see the pre-write register local,
    /// so they must consult this snapshot instead.
    /// </summary>
    private readonly Dictionary<string, int> _preMaterialized = new();

    /// <summary>
    /// Whole register locals the caller's normal path wrote with a plain Move
    /// this instruction. A lane-op fallback emits arithmetic on the local
    /// (Multiply for an unscalarized FMUL): that value is not the register's
    /// lane tuple, so only a Move counts as materializing it.
    /// </summary>
    private readonly HashSet<string> _emittedVectorMoves = new();
    private readonly Dictionary<string, Register> _shiftTemps = new();
    private readonly HashSet<ulong> _mergeTargets = new();
    private readonly HashSet<string> _claimedDests = new();

    /// A lane-copy origin: SyncScalarView and scalar FMOV moves leave the
    /// register local holding a lane of another operand — record which operand,
    /// so a paired store of two lanes can name the one value they came from.
    /// Entries keyed by register name (vector and element registers alike).
    private readonly Dictionary<string, IOperand> _copySource = new();
    private int _tempCounter;
    private bool _clearProvenanceNext;

    /// <summary>
    /// AAPCS64: a call clobbers V0-V7 and V16-V31, and the upper halves of
    /// callee-saved V8-V15 — their low 64 bits, and any tracked lanes that
    /// live there, survive.
    /// </summary>
    private void ClobberCall()
    {
        var dropped = new List<string>();
        foreach (var pair in _vectors)
        {
            var name = pair.Key;
            var state = pair.Value;
            var reg = name is ['V', ..] && int.TryParse(name[1..], out var n) ? n : -1;
            if (reg is >= 8 and <= 15)
            {
                state.SetSlot(2,  null);
                state.SetSlot(3,  null);
                state.Whole = false;
                // the call keeps the callee-saved low 64 bits
                state.MaterializedBits = Math.Min(state.MaterializedBits, 64);
            }
            else
                dropped.Add(name);
        }
        foreach (var name in dropped)
            _vectors.Remove(name);
        _clobbered.UnionWith(dropped);
        // the call lands its result in V0: the caller's Move materializes the
        // register local at scalar width, while every lane stays opaque.
        if (dropped.Contains("V0"))
        {
            _vectors["V0"] = new VectorState { Name = "V0", MaterializedBits = 32 };
            _clobbered.Remove("V0");
        }
    }

    /// <summary>Branch instruction addresses that target each merge point.</summary>
    private readonly Dictionary<ulong, List<ulong>> _mergePreds = new();

    /// <summary>Merge targets also reached by falling through from the previous instruction.</summary>
    private readonly HashSet<ulong> _mergeFallThrough = new();

    /// <summary>Address of each instruction's recorded intra-method branch target.</summary>
    private readonly Dictionary<ulong, ulong> _branchTargets = new();

    /// <summary>The method's instruction stream, kept for loop-span scans.</summary>
    private IReadOnlyList<Arm64Instruction> _instructions = [];

    /// <summary>
    /// Instructions some control-flow path can reach: bytes after an
    /// unconditional branch or return are dead code — a literal pool or a
    /// tail-shared sequence — and are no predecessor of the merge target that
    /// follows them.
    /// </summary>
    private readonly HashSet<ulong> _reachable = new();

    /// <summary>
    /// Lane state snapshot taken at a branch instruction — the value one
    /// incoming edge hands to the merge its target reaches.
    /// </summary>
    private readonly Dictionary<ulong, Dictionary<string, VectorState>> _edgeExit = new();

    /// <summary>Address of the previously converted instruction.</summary>
    private ulong _prevAddress;

    private Func<ulong, OpCode, List<IOperand>, Instruction> _add = null!;
    private ulong _address;
    private bool _emitted;

    private static readonly Immediate Zero = new(0, 8);

    // Bytes an extraction still proves: the source's own count minus the bytes
    // shifted past, capped at the extraction width.
    private static int ExtractedProvenBytes(Immediate source, int droppedBits, int widthBytes)
        => Math.Clamp(source.EffectiveProvenBytes - droppedBits / 8, 0, widthBytes);

    private static string Normalize(Arm64Register reg) => reg switch
    {
        >= Arm64Register.V0 and <= Arm64Register.V31 => "V" + (reg - Arm64Register.V0),
        >= Arm64Register.D0 and <= Arm64Register.D31 => "V" + (reg - Arm64Register.D0),
        >= Arm64Register.S0 and <= Arm64Register.S31 => "V" + (reg - Arm64Register.S0),
        >= Arm64Register.H0 and <= Arm64Register.H31 => "V" + (reg - Arm64Register.H0),
        >= Arm64Register.B0 and <= Arm64Register.B31 => "V" + (reg - Arm64Register.B0),
        _ => reg.ToString()
    };

    private static Register Reg(Arm64Register reg) => new(null, Normalize(reg));

    private static bool IsVectorRegister(Arm64Register reg) => reg
        is >= Arm64Register.V0 and <= Arm64Register.V31
            or >= Arm64Register.D0 and <= Arm64Register.D31
            or >= Arm64Register.S0 and <= Arm64Register.S31
            or >= Arm64Register.H0 and <= Arm64Register.H31
            or >= Arm64Register.B0 and <= Arm64Register.B31;

    private static bool IsGpr(Arm64Register reg) => reg
        is >= Arm64Register.W0 and <= Arm64Register.W31
            or >= Arm64Register.X0 and <= Arm64Register.X31;

    private static (int laneBits, int laneCount) Arrangement(Arm64ArrangementSpecifier specifier) => specifier switch
    {
        Arm64ArrangementSpecifier.EightB => (8, 8),
        Arm64ArrangementSpecifier.SixteenB => (8, 16),
        Arm64ArrangementSpecifier.FourH => (16, 4),
        Arm64ArrangementSpecifier.EightH => (16, 8),
        Arm64ArrangementSpecifier.TwoS => (32, 2),
        Arm64ArrangementSpecifier.FourS => (32, 4),
        Arm64ArrangementSpecifier.OneD => (64, 1),
        Arm64ArrangementSpecifier.TwoD => (64, 2),
        _ => (0, 0)
    };

    private static int ElementBits(Arm64VectorElement element) => element.Width switch
    {
        Arm64VectorElementWidth.B => 8,
        Arm64VectorElementWidth.H => 16,
        Arm64VectorElementWidth.S => 32,
        Arm64VectorElementWidth.D => 64,
        _ => 0
    };

    private static string ElementLetter(int laneBits) => laneBits switch
    {
        8 => "B",
        16 => "H",
        32 => "S",
        _ => "D"
    };

    private static Register ElementRegister(string vectorName, int laneBits, int index)
        => new(null, $"{vectorName}.{ElementLetter(laneBits)}{index}");

    private static bool IsBranch(Arm64Mnemonic mnemonic) => mnemonic is
        Arm64Mnemonic.B or Arm64Mnemonic.BC
        or Arm64Mnemonic.CBZ or Arm64Mnemonic.CBNZ
        or Arm64Mnemonic.TBZ or Arm64Mnemonic.TBNZ;

    /// <summary>
    /// Whether the instruction leaves the linear flow with no fall-through:
    /// returns, register-indirect branches and unconditional immediate
    /// branches. Disarm decodes an ordinary <c>b.cond</c> with the same
    /// <see cref="Arm64Mnemonic.B"/> mnemonic as an unconditional branch —
    /// only the conditional-branch category distinguishes the two.
    /// </summary>
    private static bool IsUnconditionalExit(Arm64Instruction insn) =>
        insn.Mnemonic is Arm64Mnemonic.BR
            or Arm64Mnemonic.RET or Arm64Mnemonic.RETAA or Arm64Mnemonic.RETAB
        || (insn.Mnemonic == Arm64Mnemonic.B
            && insn.MnemonicCategory == Arm64MnemonicCategory.Branch);

    /// <summary>Whether the instruction passes control to the next one in address order.</summary>
    private static bool FallsThrough(Arm64Instruction insn) => !IsUnconditionalExit(insn);

    /// <summary>
    /// Called once per method before conversion. Records every intra-method
    /// branch target so lane provenance can be merged there window by window,
    /// and remembers which branch instructions feed each target.
    /// </summary>
    public void Begin(IReadOnlyList<Arm64Instruction> instructions)
    {
        _vectors.Clear();
        _clobbered.Clear();
        _shiftTemps.Clear();
        _mergeTargets.Clear();
        _mergePreds.Clear();
        _mergeFallThrough.Clear();
        _branchTargets.Clear();
        _reachable.Clear();
        _edgeExit.Clear();
        _claimedDests.Clear();
        _copySource.Clear();
        _tempCounter = 0;
        _clearProvenanceNext = false;
        _prevAddress = 0;
        _instructions = instructions;

        foreach (var insn in instructions)
        {
            ulong? target = insn.Mnemonic switch
            {
                Arm64Mnemonic.B => insn.BranchTarget,
                Arm64Mnemonic.BC => insn.Op0PcRelImm,
                Arm64Mnemonic.CBZ or Arm64Mnemonic.CBNZ => (ulong)((long)insn.Address + insn.Op1Imm),
                Arm64Mnemonic.TBZ or Arm64Mnemonic.TBNZ => (ulong)((long)insn.Address + insn.Op2Imm),
                _ => null
            };
            if (target is not { } t)
                continue;
            _mergeTargets.Add(t);
            _branchTargets[insn.Address] = t;
            if (!_mergePreds.TryGetValue(t, out var preds))
                _mergePreds[t] = preds = [];
            preds.Add(insn.Address);
        }

        if (instructions.Count > 0)
            _reachable.Add(instructions[0].Address);
        for (var changed = true; changed;)
        {
            changed = false;
            for (var i = 0; i < instructions.Count; i++)
            {
                var insn = instructions[i];
                if (!_reachable.Contains(insn.Address))
                    continue;
                if (_branchTargets.TryGetValue(insn.Address, out var branchTarget)
                    && _reachable.Add(branchTarget))
                    changed = true;
                if (i + 1 < instructions.Count && FallsThrough(insn)
                    && _reachable.Add(instructions[i + 1].Address))
                    changed = true;
            }
        }

        for (var i = 1; i < instructions.Count; i++)
            if (_mergeTargets.Contains(instructions[i].Address)
                && FallsThrough(instructions[i - 1])
                && _reachable.Contains(instructions[i - 1].Address))
                _mergeFallThrough.Add(instructions[i].Address);
    }

    /// <summary>
    /// Called before each instruction is converted. At a branch target the
    /// incoming edges are merged window by window: every proven window is
    /// materialized into its canonical element register on the edges that need
    /// it, and a window survives only when every converted predecessor proves
    /// it — an edge from a not-yet-converted (backward) branch leaves it
    /// unproven. The same applies after any control-flow instruction whose
    /// effect on registers cannot be tracked (calls clobber V0-V7 and V16-V31,
    /// indirect jumps cannot be enumerated). At a branch instruction every
    /// proven window is first canonicalized so the edge carries element locals.
    /// </summary>
    public void BeginInstruction(Arm64Instruction insn,
        Func<ulong, OpCode, List<IOperand>, Instruction> add)
    {
        _claimedDests.Clear();
        _emittedVectorMoves.Clear();
        // A cached shift names its source by register, not by value: once the next
        // instruction may have redefined that register, the temporary holds the high
        // half of the old value. It is only reused within one instruction.
        _shiftTemps.Clear();
        InstallEmitter(add);
        // merge-edge materializations are stamped with the predecessor's
        // address so a branch's target lookup never lands on them
        _address = _prevAddress;
        if (_clearProvenanceNext)
        {
            _vectors.Clear();
            _clearProvenanceNext = false;
        }
        // Edge materialization reads the values the previous instruction left:
        // refresh the materialization snapshot before merges and branch-edge
        // canonicalization so a width its write just proved counts as readable.
        _preMaterialized.Clear();
        foreach (var (name, state) in _vectors)
            _preMaterialized[name] = state.MaterializedBits;
        if (_mergeTargets.Contains(insn.Address))
            MergeLanesAt(insn.Address);
        if (IsBranch(insn.Mnemonic))
        {
            CanonicalizeLanes();
            var exit = new Dictionary<string, VectorState>(_vectors.Count);
            foreach (var (name, state) in _vectors)
                exit[name] = state.Clone();
            _edgeExit[insn.Address] = exit;
        }
        _preMaterialized.Clear();
        foreach (var (name, state) in _vectors)
            _preMaterialized[name] = state.MaterializedBits;
        _prevAddress = insn.Address;
    }

    /// <summary>
    /// The register a window's value must live in to cross a control-flow
    /// edge. Window 0's canonical home is the register local itself: its low
    /// 32 bits are the lane, and keeping the lane in the local lets a scalar
    /// consumer read the phi'd register the way the field-recovery layer
    /// already resolves (a whole-register move reads the low window). Windows
    /// 1-3 canonically live in their element registers.
    /// </summary>
    private static Register CanonicalSlot(string name, int slot)
        => slot == 0 ? new Register(null, name) : ElementRegister(name, 32, slot);

    private static bool IsCanonical(string name, int slot, LaneSlice slice)
        => slice.BitOffset == 0
            && slice.Operand is Register { Name: var operandName }
            && operandName == CanonicalSlot(name, slot).Name;

    /// <summary>
    /// On a control-flow edge every proven window is materialized into its
    /// canonical element register: after this, a merge can name the window
    /// identically no matter which edge produced it, and SSA merges the element
    /// registers like any scalar. Windows are materialized top-down: writing
    /// window 0 into the register local would clobber the old register value
    /// that higher windows' shifts still need.
    /// </summary>
    private void CanonicalizeLanes()
    {
        foreach (var (name, state) in _vectors)
            for (var slot = 3; slot >= 0; slot--)
            {
                if (state.Slots[slot] is not { } slice || IsCanonical(name, slot, slice))
                    continue;
                if (SlotOperand(state, slot) is { } value)
                {
                    var canonicalMove = _add(_address, OpCode.Move, [CanonicalSlot(name, slot), value]);
                    // the move forwards a lane of unknown managed type:
                    // NativeFloatWriteBits records the write width without
                    // seeding Int32 — the lane's own type flows from its value
                    canonicalMove.NativeFloatWriteBits = 32;
                    ImmediateWriteWidth.ApplyToMove(canonicalMove);
                    _emitted = true;
                    // a literal lane stays constant through its canonical
                    // local — record the bits so wide stores still see zeroes
                    if (IsSlotConstant(slice))
                        state.SetConstantSlot(slot, new LaneSlice(CanonicalSlot(name, slot), 0),
                            SlotConstantBits(slice));
                    else
                        state.SetSlot(slot,  new LaneSlice(CanonicalSlot(name, slot), 0));
                    if (slot == 0)
                        state.Whole = false;
                }
                else
                    state.SetSlot(slot,  null);
            }
    }

    /// <summary>
    /// Meets the incoming edges of a branch target window by window. A window
    /// that every predecessor proves becomes the canonical element register —
    /// written on the fall-through edge here if that path does not already
    /// carry it, already canonical on branch edges (their ends canonicalize).
    /// A predecessor that has not been converted yet — a backward edge — makes
    /// every window unproven: nothing is guessed.
    /// </summary>
    private void MergeLanesAt(ulong target)
    {
        var fallThrough = _mergeFallThrough.Contains(target) ? _vectors : null;
        List<Dictionary<string, VectorState>>? branchEdges = null;
        var backwardEdge = false;
        if (_mergePreds.TryGetValue(target, out var predAddresses))
        {
            branchEdges = new(predAddresses.Count);
            foreach (var pred in predAddresses)
            {
                if (!_reachable.Contains(pred))
                    continue; // dead bytes can branch here but carry no live state
                if (_edgeExit.TryGetValue(pred, out var exit))
                    branchEdges.Add(exit);
                else
                    backwardEdge = true;
            }
        }
        var merged = new Dictionary<string, VectorState>();
        var names = new HashSet<string>();
        if (fallThrough != null)
            names.UnionWith(fallThrough.Keys);
        if (branchEdges != null)
            foreach (var edge in branchEdges)
                names.UnionWith(edge.Keys);

        // A predecessor that has not been converted yet (a loop back-edge)
        // carries lane values this pass never saw. A register no instruction
        // in the loop writes is loop-invariant: its back-edge hands the
        // header's own merged value back, so meeting the converted edges is
        // the fixpoint. A name the loop may write — or an inner merge or a
        // call can clobber — stays fully unproven: nothing is guessed.
        var loopWritten = backwardEdge ? LoopWrittenRegisters(target) : null;
        var allUnproven = backwardEdge && loopWritten == null;

        {
            foreach (var name in names)
            {
                if (allUnproven || loopWritten is { } loopWrites && loopWrites.Contains(name))
                {
                    merged[name] = new VectorState { Name = name };
                    continue;
                }
                var state = new VectorState { Name = name };
                var window0Clobbered = false;
                // top-down like CanonicalizeLanes: materializing window 0
                // into the register local first would clobber the old value
                // that higher windows' shifts still read
                for (var slot = 3; slot >= 0; slot--)
                {
                    // an edge that never wrote the register contributes no
                    // slice: naming an element local here would let a
                    // consumer read a local that edge never defined — the
                    // merge stays honest and leaves the window unproven
                    var proven = fallThrough == null
                        || fallThrough.TryGetValue(name, out var live) && live.Slots[slot] != null;
                    if (proven && branchEdges != null)
                        foreach (var edge in branchEdges)
                            proven &= edge.TryGetValue(name, out var exit) && exit.Slots[slot] != null;
                    if (!proven)
                        continue;

                    var canonical = CanonicalSlot(name, slot);
                    if (fallThrough != null
                        && fallThrough.TryGetValue(name, out var liveState)
                        && liveState.Slots[slot] is { } liveSlice
                        && !IsCanonical(name, slot, liveSlice)
                        && SlotOperand(liveState, slot) is { } value)
                    {
                        var canonicalMove = _add(_address, OpCode.Move, [canonical, value]);
                        canonicalMove.NativeFloatWriteBits = 32;
                        ImmediateWriteWidth.ApplyToMove(canonicalMove);
                        // writing window 0 into the register local replaces
                        // the whole-register value it held
                        if (slot == 0)
                            window0Clobbered = true;
                    }
                    // a lane holding the same constant on every edge keeps
                    // it — wide stores still see zeroes behind a canonical local
                    ulong? constant = null;
                    var constantFirst = true;
                    void MeetConstant(Dictionary<string, VectorState> edge)
                    {
                        var edgeConstant = edge.TryGetValue(name, out var edgeState)
                            ? edgeState.WindowConstant(slot)
                            : null;
                        if (constantFirst)
                        {
                            constant = edgeConstant;
                            constantFirst = false;
                        }
                        else if (edgeConstant != constant)
                            constant = null;
                    }
                    if (fallThrough != null)
                        MeetConstant(fallThrough);
                    if (branchEdges != null)
                        foreach (var edge in branchEdges)
                            MeetConstant(edge);
                    if (constant is { } bits)
                        state.SetConstantSlot(slot, new LaneSlice(canonical, 0), bits);
                    else
                        state.SetSlot(slot,  new LaneSlice(canonical, 0));
                }
                var whole = fallThrough == null
                    || (fallThrough.TryGetValue(name, out var wholeState) && wholeState.Whole);
                if (whole && branchEdges != null)
                    foreach (var edge in branchEdges)
                        whole &= edge.TryGetValue(name, out var exit) && exit.Whole;
                state.Whole = whole && !window0Clobbered;
                // a register-local read is proven only where every incoming
                // edge materialized those bits — the minimum survives a merge
                var materialized = fallThrough == null
                    ? int.MaxValue
                    : fallThrough.TryGetValue(name, out var materializedState)
                        ? materializedState.MaterializedBits
                        : 0;
                if (branchEdges != null)
                    foreach (var edge in branchEdges)
                        materialized = Math.Min(materialized,
                            edge.TryGetValue(name, out var edgeState) ? edgeState.MaterializedBits : 0);
                state.MaterializedBits = Math.Max(
                    materialized == int.MaxValue ? 0 : materialized, whole ? 128 : 0);
                // load provenance survives only where every reaching edge
                // still holds the register's bytes from a load
                var loaded = fallThrough == null
                    || (fallThrough.TryGetValue(name, out var loadedState) && loadedState.Loaded);
                if (loaded && branchEdges != null)
                    foreach (var edge in branchEdges)
                        loaded &= edge.TryGetValue(name, out var exit) && exit.Loaded;
                state.Loaded = loaded;
                // a name live on any edge stays tracked even when no window is
                // proven: a lane consumer must diagnose rather than read an
                // element local no edge materialized
                merged[name] = state;
            }
        }

        _vectors.Clear();
        foreach (var (name, state) in merged)
            _vectors[name] = state;
    }

    /// <summary>
    /// Register names the unconverted predecessors of a loop header may
    /// write: scans every instruction in (target, lastBackEdgeSource] —
    /// a destination-register write, a call's clobber, or a reachable inner
    /// merge that can meet provenance away all count. Null when no
    /// unconverted edge remains (the merge degenerates to the usual case).
    /// </summary>
    private HashSet<string>? LoopWrittenRegisters(ulong target)
    {
        if (!_mergePreds.TryGetValue(target, out var preds))
            return null;
        var hi = 0UL;
        foreach (var pred in preds)
            if (_reachable.Contains(pred) && !_edgeExit.ContainsKey(pred) && pred > hi)
                hi = pred;
        if (hi == 0)
            return null;

        var written = new HashSet<string>();
        foreach (var insn in _instructions)
        {
            // the merge target's own instruction executes inside the loop
            // too — its writes reach the back-edge like every other body's
            if (insn.Address < target || !_reachable.Contains(insn.Address))
                continue;
            if (insn.Address > hi)
                break;
            if ((insn.Address != target && _mergeTargets.Contains(insn.Address))
                || insn.Mnemonic is Arm64Mnemonic.BL or Arm64Mnemonic.BLR
                || insn.Op0Kind == Arm64OperandKind.None)
            {
                // an inner merge meets provenance away just like a write; a
                // call clobbers caller-saved vectors; an undecoded word may
                // write anything — refuse invariance for every name
                for (var i = 0; i < 32; i++)
                    written.Add("V" + i);
                continue;
            }
            if (insn.Op0Kind != Arm64OperandKind.Register
                || insn.Mnemonic is Arm64Mnemonic.FCMP or Arm64Mnemonic.FCMPE
                    or Arm64Mnemonic.FCCMP or Arm64Mnemonic.FCCMPE
                || insn.Mnemonic.ToString().StartsWith("ST", StringComparison.Ordinal))
                continue; // compares set flags, stores read the register
            if (IsVectorRegister(insn.Op0Reg))
                written.Add(Normalize(insn.Op0Reg));
            // pair/multi-destination loads also write the second register
            if (insn.Op1Kind == Arm64OperandKind.Register && IsVectorRegister(insn.Op1Reg)
                && insn.Mnemonic.ToString().StartsWith("LD", StringComparison.Ordinal))
                written.Add(Normalize(insn.Op1Reg));
        }
        return written;
    }

    /// true when the instruction was fully handled — folded to lane ops or
    /// reported via an explicit diagnostic — and false when the caller should
    /// run its normal lowering path.
    /// </summary>
    public bool TryConvert(Arm64Instruction insn,
        Func<ulong, OpCode, List<IOperand>, Instruction> add,
        Func<Arm64Instruction, int, IOperand> convertOperand)
    {
        InstallEmitter(add);
        _address = insn.Address;
        _emitted = false;

        var handled = TryConvertCore(insn, convertOperand);
        if (handled && !_emitted)
            _add(_address, OpCode.Nop, []);
        return handled;
    }

    /// <summary>
    /// Provenance maintenance for instructions the caller's normal path just
    /// emitted. Scalar-defining whole-register writes (narrow loads) prove
    /// windows; any other write to a tracked vector poisons its lanes.
    /// </summary>
    public void NoteUnhandled(Arm64Instruction insn)
    {
        // Anything that can transfer control out of this instruction's linear
        // flow invalidates lane state at the next instruction: a call clobbers
        // argument/temporary vector registers and may write the V0 result, an
        // indirect jump's targets cannot be enumerated, and bytes following an
        // unconditional branch or return are not this path's code.
        if (insn.Mnemonic is Arm64Mnemonic.BL or Arm64Mnemonic.BLR)
            ClobberCall();
        else if (IsUnconditionalExit(insn))
            _clearProvenanceNext = true;

        // stores read the register rather than writing it — no invalidation
        if (insn.Mnemonic is Arm64Mnemonic.STR or Arm64Mnemonic.STUR or Arm64Mnemonic.STP
            or Arm64Mnemonic.STRB or Arm64Mnemonic.STRH or Arm64Mnemonic.STURB or Arm64Mnemonic.STURH
            or Arm64Mnemonic.ST1 or Arm64Mnemonic.ST2 or Arm64Mnemonic.ST3 or Arm64Mnemonic.ST4
            or Arm64Mnemonic.STNP)
            return;

        var name = insn.Op0Kind is Arm64OperandKind.Register or Arm64OperandKind.VectorRegisterElement
            ? Normalize(insn.Op0Reg)
            : null;
        if (name != null && _claimedDests.Remove(name))
            return; // lane state was already written by this pass

        if (insn.Op0Kind == Arm64OperandKind.VectorRegisterElement)
        {
            // an element write we did not claim rewrites one lane window; the
            // register local itself is untouched, so a clobber stays clobbered
            var element = insn.Op0VectorElement;
            var elementName = Normalize(insn.Op0Reg);
            if (!_vectors.TryGetValue(elementName, out var elementState))
                _vectors[elementName] = elementState = new() { Name = elementName };
            elementState.SetSlot(ElementBits(element) * element.Index / 32,  null);
            elementState.Whole = false;
            return;
        }

        if (insn.Op0Kind == Arm64OperandKind.None)
        {
            // no identifiable destination: undecoded words (UNIMPLEMENTED) or
            // exotic forms may still write any vector register — drop all
            // provenance rather than fold against stale lanes
            _vectors.Clear();
            for (var i = 0; i < 32; i++)
                _clobbered.Add($"V{i}");
            return;
        }

        if (insn.Op0Kind != Arm64OperandKind.Register || !IsVectorRegister(insn.Op0Reg))
            return;

        // Op0 read without a write leaves the register's provenance intact:
        // compares only set the flags, and stores move the register's value
        // out. Ensuring state or clearing lanes on either would fabricate a
        // write and wipe the real one.
        if (insn.Mnemonic is Arm64Mnemonic.FCMP or Arm64Mnemonic.FCMPE
                or Arm64Mnemonic.FCCMP or Arm64Mnemonic.FCCMPE
            || insn.Mnemonic.ToString().StartsWith("ST", StringComparison.Ordinal))
            return;

        if (WholeVectorLoad(insn))
        {
            // plainly offset-addressed loads also materialize each 32-bit window
            // as its own element local, so downstream lane ops see real
            // provenance instead of an opaque blob.
            var windowed = insn.Mnemonic != Arm64Mnemonic.LD1
                && insn.MemIndexMode == Arm64MemoryIndexMode.Offset
                && insn.MemAddendReg == Arm64Register.INVALID
                && insn.MemBase != Arm64Register.INVALID;
            // pre/post-indexed loads run at the unindexed base — MemOffset is
            // the writeback, not the addend — so provenance records offset 0
            var loadOff = insn.MemIndexMode == Arm64MemoryIndexMode.Offset ? insn.MemOffset : 0;
            RecordVectorLoad(insn, insn.Op0Reg, loadOff, windowed);
            if (insn.Mnemonic is Arm64Mnemonic.LDP or Arm64Mnemonic.LD1
                && insn.Op1Kind == Arm64OperandKind.Register && IsVectorRegister(insn.Op1Reg))
            {
                RecordVectorLoad(insn, insn.Op1Reg, loadOff + 16, windowed);
            }
            return;
        }

        if (ScalarWholeRegisterWrite(insn, out var writtenBits))
        {
            var state = Ensure(insn.Op0Reg);
            for (var i = 0; i < 4; i++)
                state.SetSlot(i,  32 * i < writtenBits ? new LaneSlice(Reg(insn.Op0Reg), 32 * i) : new LaneSlice(Zero, 0));
            state.Whole = false; // the local now holds only the narrow scalar
            state.Loaded = insn.Mnemonic is Arm64Mnemonic.LDR or Arm64Mnemonic.LDUR or Arm64Mnemonic.LDP;
            state.MaterializedBits = writtenBits;
            _clobbered.Remove(Normalize(insn.Op0Reg));
            ClearCopyOrigin(Normalize(insn.Op0Reg));
            if (insn.Mnemonic is Arm64Mnemonic.LDR or Arm64Mnemonic.LDUR or Arm64Mnemonic.LDP
                && insn.MemBase is not (Arm64Register.INVALID or Arm64Register.X31)
                && insn.MemIndexMode == Arm64MemoryIndexMode.Offset
                && IsArgumentBase(insn.MemBase))
                state.LoadMemory = new MemoryOperand(Reg(insn.MemBase), addend: insn.MemOffset,
                    accessSize: writtenBits / 8);

            // the second destination of a paired load (LDP S/D) follows the
            // same narrow-write rule as Op0 — otherwise its state goes stale
            if (insn.Mnemonic == Arm64Mnemonic.LDP
                && insn.Op1Kind == Arm64OperandKind.Register
                && IsVectorRegister(insn.Op1Reg))
            {
                var secondBits = RegisterBytes(insn.Op1Reg) * 8;
                if (secondBits > 0)
                {
                    var second = Ensure(insn.Op1Reg);
                    for (var i = 0; i < 4; i++)
                        second.SetSlot(i,  32 * i < secondBits ? new LaneSlice(Reg(insn.Op1Reg), 32 * i) : new LaneSlice(Zero, 0));
                    second.Whole = false;
                    second.Loaded = true;
                    second.MaterializedBits = secondBits;
                    _clobbered.Remove(Normalize(insn.Op1Reg));
                    if (insn.MemBase is not (Arm64Register.INVALID or Arm64Register.X31)
                        && insn.MemIndexMode == Arm64MemoryIndexMode.Offset
                        && IsArgumentBase(insn.MemBase))
                        second.LoadMemory = new MemoryOperand(Reg(insn.MemBase),
                            addend: insn.MemOffset + secondBits / 8, accessSize: secondBits / 8);
                }
            }
            return;
        }

        // Any other vector-register write the caller emits as a whole-register
        // Move/Op: lanes stay opaque, but the register local does hold the
        // result — an opaque state keeps reads of it provable at its width.
        var opaque = Ensure(insn.Op0Reg);
        _clobbered.Remove(name!);
        for (var i = 0; i < 4; i++)
            opaque.SetSlot(i,  null); // opaque write: lanes no longer provable
        opaque.Whole = false;
        // A scalar-width destination's normal-path write — any opcode — makes
        // the local hold the register's value (a scalar Add or Select on the
        // local is the hardware's scalar result). A vector-wide destination
        // only when the caller emitted a Move: its lane-op fallbacks (Multiply
        // for an unscalarized FMUL) compute arithmetic that is not the lane
        // tuple — reads of it as the register's value must stay unproven.
        opaque.MaterializedBits = RegisterBytes(insn.Op0Reg) <= 8
            || _emittedVectorMoves.Contains(Normalize(insn.Op0Reg))
            ? RegisterBytes(insn.Op0Reg) * 8
            : 0;
    }

    private VectorState? State(Arm64Register reg)
        => _vectors.TryGetValue(Normalize(reg), out var state) ? state : null;

    /// <summary>
    /// State for lane-level consumers: at least one proven 32-bit window. A
    /// register whose only provenance is a whole-register materialization has
    /// no lane state at all, so consumers see it as opaque and leave it to the
    /// caller's normal path.
    /// </summary>
    private VectorState? LaneState(Arm64Register reg)
    {
        var state = State(reg);
        if (state == null)
            return null;
        for (var i = 0; i < state.Slots.Length; i++)
            if (state.Slots[i] != null)
                return state;
        return null;
    }

    private VectorState Ensure(Arm64Register reg)
    {
        var name = Normalize(reg);
        if (!_vectors.TryGetValue(name, out var state))
            _vectors[name] = state = new() { Name = name };
        return state;
    }

    /// <summary>
    /// Mark <paramref name="reg"/> as this instruction's destination. A lane
    /// write leaves the whole-register local stale; a partial write at bit
    /// <paramref name="staleFromBit"/> keeps the bits below it provable.
    /// </summary>
    private void ClaimDest(Arm64Register reg, int staleFromBit = 0)
    {
        var name = Normalize(reg);
        _claimedDests.Add(name);
        ClearCopyOrigin(name);
        if (_vectors.TryGetValue(name, out var state))
        {
            state.Whole = false;
            state.MaterializedBits = Math.Min(state.MaterializedBits, staleFromBit);
        }
    }

    /// <summary>
    /// An overwrite makes every local of the register self-valued again, and
    /// invalidates copies whose source register just changed value.
    /// </summary>
    private void ClearCopyOrigin(string name)
    {
        _copySource.Remove(name);
        var stale = new List<string>();
        foreach (var (key, value) in _copySource)
            if (key.StartsWith(name + ".") || ReferencesRegister(value, name))
                stale.Add(key);
        foreach (var key in stale)
            _copySource.Remove(key);
    }

    private static bool ReferencesRegister(IOperand operand, string name)
        => operand is Register { Name: { } n } && (n == name || n.StartsWith(name + "."));

    /// <summary>
    /// Lane-copy provenance rides the emission stream: a Move into a vector
    /// register makes that register local the source's value; any other write
    /// makes it self-valued again.
    /// </summary>
    private void InstallEmitter(Func<ulong, OpCode, List<IOperand>, Instruction> add)
    {
        _add = (addr, op, ops) =>
        {
            var emitted = add(addr, op, ops);
            if (ops.Count != 0 && ops[0] is Register { Name: { } destName } && destName.StartsWith('V'))
            {
                if (op == OpCode.Move && ops.Count > 1)
                    _copySource[destName] = ops[1];
                else
                    _copySource.Remove(destName);
                if (op == OpCode.Move && !destName.Contains('.'))
                    _emittedVectorMoves.Add(destName);
            }
            return emitted;
        };
    }

    /// <summary>
    /// What a register local's value came from when the last write was a
    /// lane copy, else the operand itself.
    /// </summary>
    private IOperand CopyOrigin(IOperand operand)
        => operand is Register { Name: { } n } && _copySource.TryGetValue(n, out var origin)
            ? origin
            : operand;

    /// <summary>
    /// Records what a whole-vector load proved about <paramref name="reg"/>.
    /// Windowed loads emit one element-local Move per 32-bit window so lane
    /// ops and extracts can read real locals; other loads mark only the whole
    /// register local as current and leave every window unproven.
    /// </summary>
    private void RecordVectorLoad(Arm64Instruction insn, Arm64Register reg, long offset, bool windowed)
    {
        var state = Ensure(reg);
        _clobbered.Remove(Normalize(reg));
        if (!windowed)
        {
            for (var i = 0; i < 4; i++)
                state.SetSlot(i,  null); // lanes opaque, but the local itself is current
            state.Whole = true;
            state.Loaded = true;
            // the caller's normal-path Move writes the whole register local
            state.MaterializedBits = RegisterBytes(reg) * 8;
            if (insn.MemBase != Arm64Register.X31 && RegisterBytes(reg) is > 0 and var loadBytes
                && IsArgumentBase(insn.MemBase))
                state.LoadMemory = new MemoryOperand(Reg(insn.MemBase), addend: offset, accessSize: loadBytes);
            return;
        }

        var name = Normalize(reg);
        for (var i = 0; i < 4; i++)
        {
            var laneReg = ElementRegister(name, 32, i);
            IOperand mem = insn.MemBase == Arm64Register.X31
                ? new StackOffset((int)(offset + 4 * i))
                : new MemoryOperand(Reg(insn.MemBase), addend: offset + 4 * i, accessSize: 4);
            _add(_address, OpCode.Move, [laneReg, mem]).NativeMemoryAccessSize = 4;
            _emitted = true;
            state.SetSlot(i,  new LaneSlice(laneReg, 0));
        }
        state.Whole = true; // the caller's normal-path Move materialized Vn too
        state.Loaded = true;
        state.MaterializedBits = RegisterBytes(reg) * 8;
        if (insn.MemBase != Arm64Register.X31 && RegisterBytes(reg) is > 0 and var wholeBytes
            && IsArgumentBase(insn.MemBase))
            state.LoadMemory = new MemoryOperand(Reg(insn.MemBase), addend: offset, accessSize: wholeBytes);
    }

    /// <summary>
    /// Load provenance is kept only for argument-register bases: X0–X7 carry
    /// `this` and parameters, so a load through one is a managed field or
    /// element access the resolver can re-spell. A scratch-register base is
    /// usually a raw pointer whose memory-to-memory copy would only diagnose.
    /// </summary>
    private static bool IsArgumentBase(Arm64Register reg)
        => reg is >= Arm64Register.X0 and <= Arm64Register.X7;

    /// <summary>
    /// Low bits of the register local proven materialized for a name at the
    /// start of the current instruction: the snapshot for tracked registers,
    /// full width for a never-written one (a call-clobbered name excepted).
    /// Reads inside an instruction see the pre-write register local, so they
    /// must consult this snapshot — the live value already reflects the
    /// instruction's own claimed destination.
    /// </summary>
    private int MaterializedBitsOf(string name)
        => _preMaterialized.TryGetValue(name, out var bits) ? bits
            : !_clobbered.Contains(name) ? RegisterBytes(Arm64Register.V0) * 8 : 0;

    /// <summary>
    /// Whether an operand may be read for <paramref name="bits"/> bits of a
    /// stored or consumed value: element locals ("V0.S1"), temporaries and
    /// non-vector names are defined where their writer ran, but a whole
    /// register local is readable only up to the materialized width proven on
    /// every reaching path — otherwise the read lifts an unwritten lane or a
    /// stale value without a diagnostic.
    /// </summary>
    private bool RegisterReadable(IOperand operand, int bits)
        => operand is not Register { Name: { } name }
           || name.Contains('.')
           || !name.StartsWith('V')
           || MaterializedBitsOf(name) >= bits;

    private void Diagnostic(string message)
    {
        _add(_address, OpCode.NotImplemented, [new StringLiteral(message)]);
        _emitted = true;
    }

    private Register Temp()
    {
        _emitted = true;
        return new Register(null, $"TEMP_VEC{_tempCounter++}");
    }

    /// <summary>
    /// The operand whose value equals 32-bit window <paramref name="slot"/> of
    /// <paramref name="state"/>, or null when that window is unproven.
    /// Constants fold inline; a cached ShiftRight is materialized for windows
    /// above bit 32 of a wider operand.
    /// </summary>
    private IOperand? SlotOperand(VectorState? state, int slot)
    {
        if (state == null || state.Slots[slot] is not { } slice)
            return null;

        var (operand, offset) = slice;
        if (operand is Immediate imm)
            return new Immediate(unchecked((int)(uint)(imm.UnsignedValue >> offset)),
                ExtractedProvenBytes(imm, offset, 4));
        if (!RegisterReadable(operand, offset + 32))
            return null;
        if (offset == 0)
            return operand;

        var key = $"{operand}|{offset}";
        if (!_shiftTemps.TryGetValue(key, out var temp))
        {
            temp = Temp();
            _add(_address, OpCode.ShiftRight, [temp, operand, new Immediate(offset)]);
            _shiftTemps[key] = temp;
        }
        return temp;
    }

    /// <summary>The operand covering a whole 64-bit lane (two adjacent windows).</summary>
    private IOperand? Lane64Operand(VectorState state, int lane, bool floatRead = false)
    {
        var lo = state.Slots[2 * lane];
        var hi = state.Slots[2 * lane + 1];
        if (lo == null || hi == null)
            return null;

        // the register local is current — the low 64-bit lane is simply its
        // low half; compose per-window operands only for written states
        if (lane == 0 && state.Whole && state.Name is { } whole)
            return new Register(null, whole);

        // the register local provably holds the low 64 bits on every
        // reaching path — a full-width write, or a callee-saved register
        // surviving a call — so reading it *is* the lane, even when the
        // windows were split into element locals that no longer alias it
        if (lane == 0 && state.Name is { } name && MaterializedBitsOf(name) >= 64)
            return new Register(null, name);

        if (lo.Value.BitOffset == 0 && hi.Value.BitOffset == 32
            && lo.Value.Operand.Equals(hi.Value.Operand)
            && RegisterReadable(lo.Value.Operand, 64))
            return lo.Value.Operand; // one operand already covers the whole lane

        var loOp = SlotOperand(state, 2 * lane);
        var hiOp = SlotOperand(state, 2 * lane + 1);
        if (loOp == null || hiOp == null)
            return null;

        if (loOp is Immediate { } loImm && hiOp is Immediate { } hiImm)
            return floatRead
                ? new DoubleLiteral(BitConverter.Int64BitsToDouble(
                    (hiImm.Value << 32) | (loImm.Value & 0xFFFFFFFFL)))
                : new Immediate((hiImm.Value << 32) | (loImm.Value & 0xFFFFFFFFL), 8);

        // Compose in the 64-bit domain: a narrower carrier would truncate the
        // shifted high window outright. Widening converts (not marks) seed the
        // Int64 type the composition needs.
        var loWide = Temp();
        var loConvert = _add(_address, OpCode.Convert, [loWide, loOp]);
        loConvert.ConversionSourceWidthBits = 32;
        loConvert.ConversionUnsigned = true;
        loConvert.NativeIntegerWidthBits = 64;
        var hiWide = Temp();
        var hiConvert = _add(_address, OpCode.Convert, [hiWide, hiOp]);
        hiConvert.ConversionSourceWidthBits = 32;
        hiConvert.ConversionUnsigned = true;
        hiConvert.NativeIntegerWidthBits = 64;
        var hiShifted = Temp();
        _add(_address, OpCode.ShiftLeft, [hiShifted, hiWide, new Immediate(32)]);
        var composed = Temp();
        _add(_address, OpCode.Or, [composed, hiShifted, loWide]);
        if (!floatRead)
            return composed;
        // A scalar-FP consumer wants the double the bits mean, not the Int64
        // pattern: reinterpret so conversions and float ops see System.Double.
        var asDouble = Temp();
        var convert = _add(_address, OpCode.Convert, [asDouble, composed]);
        convert.ConversionFromFloat = true;
        convert.ConversionSourceWidthBits = 64;
        convert.NativeFloatWidthBits = 64;
        return asDouble;
    }

    /// <summary>
    /// The operand holding exactly the named element's bits, or null when the
    /// covering window is unproven. Sub-32-bit elements are extracted from
    /// their proven window with ShiftRight+And.
    /// </summary>
    private IOperand? ElementOperand(VectorState state, Arm64VectorElement element)
    {
        var bits = ElementBits(element);
        var offset = bits * element.Index;
        return bits switch
        {
            32 => SlotOperand(state, element.Index),
            64 => Lane64Operand(state, element.Index),
            8 or 16 => NarrowElementOperand(state, offset / 32, offset % 32, bits),
            _ => null
        };
    }

    /// <summary>
    /// Best operand for an element read on <paramref name="reg"/>: the proven
    /// window when the register is tracked, otherwise the register local
    /// itself for element 0 (the local holds the scalar a caller left in the
    /// low lane — an argument register or an FP pipeline result). A lane above
    /// window 0 on an untracked register is never provable: the signature can
    /// only place an argument's low lane there, so the read stays unproven
    /// (null) and the consumer diagnoses it at the instruction.
    /// </summary>
    private IOperand? ResolveElementSource(Arm64Register reg, Arm64VectorElement element)
        => ResolveLaneElement(reg, element);

    /// <summary>
    /// The operand a scalar read of <paramref name="reg"/> should use when the
    /// register is lane-tracked: the proven operand for the register's scalar
    /// width — window 0 for S, the composed 64-bit lane for D. Null when the
    /// register has no proven lane at its scalar width: the caller's
    /// register-local spelling then stands (untracked or unproven).
    /// </summary>
    public IOperand? ScalarLaneOperand(Arm64Register reg)
    {
        var state = LaneState(reg);
        if (state == null)
            return null;
        return RegisterBytes(reg) * 8 == 64
            ? Lane64Operand(state, 0, floatRead: true)
            : SlotOperand(state, 0);
    }

    /// <summary>
    /// Element read for lane-wise consumers: a tracked register's unproven
    /// window stays unproven (null) so the consuming lane reports it, while an
    /// untracked register resolves as in <see cref="ResolveElementSource"/>.
    /// </summary>
    private IOperand? ResolveLaneElement(Arm64Register reg, Arm64VectorElement element)
    {
        var state = State(reg);
        if (state == null)
            return ElementBits(element) * element.Index == 0
                   && !_clobbered.Contains(Normalize(reg)) ? Reg(reg) : null;
        return ElementOperand(state, element)
               ?? (MaterializedBitsOf(state.Name) >= ElementBits(element) * (element.Index + 1)
                   ? WholeRegisterElement(reg, ElementBits(element), element.Index, unsigned: false)
                   : state.Whole
                       ? WholeRegisterElement(reg, ElementBits(element), element.Index, unsigned: false)
                       : null);
    }

    /// <summary>
    /// Scalar-register reads (FADD Sd, Sn, Sm and friends) consult the register
    /// local. A lane-level write only materializes element locals, so the
    /// register local must be kept in sync with the lane-0 window it models,
    /// otherwise a scalar consumer would read a stale or unwritten local.
    /// </summary>
    private void SyncScalarView(VectorState dest, string name)
    {
        var slice = dest.Slots[0];
        if (slice == null || slice.Value.BitOffset != 0)
            return;
        if (slice.Value.Operand is Register { Name: var operandName } && operandName == name)
            return; // the register local already holds the lane-0 value
        _add(_address, OpCode.Move, [new Register(null, name), slice.Value.Operand])
            .NativeFloatWriteBits = 32;
        _emitted = true;
        // the register local now equals lane 0 — only the low 32 bits are
        // safe to read back through it
        dest.MaterializedBits = 32;
        _clobbered.Remove(name);
    }

    private IOperand? NarrowElementOperand(VectorState state, int slot, int offsetInSlot, int bits)
    {
        var slotOp = SlotOperand(state, slot);
        if (slotOp == null)
            return null;
        if (slotOp is Immediate { } slotImm)
            return new Immediate((int)(((uint)slotImm.Value >> offsetInSlot) & ((1u << bits) - 1)),
                ExtractedProvenBytes(slotImm, offsetInSlot, bits / 8));
        var shifted = slotOp;
        if (offsetInSlot != 0)
        {
            shifted = Temp();
            _add(_address, OpCode.ShiftRight, [shifted, slotOp, new Immediate(offsetInSlot)]);
        }
        var masked = Temp();
        _add(_address, OpCode.And, [masked, shifted, new Immediate((1 << bits) - 1)]);
        return masked;
    }

    /// <summary>A narrower element's bits sign-extended to a 32-bit operand.</summary>
    private IOperand? SignedElementOperand(VectorState state, Arm64VectorElement element)
    {
        var bits = ElementBits(element);
        var offset = bits * element.Index;
        if (bits == 32)
            return SlotOperand(state, element.Index);
        if (bits == 64)
            return Lane64Operand(state, element.Index);
        var slotOp = SlotOperand(state, offset / 32);
        if (slotOp == null)
            return null;
        if (slotOp is Immediate { } signedSlotImm)
        {
            // A fully proven lane sign-extends into a fully known word; a
            // partially proven one keeps only its proven bytes.
            var kept = ExtractedProvenBytes(signedSlotImm, offset % 32, bits / 8);
            return new Immediate((int)signedSlotImm.Value << (32 - offset % 32 - bits) >> (32 - bits),
                kept >= bits / 8 ? 4 : kept);
        }
        // (value << (32 - off - bits)) >> (32 - bits): arithmetic shift sign-extends.
        var left = Temp();
        _add(_address, OpCode.ShiftLeft, [left, slotOp, new Immediate(32 - offset % 32 - bits)]);
        var extended = Temp();
        _add(_address, OpCode.ShiftRight, [extended, left, new Immediate(32 - bits)]);
        return extended;
    }

    private void EmitLaneOp(OpCode opCode, string destName, int laneBits, int lane,
        IOperand left, IOperand right, VectorState dest, bool isFloat = false,
        List<PendingLane>? narrow = null)
    {
        var destReg = ElementRegister(destName, laneBits, lane);
        var emitted = _add(_address, opCode, [destReg, left, right]);
        if (!isFloat && laneBits == 32)
            emitted.NativeIntegerWidthBits = 32;
        else if (isFloat && laneBits >= 32)
            // a float lane's result is a Single/Double: seed it so the lane
            // local does not inherit a wide operand's aggregate type
            emitted.NativeFloatWidthBits = laneBits;
        _emitted = true;
        if (laneBits >= 32)
        {
            dest.SetSlot(lane * laneBits / 32,  new LaneSlice(destReg, 0));
            if (laneBits == 64)
                dest.SetSlot(lane * 2 + 1,  new LaneSlice(destReg, 32));
            return;
        }
        // sub-32-bit lanes are masked to the lane width and buffered: their
        // covering 32-bit window is composed once every lane of it is written.
        _add(_address, OpCode.And, [destReg, destReg, new Immediate((1L << laneBits) - 1)])
            .NativeIntegerWidthBits = 32;
        _emitted = true;
        narrow!.Add(new PendingLane(laneBits * lane / 32, laneBits * lane % 32, destReg));
    }

    /// <summary>A sub-32-bit lane parked for window composition.</summary>
    private readonly record struct PendingLane(int Window, int BitOffset, IOperand Operand);

    /// <summary>
    /// A binary-op result in a fresh temporary. Width marks follow the lane
    /// width: 32-bit lanes need the emitted CIL to truncate at int32.
    /// </summary>
    private IOperand EmitTempOp(OpCode opCode, IOperand left, IOperand right, int widthBits)
    {
        if (left is Immediate { } leftImm && right is Immediate { } rightImm)
        {
            var l = leftImm.Value;
            var r = rightImm.Value;
            long? folded = opCode switch
            {
                OpCode.And => l & r,
                OpCode.Or => l | r,
                OpCode.Xor => l ^ r,
                OpCode.ShiftLeft => l << (int)r,
                // ISIL 'shr' lowers to an arithmetic shift
                OpCode.ShiftRight => l >> (int)r,
                OpCode.Add => l + r,
                OpCode.Subtract => l - r,
                _ => null
            };
            if (folded is { } result)
            {
                if (widthBits < 64)
                    result &= (1L << widthBits) - 1;
                // A folded byte is proven only where every input byte was;
                // the result itself only describes the folded width.
                return new Immediate(result,
                    Math.Min(Math.Min(leftImm.EffectiveProvenBytes, rightImm.EffectiveProvenBytes),
                        widthBits / 8));
            }
        }
        var temp = Temp();
        var emitted = _add(_address, opCode, [temp, left, right]);
        if (widthBits == 32)
            emitted.NativeIntegerWidthBits = 32;
        return temp;
    }

    private IOperand EmitTempUnary(OpCode opCode, IOperand operand, int widthBits)
    {
        if (operand is Immediate { } operandImm)
        {
            var v = operandImm.Value;
            long? folded = opCode switch
            {
                OpCode.Not => ~v,
                OpCode.Negate => -v,
                OpCode.SignExtend32 => (int)v,
                _ => null
            };
            if (folded is { } result)
            {
                if (widthBits < 64)
                    result &= (1L << widthBits) - 1;
                return new Immediate(result,
                    Math.Min(operandImm.EffectiveProvenBytes, widthBits / 8));
            }
        }
        var temp = Temp();
        var emitted = _add(_address, opCode, [temp, operand]);
        if (widthBits == 32)
            emitted.NativeIntegerWidthBits = 32;
        return temp;
    }

    /// <summary>
    /// Writes a lane's value into the destination's element local and records
    /// its provenance. 32/64-bit lanes cover whole windows; narrower lanes are
    /// masked to the lane width and buffered for <see cref="FlushNarrowLanes"/>,
    /// which composes every fully covered window into a 32-bit element local —
    /// a window with any unwritten lane stays unproven.
    /// </summary>
    private void EmitLaneValue(VectorState dest, string destName, int laneBits, int lane,
        IOperand value, List<PendingLane>? narrow, bool integerLanes = false)
    {
        var elementReg = ElementRegister(destName, laneBits, lane);
        if (laneBits >= 32)
        {
            var emitted = _add(_address, OpCode.Move, [elementReg, value]);
            // An integer lane's local wants the native-int32 mark; a forwarded
            // float lane must not carry it — only the write's byte width.
            if (laneBits == 32)
            {
                if (integerLanes)
                    emitted.NativeIntegerWidthBits = 32;
                else
                    emitted.NativeFloatWriteBits = 32;
            }
            ImmediateWriteWidth.ApplyToMove(emitted);
            _emitted = true;
            // the slot names the element local just written — recording the
            // source operand would alias it: a later write to the source's
            // register would then read through to this lane. Immediates keep
            // their own slice so constant provenance survives.
            dest.SetSlot(lane * laneBits / 32,  new LaneSlice(value is Immediate ? value : elementReg, 0));
            if (laneBits == 64)
                dest.SetSlot(lane * 2 + 1,  new LaneSlice(value is Immediate ? value : elementReg, 32));
            return;
        }

        var mask = (1L << laneBits) - 1;
        var laneOperand = value is Immediate { } laneImm
            ? (IOperand)new Immediate(laneImm.Value & mask,
                Math.Min(laneImm.EffectiveProvenBytes, laneBits / 8))
            : elementReg;
        if (value is Immediate)
        {
            var laneMove = _add(_address, OpCode.Move, [elementReg, laneOperand]);
            if (integerLanes)
                laneMove.NativeIntegerWidthBits = 32;
            else
                laneMove.NativeFloatWriteBits = 32;
            ImmediateWriteWidth.ApplyToMove(laneMove);
        }
        else
            _add(_address, OpCode.And, [elementReg, value, new Immediate(mask)]).NativeIntegerWidthBits = 32;
        _emitted = true;
        narrow!.Add(new PendingLane(laneBits * lane / 32, laneBits * lane % 32, laneOperand));
    }

    /// <summary>
    /// Composes buffered narrow lanes into their 32-bit windows. Only windows
    /// covered by every buffered lane are proven; a partially covered window is
    /// poisoned so consumers report it instead of reading a fabricated value.
    /// </summary>
    private void FlushNarrowLanes(VectorState dest, string destName, int laneBits, List<PendingLane> lanes)
    {
        var partsPerWindow = 32 / laneBits;
        for (var window = 0; window < 4; window++)
        {
            var parts = new IOperand?[partsPerWindow];
            var count = 0;
            foreach (var lane in lanes)
                if (lane.Window == window)
                {
                    parts[lane.BitOffset / laneBits] = lane.Operand;
                    count++;
                }
            if (count == 0)
                continue;
            if (count < partsPerWindow)
            {
                dest.SetSlot(window,  null); // partial window: hardware wrote it, we cannot name it
                continue;
            }

            IOperand composed = parts[0]!;
            // Every part of a composed window was a written lane, so the window
            // claims its whole width only when all of them were proven.
            var fullyProven = true;
            foreach (var part in parts)
                fullyProven &= part is Immediate { EffectiveProvenBytes: var partProven }
                    && partProven >= laneBits / 8;
            for (var part = 1; part < partsPerWindow; part++)
            {
                if (parts[part] is Immediate { } partImm)
                    parts[part] = new Immediate(partImm.Value << (part * laneBits), laneBits / 8);
                var shifted = parts[part] is Immediate
                    ? parts[part]
                    : EmitTempOp(OpCode.ShiftLeft, parts[part]!, new Immediate(part * laneBits), 32);
                composed = composed is Immediate { } composedImm && shifted is Immediate { } shiftedImm
                    ? new Immediate(composedImm.Value | shiftedImm.Value,
                        fullyProven ? 4 : Math.Min(composedImm.EffectiveProvenBytes,
                            shiftedImm.EffectiveProvenBytes))
                    : EmitTempOp(OpCode.Or, composed, shifted!, 32);
            }

            var windowReg = ElementRegister(destName, 32, window);
            var windowMove = _add(_address, OpCode.Move, [windowReg, composed]);
            windowMove.NativeIntegerWidthBits = 32;
            ImmediateWriteWidth.ApplyToMove(windowMove);
            _emitted = true;
            dest.SetSlot(window,  new LaneSlice(windowReg, 0));
        }
    }

    /// <summary>The operand holding lane <paramref name="lane"/> of <paramref name="state"/> at any width.</summary>
    private IOperand? LaneValueOperand(VectorState? state, int laneBits, int lane, bool signed)
        => state == null
            ? null
            : laneBits == 32
                ? SlotOperand(state, lane)
                : laneBits == 64
                    ? Lane64Operand(state, lane)
                    : signed
                        ? SignedElementOperand(state, new Arm64VectorElement(LaneWidth(laneBits), lane))
                        : NarrowElementOperand(state, lane * laneBits / 32, lane * laneBits % 32, laneBits);

    private static Arm64VectorElementWidth LaneWidth(int laneBits) => laneBits switch
    {
        8 => Arm64VectorElementWidth.B,
        16 => Arm64VectorElementWidth.H,
        32 => Arm64VectorElementWidth.S,
        _ => Arm64VectorElementWidth.D
    };

    /// <summary>
    /// Emit <paramref name="result"/> into scalar lane 0 of <paramref name="destReg"/>
    /// and record the register's post-write state: the scalar in the low element,
    /// the rest of the vector zeroed. Reduction and scalar-import results follow
    /// this shape.
    /// </summary>
    private void WriteScalarElement(Arm64Register destReg, int destBits, IOperand result)
    {
        var destName = Normalize(destReg);
        var elementReg = ElementRegister(destName, destBits, 0);
        var mask = destBits < 64 ? (1L << destBits) - 1 : -1L;
        if (result is Immediate { } resultImm)
            _add(_address, OpCode.Move, [elementReg,
                    new Immediate(resultImm.Value & mask,
                        Math.Min(resultImm.EffectiveProvenBytes, destBits / 8))])
                .NativeFloatWriteBits = 32;
        else if (destBits < 32)
        {
            _add(_address, OpCode.Move, [elementReg, result]).NativeIntegerWidthBits = 32;
            _add(_address, OpCode.And, [elementReg, elementReg, new Immediate(mask)])
                .NativeIntegerWidthBits = 32;
        }
        else
        {
            var elementMove = _add(_address, OpCode.Move, [elementReg, result]);
            elementMove.NativeFloatWriteBits = destBits;
            ImmediateWriteWidth.ApplyToMove(elementMove);
        }
        _emitted = true;

        var dest = Ensure(destReg);
        if (destBits >= 32)
        {
            dest.SetSlot(0,  new LaneSlice(elementReg, 0));
            dest.SetSlot(1,  destBits == 64 ? new LaneSlice(elementReg, 32) : new LaneSlice(Zero, 0));
        }
        else
        {
            // the scalar write zeroes the rest of the vector, so window 0 is the
            // masked element value — materialize it for window-level consumers.
            var windowReg = ElementRegister(destName, 32, 0);
            _add(_address, OpCode.Move, [windowReg, elementReg]).NativeIntegerWidthBits = 32;
            _emitted = true;
            dest.SetSlot(0,  new LaneSlice(windowReg, 0));
            dest.SetSlot(1,  new LaneSlice(Zero, 0));
        }
        dest.SetSlot(2,  new LaneSlice(Zero, 0));
        dest.SetSlot(3,  new LaneSlice(Zero, 0));
        SyncScalarView(dest, destName);
    }

    /// <summary>Unsigned value of the low byte of <paramref name="shiftLane"/>, sign-extended.</summary>
    private IOperand ShiftCountOperand(IOperand shiftLane, int laneBits)
    {
        var shifted = EmitTempOp(OpCode.ShiftLeft, shiftLane, new Immediate(laneBits - 8), laneBits);
        return EmitTempOp(OpCode.ShiftRight, shifted, new Immediate(laneBits - 8), laneBits);
    }

    private static bool IsLaneWiseBinop(Arm64Mnemonic mnemonic) => mnemonic is
        Arm64Mnemonic.AND or Arm64Mnemonic.ORR or Arm64Mnemonic.EOR
        or Arm64Mnemonic.BIC or Arm64Mnemonic.ORN or Arm64Mnemonic.EON
        or Arm64Mnemonic.ADD or Arm64Mnemonic.SUB or Arm64Mnemonic.MUL
        or Arm64Mnemonic.MLA or Arm64Mnemonic.MLS or Arm64Mnemonic.ADDP
        or Arm64Mnemonic.FADD or Arm64Mnemonic.FSUB or Arm64Mnemonic.FMUL or Arm64Mnemonic.FDIV
        or Arm64Mnemonic.FADDP;

    private static bool IsBitwise(Arm64Mnemonic mnemonic) => mnemonic is
        Arm64Mnemonic.AND or Arm64Mnemonic.ORR or Arm64Mnemonic.EOR
        or Arm64Mnemonic.BIC or Arm64Mnemonic.ORN or Arm64Mnemonic.EON;

    private static bool InvertsSecondOperand(Arm64Mnemonic mnemonic)
        => mnemonic is Arm64Mnemonic.BIC or Arm64Mnemonic.ORN or Arm64Mnemonic.EON;

    private static bool IsFloatLaneOp(Arm64Mnemonic mnemonic) => mnemonic is
        Arm64Mnemonic.FADD or Arm64Mnemonic.FSUB or Arm64Mnemonic.FMUL or Arm64Mnemonic.FDIV
        or Arm64Mnemonic.FADDP;

    /// <summary>
    /// The low window of a whole-register local is honest only when the
    /// register provably carries nothing beyond the low scalar — every upper
    /// slot a constant, the shape left by scalar-width writes. Wider carriers
    /// (LDR D/Q, vector copies) keep real provenance in the upper slots, where
    /// a managed aggregate (Vector2/3) may live.
    /// </summary>
    private static bool IsScalarWholeWindow(VectorState state, int slot, LaneSlice slice)
        => slot == 0
            && slice.BitOffset == 0
            && slice.Operand is Register { Name: { } name } && !name.Contains('.')
            && UpperWindowsProvable(state);

    /// Every upper window provably benign for a scalar-window read: a
    /// constant or an element local — either proves the window cannot carry
    /// part of a managed aggregate. A bare register window above bit 32 may
    /// hide half of a Vector2/3 load, so it does not qualify.
    /// </summary>
    private static bool UpperWindowsProvable(VectorState state)
    {
        for (var i = 1; i < 4; i++)
        {
            if (state.Slots[i] is not { } slice)
                return false;
            var ok = slice.Operand is Immediate
                || slice.Operand is Register { Name: { } upper } && upper.Contains('.');
            if (!ok)
                return false;
        }
        return true;
    }

    /// <summary>
    /// Whether a lane window is an honest floating-point carrier: an element
    /// local (V6.S0-style — provably one lane's bits), a constant, or the low
    /// window of a scalar-carrying register. A whole-register local in any
    /// other shape is refused — an LDR S/D may leave a managed aggregate
    /// (Vector2/Vector3) in the register local, and slicing or reading that
    /// as lane bits fabricates lane values out of managed semantics.
    /// </summary>
    private static bool IsFloatCarrier(VectorState state, int slot)
    {
        if (state.Slots[slot] is not { } slice)
            return false;
        if (slice.Operand is Immediate)
            return true;
        if (slice.Operand is Register { Name: { } name } && name.Contains('.'))
            return true; // element local — extracting any of its windows reads a proven lane
        return IsScalarWholeWindow(state, slot, slice);
    }

    /// <summary>
    /// Pure check that the lane is an honest float carrier — reads slot
    /// provenance only, emits nothing. Every caller probes all lanes with this
    /// first and materializes operands only once the whole vector checks out,
    /// so a failed fold leaves no orphaned shift temps behind.
    /// </summary>
    private static bool CanFloatLane(VectorState? state, int laneBits, int lane)
    {
        if (state == null)
            return false;
        if (laneBits == 32)
            return IsFloatCarrier(state, lane);
        return IsFloatCarrier(state, 2 * lane) && IsFloatCarrier(state, 2 * lane + 1);
    }

    /// <summary>
    /// A floating-point lane operand, or null when the lane cannot be read
    /// without pretending a whole-register local is an integer lane carrier.
    /// Call only after CanFloatLane passed — it may emit extraction temps.
    /// </summary>
    private IOperand? FloatLaneOperand(VectorState? state, int laneBits, int lane)
    {
        if (state == null)
            return null;
        if (laneBits == 32)
            return IsFloatCarrier(state, lane) ? SlotOperand(state, lane) : null;
        if (!IsFloatCarrier(state, 2 * lane) || !IsFloatCarrier(state, 2 * lane + 1))
            return null;
        return Lane64Operand(state, lane);
    }

    /// <summary>
    /// Whether a scalar FCM* register operand provably carries a scalar: an
    /// element local spanning the compare width, a constant, the low scalar
    /// of a scalar-carrying register (S-width compares only), or an untracked
    /// local (parameter/copy — typed by the signature, no aggregate ambiguity).
    /// A D-width carrier is always ambiguous — LDR D and a double result are
    /// indistinguishable here — so scalar FCMGT D folds only on operands with
    /// no provenance or element-local lanes.
    /// </summary>
    private bool ScalarCompareOperandHonest(Arm64Register reg, int width)
    {
        var state = LaneState(reg);
        if (state == null)
            return true;
        if (state.Slots[0] is not { BitOffset: 0 } slice)
            return false;
        if (slice.Operand is Immediate)
            return true;
        if (slice.Operand is Register { Name: { } n } && n.Contains('.'))
            return width == 32 || n.Contains(".D");
        return width == 32 && IsScalarWholeWindow(state, 0, slice);
    }

    /// <summary>
    /// Whether the register operands of a scalar FCM* are honest scalars —
    /// see ScalarCompareOperandHonest.
    /// </summary>
    public bool ScalarCompareOperandsHonest(Arm64Instruction insn)
    {
        var width = insn.Op0Reg is >= Arm64Register.D0 and <= Arm64Register.D31 ? 64 : 32;
        if (insn.Op1Kind == Arm64OperandKind.Register && !ScalarCompareOperandHonest(insn.Op1Reg, width))
            return false;
        return insn.Op2Kind != Arm64OperandKind.Register || ScalarCompareOperandHonest(insn.Op2Reg, width);
    }

    private bool TryConvertCore(Arm64Instruction insn, Func<Arm64Instruction, int, IOperand> convertOperand)
    {
        if (IsLaneWiseBinop(insn.Mnemonic)
            && insn.Op0Kind == Arm64OperandKind.Register
            && insn.Op1Kind is Arm64OperandKind.Register or Arm64OperandKind.VectorRegisterElement
            && insn.Op2Kind is Arm64OperandKind.Register or Arm64OperandKind.VectorRegisterElement
            && insn.Op0Arrangement != Arm64ArrangementSpecifier.None
            && IsVectorRegister(insn.Op0Reg))
        {
            // BIC .16B may complete a recorded Vector4 comparison — leave it to the
            // caller's existing path which recognizes that pattern.
            if (insn.Mnemonic == Arm64Mnemonic.BIC && insn.Op0Arrangement == Arm64ArrangementSpecifier.SixteenB)
                return false;
            return LowerLaneWise(insn);
        }

        switch (insn.Mnemonic)
        {
            case Arm64Mnemonic.MOV or Arm64Mnemonic.INS or Arm64Mnemonic.FMOV
                when insn.Op0Kind == Arm64OperandKind.VectorRegisterElement:
                return LowerInsert(insn, convertOperand);

            case Arm64Mnemonic.MOV
                when insn.Op0Kind == Arm64OperandKind.Register
                    && insn.Op1Kind == Arm64OperandKind.VectorRegisterElement:
            case Arm64Mnemonic.UMOV:
                return LowerExtract(insn, convertOperand, unsigned: true);
            case Arm64Mnemonic.SMOV:
                return LowerExtract(insn, convertOperand, unsigned: false);

            case Arm64Mnemonic.FMOV:
                return LowerFmov(insn, convertOperand);

            case Arm64Mnemonic.MOVI or Arm64Mnemonic.MVNI:
                return LowerMovi(insn, convertOperand);

            case Arm64Mnemonic.ORR or Arm64Mnemonic.BIC
                when insn.Op0Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op0Reg)
                    && insn.Op0Arrangement != Arm64ArrangementSpecifier.None
                    && insn.Op1Kind == Arm64OperandKind.Immediate:
                return LowerVectorImmediateOp(insn);

            case Arm64Mnemonic.SHL
                when insn.Op0Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op0Reg)
                    && insn.Op0Arrangement != Arm64ArrangementSpecifier.None:
                return LowerShiftImmediate(insn, OpCode.ShiftLeft);
            case Arm64Mnemonic.USHR or Arm64Mnemonic.SSHR
                when insn.Op0Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op0Reg)
                    && insn.Op0Arrangement != Arm64ArrangementSpecifier.None:
                return LowerShiftImmediate(insn, OpCode.ShiftRight);

            case Arm64Mnemonic.MOV
                when insn.Op0Kind == Arm64OperandKind.Register
                    && insn.Op1Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op0Reg) && IsVectorRegister(insn.Op1Reg)
                    && insn.Op0Arrangement != Arm64ArrangementSpecifier.None:
                return LowerVectorCopy(insn);

            case Arm64Mnemonic.MVN
                when insn.Op0Kind == Arm64OperandKind.Register
                    && insn.Op1Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op0Reg) && IsVectorRegister(insn.Op1Reg)
                    && insn.Op0Arrangement != Arm64ArrangementSpecifier.None:
                return LowerVectorNot(insn);

            case Arm64Mnemonic.USHLL or Arm64Mnemonic.USHLL2
                or Arm64Mnemonic.SSHLL or Arm64Mnemonic.SSHLL2
                when insn.Op0Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op0Reg)
                    && insn.Op1Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op1Reg)
                    && insn.Op2Kind == Arm64OperandKind.Immediate:
                return LowerShiftLong(insn);

            case Arm64Mnemonic.XTN or Arm64Mnemonic.XTN2
                when insn.Op0Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op0Reg)
                    && insn.Op1Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op1Reg):
                return LowerNarrow(insn);

            case Arm64Mnemonic.CMEQ or Arm64Mnemonic.CMGE or Arm64Mnemonic.CMGT
                or Arm64Mnemonic.CMHS or Arm64Mnemonic.CMHI
                or Arm64Mnemonic.CMLE or Arm64Mnemonic.CMLT
                when insn.Op0Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op0Reg)
                    && insn.Op0Arrangement != Arm64ArrangementSpecifier.None
                    && insn.Op1Kind == Arm64OperandKind.Register
                    && (insn.Op2Kind == Arm64OperandKind.Register
                        || insn.Op2Kind == Arm64OperandKind.Immediate):
                return LowerVectorCompare(insn);

            case Arm64Mnemonic.SMIN or Arm64Mnemonic.SMAX
                or Arm64Mnemonic.UMIN or Arm64Mnemonic.UMAX
                when insn.Op0Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op0Reg)
                    && insn.Op0Arrangement != Arm64ArrangementSpecifier.None
                    && insn.Op1Kind == Arm64OperandKind.Register
                    && insn.Op2Kind == Arm64OperandKind.Register:
                return LowerVectorMinMax(insn);

            case Arm64Mnemonic.USHL or Arm64Mnemonic.SSHL
                when insn.Op0Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op0Reg)
                    && insn.Op0Arrangement != Arm64ArrangementSpecifier.None
                    && insn.Op1Kind == Arm64OperandKind.Register
                    && insn.Op2Kind == Arm64OperandKind.Register:
                return LowerVectorShift(insn);

            case Arm64Mnemonic.ADDV or Arm64Mnemonic.SMINV or Arm64Mnemonic.SMAXV
                or Arm64Mnemonic.UMINV or Arm64Mnemonic.UMAXV
                when insn.Op0Kind == Arm64OperandKind.Register
                    && insn.Op0Arrangement == Arm64ArrangementSpecifier.None
                    && insn.Op1Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op1Reg)
                    && insn.Op1Arrangement != Arm64ArrangementSpecifier.None:
                return LowerReduction(insn);

            case Arm64Mnemonic.UCVTF or Arm64Mnemonic.SCVTF
                or Arm64Mnemonic.FCVTZS or Arm64Mnemonic.FCVTZU
                or Arm64Mnemonic.FCVTMS or Arm64Mnemonic.FCVTMU
                or Arm64Mnemonic.FCVTNS or Arm64Mnemonic.FCVTNU
                or Arm64Mnemonic.FCVTPS or Arm64Mnemonic.FCVTPU
                or Arm64Mnemonic.FCVTAS or Arm64Mnemonic.FCVTAU
                when insn.Op0Kind == Arm64OperandKind.Register
                    && insn.Op1Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op0Reg) && IsVectorRegister(insn.Op1Reg)
                    && insn.Op0Arrangement != Arm64ArrangementSpecifier.None
                    && insn.Op0Arrangement == insn.Op1Arrangement:
                return LowerConvert(insn);

            case Arm64Mnemonic.EXT
                when insn.Op0Kind == Arm64OperandKind.Register
                    && insn.Op1Kind == Arm64OperandKind.Register
                    && insn.Op2Kind == Arm64OperandKind.Register
                    && insn.Op3Kind == Arm64OperandKind.Immediate
                    && IsVectorRegister(insn.Op0Reg)
                    && insn.Op0Arrangement != Arm64ArrangementSpecifier.None:
                return LowerExt(insn);

            case Arm64Mnemonic.ZIP1 or Arm64Mnemonic.ZIP2
                or Arm64Mnemonic.UZP1 or Arm64Mnemonic.UZP2
                or Arm64Mnemonic.TRN1 or Arm64Mnemonic.TRN2
                when insn.Op0Kind == Arm64OperandKind.Register
                    && insn.Op1Kind == Arm64OperandKind.Register
                    && insn.Op2Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op0Reg)
                    && insn.Op0Arrangement != Arm64ArrangementSpecifier.None:
                return LowerPermute(insn);

            case Arm64Mnemonic.REV64
                when insn.Op0Kind == Arm64OperandKind.Register
                    && insn.Op1Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op0Reg)
                    && insn.Op0Arrangement != Arm64ArrangementSpecifier.None:
                return LowerPermute(insn);

            case Arm64Mnemonic.LD1R
                when insn.Op0Kind == Arm64OperandKind.Register
                    && insn.Op1Kind == Arm64OperandKind.Memory
                    && insn.MemIndexMode == Arm64MemoryIndexMode.Offset
                    && insn.MemAddendReg == Arm64Register.INVALID
                    && insn.MemBase != Arm64Register.INVALID:
                return LowerReplicateLoad(insn);

            case Arm64Mnemonic.LD1
                when insn.Op0Kind == Arm64OperandKind.VectorRegisterElement
                    && insn.Op1Kind == Arm64OperandKind.Memory
                    && insn.MemIndexMode == Arm64MemoryIndexMode.Offset
                    && insn.MemAddendReg == Arm64Register.INVALID
                    && insn.MemBase != Arm64Register.INVALID:
                return LowerElementLoad(insn);

            case Arm64Mnemonic.LD1
                when insn.Op0Kind == Arm64OperandKind.Register
                    && insn.Op0Arrangement != Arm64ArrangementSpecifier.None
                    && insn.MemIndexMode == Arm64MemoryIndexMode.Offset
                    && insn.MemAddendReg == Arm64Register.INVALID
                    && insn.MemBase != Arm64Register.INVALID:
                return LowerStructureLoad(insn);

            case Arm64Mnemonic.ST1
                when insn.Op0Kind == Arm64OperandKind.VectorRegisterElement
                    && insn.MemIndexMode == Arm64MemoryIndexMode.Offset
                    && insn.MemAddendReg == Arm64Register.INVALID
                    && insn.MemBase != Arm64Register.INVALID:
                return LowerElementStore(insn);

            case Arm64Mnemonic.STR or Arm64Mnemonic.STUR or Arm64Mnemonic.STP
                when insn.Op0Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op0Reg)
                    && insn.MemAddendReg == Arm64Register.INVALID
                    && insn.MemBase != Arm64Register.INVALID:
                return LowerStore(insn);
        }

        return false;
    }

    /// <summary>
    /// DUP Vd.T, Rn / Vn.T[i]: broadcast by emitting one element-local Move per
    /// lane; every written element local is its own provenance. Returns false
    /// only for operand shapes the pass cannot describe.
    /// </summary>
    public bool TryBroadcastDup(Arm64Instruction insn,
        Func<ulong, OpCode, List<IOperand>, Instruction> add,
        Func<Arm64Instruction, int, IOperand> convertOperand)
    {
        InstallEmitter(add);
        _address = insn.Address;
        _emitted = false;

        if (insn.Op0Kind != Arm64OperandKind.Register
            || insn.Op0Arrangement == Arm64ArrangementSpecifier.None)
            return false;

        var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
        var destName = Normalize(insn.Op0Reg);

        IOperand? source;
        if (insn.Op1Kind == Arm64OperandKind.Register)
            source = convertOperand(insn, 1);
        else if (insn.Op1Kind == Arm64OperandKind.VectorRegisterElement)
            source = ResolveElementSource(insn.Op1Reg, insn.Op1VectorElement);
        else
            return false;

        if (source == null)
        {
            var element = insn.Op1VectorElement;
            var opaqueDest = Ensure(insn.Op0Reg);
            ClaimDest(insn.Op0Reg);
            // the hardware still writes every lane with a value we cannot name
            var used = laneCount * laneBits / 32;
            for (var s = 0; s < used; s++)
                opaqueDest.SetSlot(s,  null);
            for (var s = used; s < 4; s++)
                opaqueDest.SetSlot(s,  new LaneSlice(Zero, 0));
            Diagnostic($"ARM64 SIMD lane {Normalize(insn.Op1Reg)}.{ElementLetter(ElementBits(element))}{element.Index} is unproven; broadcast is not safe.");
            return true;
        }

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);

        var slotsUsed = laneCount * laneBits / 32;
        for (var lane = 0; lane < laneCount; lane++)
        {
            var laneReg = ElementRegister(destName, laneBits, lane);
            _add(_address, OpCode.Move, [laneReg, source]).NativeFloatWriteBits = laneBits;
            _emitted = true;
            if (laneBits == 32)
                dest.SetSlot(lane,  new LaneSlice(laneReg, 0));
            else if (laneBits == 64)
            {
                dest.SetSlot(lane * 2,  new LaneSlice(laneReg, 0));
                dest.SetSlot(lane * 2 + 1,  new LaneSlice(laneReg, 32));
            }
            // 8/16-bit lanes cannot be represented at 32-bit granularity: the
            // element Moves are still emitted faithfully, slots stay unproven.
        }
        if (laneBits < 32)
            for (var slot = 0; slot < slotsUsed; slot++)
                dest.SetSlot(slot,  null); // bytes rewritten at sub-window granularity
        for (var slot = slotsUsed; slot < 4; slot++)
            dest.SetSlot(slot,  new LaneSlice(Zero, 0)); // 64-bit forms zero the upper half

        SyncScalarView(dest, destName);
        if (!_emitted)
            _add(_address, OpCode.Nop, []);
        return true;
    }

    /// <summary>
    /// FCMGT/FCMLT/FCMGE/FCMLE/FCMEQ vector forms (2S/4S/2D against a register
    /// or against #0): each lane folds to the hardware's all-ones/zero mask —
    /// a Check* op (ordered compares are unordered->0, which the emitted CIL
    /// comparison matches) followed by Negate. FCMGE/FCMLE are composite
    /// (a>b)|(a==b) / (a<b)|(a==b) so unordered lanes still mask to zero.
    /// Every source lane must be an honest float carrier; returns false when
    /// any lane is unprovable so the caller can pick a recorded-comparison or
    /// diagnostic path.
    /// </summary>
    public bool TryCompareMask(Arm64Instruction insn,
        Func<ulong, OpCode, List<IOperand>, Instruction> add,
        Func<Arm64Instruction, int, IOperand> convertOperand)
    {
        InstallEmitter(add);
        _address = insn.Address;
        _emitted = false;

        if (insn.Op0Kind != Arm64OperandKind.Register
            || insn.Op1Kind != Arm64OperandKind.Register)
            return false;

        var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
        if (laneBits is not (32 or 64))
            return false;

        var sourceA = LaneState(insn.Op1Reg);
        VectorState? sourceB = null;
        IOperand? zero = null;
        if (insn.Op2Kind == Arm64OperandKind.Register)
            sourceB = LaneState(insn.Op2Reg);
        else if (insn.Op2Kind == Arm64OperandKind.FloatingPointImmediate)
            zero = laneBits == 32 ? new FloatLiteral(0f) : new DoubleLiteral(0);
        else
            return false;

        if (sourceA == null && sourceB == null)
            return false; // fully opaque chain: caller's normal path

        // all-or-nothing: probe every lane before emitting anything — a
        // partially proven mask must leave the instruction unimplemented, not
        // trade it for a fold plus orphaned extraction temps.
        for (var lane = 0; lane < laneCount; lane++)
            if (!CanFloatLane(sourceA, laneBits, lane)
                || (zero == null && !CanFloatLane(sourceB, laneBits, lane)))
                return false;

        var aOps = new IOperand?[laneCount];
        var bOps = new IOperand?[laneCount];
        for (var lane = 0; lane < laneCount; lane++)
        {
            aOps[lane] = FloatLaneOperand(sourceA, laneBits, lane);
            bOps[lane] = zero ?? FloatLaneOperand(sourceB, laneBits, lane);
        }

        var primary = insn.Mnemonic switch
        {
            Arm64Mnemonic.FCMLT or Arm64Mnemonic.FCMLE => OpCode.CheckLess,
            Arm64Mnemonic.FCMEQ => OpCode.CheckEqual,
            _ => OpCode.CheckGreater
        };
        var orEqual = insn.Mnemonic is Arm64Mnemonic.FCMGE or Arm64Mnemonic.FCMLE;

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        var destName = Normalize(insn.Op0Reg);

        for (var lane = 0; lane < laneCount; lane++)
        {
            var laneReg = ElementRegister(destName, laneBits, lane);
            EmitLaneOp(primary, destName, laneBits, lane, aOps[lane]!, bOps[lane]!, dest, isFloat: true);
            if (orEqual)
            {
                var equal = Temp();
                _add(_address, OpCode.CheckEqual, [equal, aOps[lane]!, bOps[lane]!]);
                _add(_address, OpCode.Or, [laneReg, laneReg, equal]);
            }
            // Check* yields a boolean 0/1; negating it produces the mask's
            // all-ones. The lane is pinned Int32 — the comparison seed would
            // otherwise type the mask Boolean, whose stack value is 1, and a
            // downstream `and` would compute 1 & n instead of ~0 & n.
            _add(_address, OpCode.Negate, [laneReg, laneReg]).NativeIntegerWidthBits = 32;
            _emitted = true;
        }

        for (var slot = laneCount * laneBits / 32; slot < 4; slot++)
            dest.SetSlot(slot,  new LaneSlice(Zero, 0)); // narrow forms zero the upper half
        SyncScalarView(dest, destName);
        return true;
    }

    /// <summary>
    /// BIT/BIF/BSL Vd.{8B,16B}, Vn, Vm — three-way bitwise select folded per
    /// 32-bit window. All three are read-modify-write on the destination:
    ///   BIT: d = (n &amp; m) | (d &amp; ~m) — mask in operand 2
    ///   BIF: d = (n &amp; ~m) | (d &amp; m) — inverted mask in operand 2
    ///   BSL: d = (n &amp; d) | (m &amp; ~d) — mask is the old destination
    /// The ops are pure bit logic, so window granularity is exact; the old
    /// destination windows are read before its slots are claimed.
    ///
    /// Every consumed window must already hold a value readable as-is: an
    /// Immediate, an element local at offset 0, or the low window of a
    /// scalar-carrying register. Whole-register locals carrying wider data and
    /// shifted extractions are refused — consuming a managed-aggregate local
    /// through an integer op materializes reinterpret loads downstream, and a
    /// partial fold trades one honest diagnostic for several.
    /// </summary>
    private static bool CanBitWindow(VectorState state, int w)
    {
        if (state.Slots[w] is not { BitOffset: 0 } slice)
            return false;
        if (slice.Operand is Immediate)
            return true;
        if (slice.Operand is Register { Name: { } n })
            return n.Contains('.') || IsScalarWholeWindow(state, w, slice);
        return false;
    }
    public bool TryBitSelect(Arm64Instruction insn,
        Func<ulong, OpCode, List<IOperand>, Instruction> add,
        Func<Arm64Instruction, int, IOperand> convertOperand)
    {
        InstallEmitter(add);
        _address = insn.Address;
        _emitted = false;

        if (insn.Op0Kind != Arm64OperandKind.Register
            || insn.Op1Kind != Arm64OperandKind.Register
            || insn.Op2Kind != Arm64OperandKind.Register
            || insn.Op0Arrangement is not (Arm64ArrangementSpecifier.EightB
                or Arm64ArrangementSpecifier.SixteenB))
            return false;

        var slots = insn.Op0Arrangement == Arm64ArrangementSpecifier.SixteenB ? 4 : 2;

        var stateD = LaneState(insn.Op0Reg);
        var stateA = LaneState(insn.Op1Reg);
        var stateB = LaneState(insn.Op2Reg);
        if (stateD == null && stateA == null && stateB == null)
            return false; // fully opaque chain: caller's normal path

        // all-or-nothing: a partially proven select would swap the honest
        // diagnostic for a fold plus unknown windows — refuse instead
        if (stateD == null || stateA == null || stateB == null)
            return false;
        for (var w = 0; w < slots; w++)
            if (!CanBitWindow(stateA, w) || !CanBitWindow(stateB, w) || !CanBitWindow(stateD, w))
                return false;

        var aOps = new IOperand?[slots];
        var bOps = new IOperand?[slots];
        var dOps = new IOperand?[slots];
        for (var w = 0; w < slots; w++)
        {
            aOps[w] = SlotOperand(stateA, w);
            bOps[w] = SlotOperand(stateB, w);
            dOps[w] = SlotOperand(stateD, w);
        }

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        var destName = Normalize(insn.Op0Reg);

        for (var w = 0; w < slots; w++)
        {
            Register left, right;
            if (insn.Mnemonic == Arm64Mnemonic.BSL)
            {
                var notD = Temp();
                _add(_address, OpCode.Not, [notD, dOps[w]!]).NativeIntegerWidthBits = 32;
                left = Temp();
                _add(_address, OpCode.And, [left, aOps[w]!, dOps[w]!]).NativeIntegerWidthBits = 32;
                right = Temp();
                _add(_address, OpCode.And, [right, bOps[w]!, notD]).NativeIntegerWidthBits = 32;
            }
            else
            {
                var notB = Temp();
                _add(_address, OpCode.Not, [notB, bOps[w]!]).NativeIntegerWidthBits = 32;
                var aSide = insn.Mnemonic == Arm64Mnemonic.BIF ? notB : bOps[w]!;
                var dSide = insn.Mnemonic == Arm64Mnemonic.BIF ? bOps[w]! : notB;
                left = Temp();
                _add(_address, OpCode.And, [left, aOps[w]!, aSide]).NativeIntegerWidthBits = 32;
                right = Temp();
                _add(_address, OpCode.And, [right, dOps[w]!, dSide]).NativeIntegerWidthBits = 32;
            }

            var lane = ElementRegister(destName, 32, w);
            _add(_address, OpCode.Or, [lane, left, right]).NativeIntegerWidthBits = 32;
            _emitted = true;
            dest.SetSlot(w,  new LaneSlice(lane, 0));
        }

        for (var w = slots; w < 4; w++)
            dest.SetSlot(w,  new LaneSlice(Zero, 0)); // the 8B form zeroes the upper half
        SyncScalarView(dest, destName);
        return true;
    }

    /// <summary>
    /// FADDP Sd, Vn.2S / FADDP Dd, Vn.2D — the scalar pairwise reduction —
    /// folds to a plain Add when both lanes are honest float carriers (real
    /// element locals or constants, e.g. an INS-built vector or a windowed
    /// vector load). Returns false otherwise: a lane reached by shifting a
    /// whole-register local is refused, since a narrow write such as LDR D
    /// may carry a managed Vector2/aggregate that must not be treated as an
    /// integer lane carrier.
    /// </summary>
    public bool TryScalarFaddp(Arm64Instruction insn,
        Func<ulong, OpCode, List<IOperand>, Instruction> add,
        Func<Arm64Instruction, int, IOperand> convertOperand)
    {
        InstallEmitter(add);
        _address = insn.Address;
        _emitted = false;

        var laneBits = insn.Op1Arrangement switch
        {
            Arm64ArrangementSpecifier.TwoS => 32,
            Arm64ArrangementSpecifier.TwoD => 64,
            _ => 0
        };
        if (insn.Op0Kind != Arm64OperandKind.Register
            || insn.Op0Arrangement != Arm64ArrangementSpecifier.None // scalar form: Sd/Dd destination
            || insn.Op1Kind != Arm64OperandKind.Register
            || insn.Op2Kind != Arm64OperandKind.None
            || laneBits == 0)
            return false;

        var state = LaneState(insn.Op1Reg);
        // probe before materializing: a refused reduction must not leave
        // orphaned extraction temps behind
        if (!CanFloatLane(state, laneBits, 0) || !CanFloatLane(state, laneBits, 1))
            return false;

        _add(_address, OpCode.Add,
            [convertOperand(insn, 0), FloatLaneOperand(state, laneBits, 0)!, FloatLaneOperand(state, laneBits, 1)!]);
        _emitted = true;
        return true;
    }

    /// <summary>
    /// INS Vd.T[i], Rm / Vn.T[j] (also decoded as the MOV alias). The element
    /// Move is always emitted — it is the literal instruction semantics — but a
    /// destination window is only proven at 32/64-bit element widths.
    /// </summary>
    private bool LowerInsert(Arm64Instruction insn, Func<Arm64Instruction, int, IOperand> convertOperand)
    {
        var dest = Ensure(insn.Op0Reg);
        var element = insn.Op0VectorElement;
        // an element write leaves the register local's lower bits proven
        ClaimDest(insn.Op0Reg, element.Index * ElementBits(element));

        var elementBits = ElementBits(element);
        var destName = Normalize(insn.Op0Reg);
        var elementReg = ElementRegister(destName, elementBits, element.Index);

        IOperand? source;
        if (insn.Op1Kind == Arm64OperandKind.VectorRegisterElement)
            source = ResolveElementSource(insn.Op1Reg, insn.Op1VectorElement);
        else
            source = convertOperand(insn, 1);

        if (source == null)
        {
            var srcElement = insn.Op1VectorElement;
            dest.SetSlot(elementBits * element.Index / 32,  null);
            Diagnostic($"ARM64 SIMD lane {Normalize(insn.Op1Reg)}.{ElementLetter(ElementBits(srcElement))}{srcElement.Index} is unproven; insert source is not safe.");
            return true;
        }

        _add(_address, OpCode.Move, [elementReg, source]).NativeFloatWriteBits = elementBits;
        _emitted = true;

        switch (elementBits)
        {
            case 32:
                dest.SetSlot(element.Index,  new LaneSlice(elementReg, 0));
                break;
            case 64:
                dest.SetSlot(element.Index * 2,  new LaneSlice(elementReg, 0));
                dest.SetSlot(element.Index * 2 + 1,  new LaneSlice(elementReg, 32));
                break;
            default:
                dest.SetSlot(elementBits * element.Index / 32,  null); // partial-window write
                break;
        }
        if (elementBits * element.Index < 32)
            SyncScalarView(dest, destName);
        return true;
    }

    /// <summary>
    /// UMOV/SMOV/MOV Rd, Vn.T[i] extracts. A proven lane moves (or sign-extends)
    /// to the GPR; a tracked-but-unproven lane leaves an explicit diagnostic
    /// instead of reading an unwritten element local.
    /// </summary>
    private bool LowerExtract(Arm64Instruction insn, Func<Arm64Instruction, int, IOperand> convertOperand, bool unsigned)
    {
        var source = State(insn.Op1Reg);
        var element = insn.Op1VectorElement;
        var bits = ElementBits(element);

        IOperand? laneOp;
        if (source == null)
        {
            // an untracked register: only element 0 is provable, and only
            // when the local was not clobbered — a caller write or argument
            // provenance may still define it. A higher lane was never written
            // in the method: diagnose rather than fabricate an element local.
            if (bits * element.Index != 0 || _clobbered.Contains(Normalize(insn.Op1Reg)))
            {
                Diagnostic($"ARM64 SIMD lane {Normalize(insn.Op1Reg)}.{ElementLetter(bits)}{element.Index} is unproven; extraction is not safe.");
                return true;
            }
            laneOp = WholeRegisterElement(insn.Op1Reg, bits, 0, unsigned);
        }
        else
        {
            laneOp = unsigned ? ElementOperand(source, element) : SignedElementOperand(source, element);
            // a materialized register local holds its width of lanes: read
            // the element out of it when the covered bits are proven
            laneOp ??= MaterializedBitsOf(source.Name) >= bits * (element.Index + 1) || source.Whole
                ? WholeRegisterElement(insn.Op1Reg, bits, element.Index, unsigned) : null;
            if (laneOp == null)
            {
                Diagnostic($"ARM64 SIMD lane {Normalize(insn.Op1Reg)}.{ElementLetter(bits)}{element.Index} is unproven; extraction is not safe.");
                return true;
            }
        }

        var dest = convertOperand(insn, 0);
        if (!unsigned && insn.Op0Reg is >= Arm64Register.X0 and <= Arm64Register.X31)
        {
            _add(_address, OpCode.SignExtend32, [dest, laneOp]);
            _emitted = true;
            return true;
        }
        _add(_address, OpCode.Move, [dest, laneOp]);
        _emitted = true;
        return true;
    }

    /// <summary>
    /// FMOV forms: GPR->scalar moves prove window 0, scalar->GPR reads consume
    /// it, scalar<->scalar copies re-emit against provenance, and vector float
    /// constants materialize per-lane float element locals.
    /// </summary>
    private bool LowerFmov(Arm64Instruction insn, Func<Arm64Instruction, int, IOperand> convertOperand)
    {
        var destIsScalarFp = insn.Op0Kind == Arm64OperandKind.Register
            && insn.Op0Reg is >= Arm64Register.S0 and <= Arm64Register.S31 or >= Arm64Register.D0 and <= Arm64Register.D31;
        var destIsVector = insn.Op0Kind == Arm64OperandKind.Register
            && insn.Op0Reg is >= Arm64Register.V0 and <= Arm64Register.V31;
        var destIsGpr = insn.Op0Kind == Arm64OperandKind.Register && IsGpr(insn.Op0Reg);
        var srcIsScalarFp = insn.Op1Kind == Arm64OperandKind.Register
            && insn.Op1Reg is >= Arm64Register.S0 and <= Arm64Register.S31 or >= Arm64Register.D0 and <= Arm64Register.D31;

        // vector constant: FMOV Vd.T, #fpimm
        if (destIsVector && insn.Op1Kind == Arm64OperandKind.FloatingPointImmediate
            && insn.Op0Arrangement != Arm64ArrangementSpecifier.None)
        {
            var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
            var destName = Normalize(insn.Op0Reg);
            var dest = Ensure(insn.Op0Reg);
            ClaimDest(insn.Op0Reg);
            var slotsUsed = laneCount * laneBits / 32;
            IOperand laneLiteral = laneBits == 64
                ? new DoubleLiteral(insn.Op1FpImm)
                : new FloatLiteral((float)insn.Op1FpImm);
            for (var lane = 0; lane < laneCount; lane++)
            {
                var laneReg = ElementRegister(destName, laneBits, lane);
                _add(_address, OpCode.Move, [laneReg, laneLiteral]).NativeFloatWriteBits = laneBits;
                _emitted = true;
                if (laneBits == 32)
                    dest.SetSlot(lane,  new LaneSlice(laneReg, 0));
                else if (laneBits == 64)
                {
                    dest.SetSlot(lane * 2,  new LaneSlice(laneReg, 0));
                    dest.SetSlot(lane * 2 + 1,  new LaneSlice(laneReg, 32));
                }
            }
            if (laneBits < 32)
                for (var slot = 0; slot < slotsUsed; slot++)
                    dest.SetSlot(slot,  null);
            for (var slot = slotsUsed; slot < 4; slot++)
                dest.SetSlot(slot,  new LaneSlice(Zero, 0));
            SyncScalarView(dest, destName);
            return true;
        }

        // scalar GPR -> FP: FMOV Sd/Dd, Wn/Xn — a scalar-defining write
        if (destIsScalarFp && insn.Op1Kind == Arm64OperandKind.Register && IsGpr(insn.Op1Reg))
        {
            var width = insn.Op0Reg is >= Arm64Register.D0 and <= Arm64Register.D31 ? 64 : 32;
            // The S/D width is what a later slot read needs to know which of
            // the source's bytes the register actually took. NativeFloatWriteBits
            // keeps it provenance-only: the destination may still be read back
            // as a wider vector, so the write must not seed its managed type.
            _add(_address, OpCode.Move, [convertOperand(insn, 0), convertOperand(insn, 1)])
                .NativeFloatWriteBits = width;
            _emitted = true;
            var dest = Ensure(insn.Op0Reg);
            for (var i = 0; i < 4; i++)
                dest.SetSlot(i,  32 * i < width ? new LaneSlice(Reg(insn.Op0Reg), 32 * i) : new LaneSlice(Zero, 0));
            ClaimDest(insn.Op0Reg);
            // the emitted Move materializes the register local at the write's width
            dest.MaterializedBits = width;
            return true;
        }

        // scalar FP -> GPR: FMOV Wd/Xd, Sn/Dn — a bit copy of the low lane
        if (destIsGpr && srcIsScalarFp)
        {
            var source = LaneState(insn.Op1Reg);
            if (source == null)
                return false; // untouched vector local: keep the plain Move
            var width64 = insn.Op1Reg is >= Arm64Register.D0 and <= Arm64Register.D31;
            var laneOp = width64 ? Lane64Operand(source, 0) : SlotOperand(source, 0);
            if (laneOp == null)
            {
                Diagnostic($"ARM64 SIMD lane {Normalize(insn.Op1Reg)}.{(width64 ? "D" : "S")}0 is unproven; extraction is not safe.");
                return true;
            }
            _add(_address, OpCode.Move, [convertOperand(insn, 0), laneOp]);
            _emitted = true;
            return true;
        }

        // scalar FP -> scalar FP: FMOV Sd, Sn / Dd, Dn
        if (destIsScalarFp && srcIsScalarFp)
        {
            var source = State(insn.Op1Reg);
            var width64 = insn.Op1Reg is >= Arm64Register.D0 and <= Arm64Register.D31;
            IOperand? laneOp = null;
            if (source != null)
                laneOp = width64 ? Lane64Operand(source, 0) : SlotOperand(source, 0);
            laneOp ??= convertOperand(insn, 1); // fall back to the register local itself
            var dest = Ensure(insn.Op0Reg);
            // claim before the copy: ClaimDest clears lane-copy origins, and
            // the Move below records this one
            ClaimDest(insn.Op0Reg);
            var move = _add(_address, OpCode.Move, [convertOperand(insn, 0), laneOp]);
            move.NativeFloatWriteBits = width64 ? 64 : 32;
            ImmediateWriteWidth.ApplyToMove(move);
            _emitted = true;
            for (var i = 0; i < 4; i++)
                dest.SetSlot(i,  32 * i < (width64 ? 64 : 32) ? new LaneSlice(Reg(insn.Op0Reg), 32 * i) : new LaneSlice(Zero, 0));
            dest.MaterializedBits = width64 ? 64 : 32;
            return true;
        }

        return false;
    }

    /// <summary>
    /// MOVI/MVNI: constants make every window provable. The caller's scalar or
    /// float-literal Move is reproduced verbatim; per-window Moves of the
    /// expanded integer constant record the provenance.
    /// </summary>
    private bool LowerMovi(Arm64Instruction insn, Func<Arm64Instruction, int, IOperand> convertOperand)
    {
        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);

        if (insn.Op0Arrangement == Arm64ArrangementSpecifier.None)
        {
            var value = insn.Mnemonic == Arm64Mnemonic.MVNI ? ~insn.Op1Imm : insn.Op1Imm;
            _add(_address, OpCode.Move, [convertOperand(insn, 0), new Immediate(value, 8)]);
            _emitted = true;
            dest.SetSlot(0,  new LaneSlice(new Immediate(value, 8), 0));
            dest.SetSlot(1,  new LaneSlice(new Immediate(value, 8), 32));
            dest.SetSlot(2,  new LaneSlice(Zero, 0));
            dest.SetSlot(3,  new LaneSlice(Zero, 0));
            // the Move materializes the local as the register's whole value
            dest.MaterializedBits = 128;
            return true;
        }

        var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
        var destName = Normalize(insn.Op0Reg);
        var slotsUsed = laneCount * laneBits / 32;

        // reproduce the caller's emission so float consumers keep the vector form
        if (insn.Op0Arrangement is Arm64ArrangementSpecifier.TwoS or Arm64ArrangementSpecifier.FourS)
        {
            var bits = unchecked((uint)insn.Op1Imm << (int)insn.Op2Imm);
            if (insn.Mnemonic == Arm64Mnemonic.MVNI)
                bits = ~bits;
            var laneValue = BitConverter.Int32BitsToSingle(unchecked((int)bits));
            _add(_address, OpCode.Move,
                [convertOperand(insn, 0), new Vector128Literal(laneValue, laneValue, laneValue, laneValue)]);
        }
        else
        {
            var value = insn.Mnemonic == Arm64Mnemonic.MVNI ? ~insn.Op1Imm : insn.Op1Imm;
            _add(_address, OpCode.Move, [convertOperand(insn, 0), new Immediate(value)]);
        }
        _emitted = true;

        if (laneBits == 64)
        {
            var lane64 = insn.Mnemonic == Arm64Mnemonic.MVNI ? ~insn.Op1Imm : insn.Op1Imm;
            for (var lane = 0; lane < laneCount; lane++)
            {
                var laneReg = ElementRegister(destName, 64, lane);
                _add(_address, OpCode.Move, [laneReg, new Immediate(lane64, 8)]).NativeFloatWriteBits = 64;
                _emitted = true;
                dest.SetSlot(lane * 2,  new LaneSlice(new Immediate(lane64, 8), 0));
                dest.SetSlot(lane * 2 + 1,  new LaneSlice(new Immediate(lane64, 8), 32));
            }
        }
        else
        {
            // per-window broadcast constant: 32-bit lanes directly, narrower
            // lanes repeated across the window
            var window = laneBits switch
            {
                32 => unchecked((int)((uint)insn.Op1Imm << (int)insn.Op2Imm)),
                16 => ExpandToWindow(unchecked((ushort)((uint)insn.Op1Imm << (int)insn.Op2Imm))),
                _ => ExpandToWindow(unchecked((ushort)(byte)(insn.Op1Imm))),
            };
            if (insn.Mnemonic == Arm64Mnemonic.MVNI)
                window = ~window;
            for (var slot = 0; slot < slotsUsed; slot++)
            {
                var laneReg = ElementRegister(destName, 32, slot);
                _add(_address, OpCode.Move, [laneReg, new Immediate(window, 4)]).NativeFloatWriteBits = 32;
                _emitted = true;
                dest.SetSlot(slot,  new LaneSlice(new Immediate(window, 4), 0));
            }
        }
        for (var slot = slotsUsed; slot < 4; slot++)
            dest.SetSlot(slot,  new LaneSlice(Zero, 0));
        // the emitted Move writes the local: a broadcast literal is the
        // register's value whole, a scalar immediate only the lanes its bits
        // honestly cover (a .2D immediate is the low lane; a zero is the
        // whole cleared register).
        dest.MaterializedBits = insn.Op0Arrangement
            is Arm64ArrangementSpecifier.TwoS or Arm64ArrangementSpecifier.FourS
            ? 128
            : insn.Op1Imm == 0 ? 128 : laneBits == 64 ? 64 : 0;
        return true;

        static int ExpandToWindow(ushort lane) => unchecked((int)(uint)(lane | (uint)lane << 16));
    }

    /// <summary>
    /// ORR/BIC Vd.T, #imm{, LSL #s}: read-modify-write per window against the
    /// expanded immediate; the vector is its own input so every consumed
    /// window must already be proven.
    /// </summary>
    private bool LowerVectorImmediateOp(Arm64Instruction insn)
    {
        var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
        if (laneBits is not (32 or 16))
            return false;

        var dest = LaneState(insn.Op0Reg);
        if (dest == null)
            return false; // opaque dest: caller's normal path

        ClaimDest(insn.Op0Reg);
        var destName = Normalize(insn.Op0Reg);
        var slotsUsed = laneCount * laneBits / 32;

        var expanded = unchecked((int)((uint)insn.Op1Imm << (int)insn.Op2Imm));
        if (laneBits == 16)
            expanded = (expanded & 0xFFFF) | (expanded & 0xFFFF) << 16;
        if (insn.Mnemonic == Arm64Mnemonic.BIC)
            expanded = ~expanded;

        var operands = new IOperand?[slotsUsed];
        var proven = true;
        for (var slot = 0; slot < slotsUsed; slot++)
        {
            operands[slot] = SlotOperand(dest, slot);
            proven &= operands[slot] != null;
        }

        if (!proven)
        {
            for (var slot = 0; slot < slotsUsed; slot++)
                dest.SetSlot(slot,  null);
            for (var slot = slotsUsed; slot < 4; slot++)
                dest.SetSlot(slot,  new LaneSlice(Zero, 0));
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} immediate form has unproven lane provenance; scalarization skipped.");
            return true;
        }

        for (var slot = 0; slot < slotsUsed; slot++)
        {
            var laneReg = ElementRegister(destName, 32, slot);
            var emitted = _add(_address, insn.Mnemonic == Arm64Mnemonic.ORR ? OpCode.Or : OpCode.And,
                [laneReg, operands[slot]!, new Immediate(expanded)]);
            emitted.NativeIntegerWidthBits = 32;
            _emitted = true;
            dest.SetSlot(slot,  new LaneSlice(laneReg, 0));
        }
        for (var slot = slotsUsed; slot < 4; slot++)
            dest.SetSlot(slot,  new LaneSlice(Zero, 0));
        SyncScalarView(dest, destName);
        return true;
    }

    /// <summary>
    /// SHL/USHR/SSHR Vd.T, Vn.T, #imm: a per-lane shift at the element width.
    /// USHR masks the bits shifted in from the left — the emitted `shr` is
    /// arithmetic, so an unmasked fold would sign-extend unsigned lanes. Narrow
    /// lanes shift on their extracted element and compose back into windows.
    /// </summary>
    private bool LowerShiftImmediate(Arm64Instruction insn, OpCode op)
    {
        var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
        if (laneBits == 0)
            return false;
        var source = LaneState(insn.Op1Reg);
        if (source == null)
            return false;

        var signed = insn.Mnemonic == Arm64Mnemonic.SSHR;
        var operands = new IOperand?[laneCount];
        var proven = true;
        for (var lane = 0; lane < laneCount; lane++)
        {
            operands[lane] = LaneValueOperand(source, laneBits, lane, signed);
            proven &= operands[lane] != null;
        }

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        var destName = Normalize(insn.Op0Reg);
        var slotsUsed = laneCount * laneBits / 32;

        if (!proven)
        {
            for (var slot = 0; slot < slotsUsed; slot++)
                dest.SetSlot(slot,  null);
            for (var slot = slotsUsed; slot < 4; slot++)
                dest.SetSlot(slot,  new LaneSlice(Zero, 0));
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} has unproven lane provenance; scalarization skipped.");
            return true;
        }

        var narrow = laneBits < 32 ? new List<PendingLane>() : null;
        for (var lane = 0; lane < laneCount; lane++)
        {
            // narrow lanes read zero/sign-extended elements whose high bits are
            // already clear, so a plain `shr` is exact; on 32/64-bit lanes the
            // emitted `shr` is arithmetic and USHR must mask the fill bits.
            EmitLaneOp(op, destName, laneBits, lane, operands[lane]!, new Immediate(insn.Op2Imm), dest,
                narrow: narrow);
            if (insn.Mnemonic == Arm64Mnemonic.USHR && laneBits >= 32)
            {
                // (1 << (laneBits - imm)) - 1 in unchecked lane-width arithmetic
                var mask = unchecked((1L << (int)(laneBits - insn.Op2Imm)) - 1);
                var laneReg = ElementRegister(destName, laneBits, lane);
                _add(_address, OpCode.And, [laneReg, laneReg, new Immediate(mask)])
                    .NativeIntegerWidthBits = laneBits == 32 ? 32 : null;
                _emitted = true;
            }
        }
        if (narrow != null)
        {
            for (var slot = 0; slot < slotsUsed; slot++)
                dest.SetSlot(slot,  null); // FlushNarrowLanes re-proves covered windows
            FlushNarrowLanes(dest, destName, laneBits, narrow);
        }
        for (var slot = slotsUsed; slot < 4; slot++)
            dest.SetSlot(slot,  new LaneSlice(Zero, 0));
        SyncScalarView(dest, destName);
        return true;
    }

    /// <summary>
    /// Lane-wise binary/accumulator ops. Folding is all-or-nothing per
    /// instruction: every consumed window of every vector input must be proven,
    /// otherwise an explicit diagnostic is emitted and the result stays opaque.
    /// </summary>
    private bool LowerLaneWise(Arm64Instruction insn)
    {
        var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
        var vectorSlots = laneCount * laneBits / 32;
        var bitwise = IsBitwise(insn.Mnemonic);
        var isFloat = IsFloatLaneOp(insn.Mnemonic);
        var accumulates = insn.Mnemonic is Arm64Mnemonic.MLA or Arm64Mnemonic.MLS;

        // an element operand (FMUL Vd.2S, Vn.2S, Vm.S[i]) broadcasts one lane
        var aIsElement = insn.Op1Kind == Arm64OperandKind.VectorRegisterElement;
        var bIsElement = insn.Op2Kind == Arm64OperandKind.VectorRegisterElement;
        var sourceA = aIsElement ? null : LaneState(insn.Op1Reg);
        var sourceB = bIsElement ? null : LaneState(insn.Op2Reg);
        var elementA = aIsElement ? ResolveLaneElement(insn.Op1Reg, insn.Op1VectorElement) : null;
        var elementB = bIsElement ? ResolveLaneElement(insn.Op2Reg, insn.Op2VectorElement) : null;
        var sourceD = accumulates ? LaneState(insn.Op0Reg) : null;

        if (sourceA == null && sourceB == null && sourceD == null && elementA == null && elementB == null)
            return false; // fully opaque chain: caller's normal path

        // FADDP is all-or-nothing: a partially proven pairwise fold trades the
        // honest diagnostic for lane ops plus unknown windows — refuse before
        // the destination is claimed or any operand is materialized.
        if (insn.Mnemonic == Arm64Mnemonic.FADDP && laneBits is 32 or 64)
            for (var lane = 0; lane < laneCount; lane++)
            {
                var pairSource = lane < laneCount / 2 ? sourceA : sourceB;
                var pair = lane < laneCount / 2 ? lane : lane - laneCount / 2;
                if (!CanFloatLane(pairSource, laneBits, 2 * pair)
                    || !CanFloatLane(pairSource, laneBits, 2 * pair + 1))
                    return false;
            }

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        var destName = Normalize(insn.Op0Reg);

        var supported = bitwise || laneBits is 32 or 64 || !isFloat;
        var rows = bitwise ? vectorSlots : laneCount;
        var narrow = !bitwise && laneBits < 32 ? new List<PendingLane>() : null;
        var aOps = new IOperand?[rows];
        var bOps = new IOperand?[rows];
        var dOps = new IOperand?[rows];
        var anyLaneProven = false;

        for (var lane = 0; lane < rows; lane++)
        {
            if (insn.Mnemonic is Arm64Mnemonic.ADDP or Arm64Mnemonic.FADDP
                && laneBits is 32 or 64)
            {
                // out[i] = in1[2i]+in1[2i+1] for the lower half, in2 for the upper
                var pairSource = lane < laneCount / 2 ? sourceA : sourceB;
                var pair = lane < laneCount / 2 ? lane : lane - laneCount / 2;
                aOps[lane] = isFloat
                    ? FloatLaneOperand(pairSource, laneBits, 2 * pair)
                    : LaneOperand(pairSource, laneBits, 2 * pair);
                bOps[lane] = isFloat
                    ? FloatLaneOperand(pairSource, laneBits, 2 * pair + 1)
                    : LaneOperand(pairSource, laneBits, 2 * pair + 1);
            }
            else if (bitwise)
            {
                aOps[lane] = aIsElement ? elementA : sourceA == null ? null : SlotOperand(sourceA, lane);
                bOps[lane] = bIsElement ? elementB : sourceB == null ? null : SlotOperand(sourceB, lane);
            }
            else
            {
                aOps[lane] = aIsElement ? elementA : LaneOperand(sourceA, laneBits, lane);
                bOps[lane] = bIsElement ? elementB : LaneOperand(sourceB, laneBits, lane);
            }

            if (accumulates)
                dOps[lane] = bitwise ? SlotOperand(sourceD!, lane) : LaneOperand(sourceD, laneBits, lane);

            var laneProven = aOps[lane] != null && bOps[lane] != null
                && (!accumulates || dOps[lane] != null);
            anyLaneProven |= laneProven;
        }

        if (!supported || !anyLaneProven)
        {
            // bitwise ops are honest as a packed operation — when not one
            // window can be scalarized the whole-vector form still lifts the
            // instruction exactly, so refuse rather than diagnose
            if (supported && bitwise)
                return false;
            for (var slot = 0; slot < vectorSlots; slot++)
                dest.SetSlot(slot,  null);
            for (var slot = vectorSlots; slot < 4; slot++)
                dest.SetSlot(slot,  new LaneSlice(Zero, 0));
            Diagnostic(supported
                ? $"ARM64 SIMD {insn.Mnemonic} has unproven lane provenance; scalarization skipped."
                : $"ARM64 SIMD {insn.Mnemonic} on {laneBits}-bit lanes cannot be scalarized.");
            return true;
        }

        var unprovenLanes = 0;
        for (var lane = 0; lane < rows; lane++)
        {
            if (aOps[lane] == null || bOps[lane] == null || (accumulates && dOps[lane] == null))
            {
                // this lane is genuinely unknown — the hardware writes it, but
                // no local describes it: leave the window unproven and report.
                if (bitwise)
                    dest.SetSlot(lane,  null);
                else if (narrow == null)
                    for (var w = lane * laneBits / 32; w < (lane + 1) * laneBits / 32; w++)
                        dest.SetSlot(w,  null);
                unprovenLanes++;
                continue;
            }
            var a = aOps[lane]!;
            var b = bOps[lane]!;
            if (insn.Mnemonic is Arm64Mnemonic.BIC or Arm64Mnemonic.ORN or Arm64Mnemonic.EON)
            {
                var notB = Temp();
                _add(_address, OpCode.Not, [notB, b]);
                b = notB;
            }
            if (accumulates)
            {
                var product = Temp();
                _add(_address, OpCode.Multiply, [product, a, b]);
                EmitLaneOp(insn.Mnemonic == Arm64Mnemonic.MLA ? OpCode.Add : OpCode.Subtract,
                    destName, laneBits, lane, dOps[lane]!, product, dest, narrow: narrow);
                continue;
            }
            var op = insn.Mnemonic switch
            {
                Arm64Mnemonic.AND or Arm64Mnemonic.BIC => OpCode.And,
                Arm64Mnemonic.ORN => OpCode.Or,
                Arm64Mnemonic.EON or Arm64Mnemonic.EOR => OpCode.Xor,
                Arm64Mnemonic.SUB or Arm64Mnemonic.FSUB => OpCode.Subtract,
                Arm64Mnemonic.MUL or Arm64Mnemonic.FMUL => OpCode.Multiply,
                Arm64Mnemonic.FDIV => OpCode.Divide,
                _ => OpCode.Add
            };
            EmitLaneOp(op, destName, bitwise ? 32 : laneBits, lane, a, b, dest, isFloat, narrow);
        }
        if (narrow != null)
        {
            for (var slot = 0; slot < vectorSlots; slot++)
                dest.SetSlot(slot,  null); // FlushNarrowLanes re-proves covered windows
            FlushNarrowLanes(dest, destName, laneBits, narrow);
        }
        for (var slot = vectorSlots; slot < 4; slot++)
            dest.SetSlot(slot,  new LaneSlice(Zero, 0));
        SyncScalarView(dest, destName);
        if (unprovenLanes > 0)
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} has unproven lane provenance; scalarized {rows - unprovenLanes} of {rows} lanes.");
        return true;
    }

    private IOperand? LaneOperand(VectorState? state, int laneBits, int lane)
        => state == null ? null
            : laneBits < 32
                ? NarrowElementOperand(state, lane * laneBits / 32, lane * laneBits % 32, laneBits)
                : laneBits == 32 ? SlotOperand(state, lane) : Lane64Operand(state, lane);

    /// <summary>
    /// MOV Vd.T, Vn.T — the whole-vector register copy (ORR alias). The
    /// normal-path Move is reproduced so the register local keeps its meaning,
    /// and each proven window additionally copies into the destination's own
    /// element local: without that, lane state would reference the source's
    /// element locals, which a later write to the source would silently reuse.
    /// </summary>
    private bool LowerVectorCopy(Arm64Instruction insn)
    {
        var source = State(insn.Op1Reg);
        if (source == null)
            return false; // untracked: caller's plain Move stands on its own

        _add(_address, OpCode.Move, [Reg(insn.Op0Reg), Reg(insn.Op1Reg)]);
        _emitted = true;

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        var destName = Normalize(insn.Op0Reg);
        var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
        var slotsUsed = laneBits * laneCount / 32;
        for (var slot = 0; slot < slotsUsed; slot++)
        {
            var op = SlotOperand(source, slot);
            if (op == null)
            {
                dest.SetSlot(slot,  null);
                continue;
            }
            var laneReg = ElementRegister(destName, 32, slot);
            var slotMove = _add(_address, OpCode.Move, [laneReg, op]);
            slotMove.NativeFloatWriteBits = 32;
            ImmediateWriteWidth.ApplyToMove(slotMove);
            _emitted = true;
            dest.SetSlot(slot,  new LaneSlice(laneReg, 0));
        }
        for (var slot = slotsUsed; slot < 4; slot++)
            dest.SetSlot(slot,  new LaneSlice(Zero, 0));
        dest.Whole = source.Whole;
        return true;
    }

    /// <summary>MVN Vd.T, Vn.T — bitwise NOT, exact at 32-bit window granularity.</summary>
    private bool LowerVectorNot(Arm64Instruction insn)
    {
        var source = LaneState(insn.Op1Reg);

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        var destName = Normalize(insn.Op0Reg);
        var slotsUsed = insn.Op0Arrangement == Arm64ArrangementSpecifier.SixteenB ? 4 : 2;

        var unproven = 0;
        for (var slot = 0; slot < slotsUsed; slot++)
        {
            var op = SlotOperand(source, slot);
            if (op == null)
            {
                dest.SetSlot(slot,  null);
                unproven++;
                continue;
            }
            var laneReg = ElementRegister(destName, 32, slot);
            _add(_address, OpCode.Not, [laneReg, op]).NativeIntegerWidthBits = 32;
            _emitted = true;
            dest.SetSlot(slot,  new LaneSlice(laneReg, 0));
        }
        for (var slot = slotsUsed; slot < 4; slot++)
            dest.SetSlot(slot,  new LaneSlice(Zero, 0));
        SyncScalarView(dest, destName);
        if (unproven > 0)
            Diagnostic($"ARM64 SIMD MVN has unproven lane provenance; scalarized {slotsUsed - unproven} of {slotsUsed} lanes.");
        return true;
    }

    /// <summary>
    /// USHLL/USHLL2/SSHLL/SSHLL2: each destination lane is the zero- or
    /// sign-extended source lane shifted left by the immediate — the *2 forms
    /// read the source's high half.
    /// </summary>
    private bool LowerShiftLong(Arm64Instruction insn)
    {
        var (destBits, destLanes) = Arrangement(insn.Op0Arrangement);
        var (srcBits, srcLanes) = Arrangement(insn.Op1Arrangement);
        var unsigned = insn.Mnemonic is Arm64Mnemonic.USHLL or Arm64Mnemonic.USHLL2;
        var high = insn.Mnemonic is Arm64Mnemonic.USHLL2 or Arm64Mnemonic.SSHLL2;
        // *2 forms expose the wide source arrangement and read its high half
        if (srcBits == 0 || destBits != 2 * srcBits
            || srcLanes != (high ? 2 : 1) * destLanes)
            return false;

        var source = LaneState(insn.Op1Reg);

        var operands = new IOperand?[destLanes];
        var proven = true;
        for (var lane = 0; lane < destLanes; lane++)
        {
            var op = LaneValueOperand(source, srcBits, high ? destLanes + lane : lane,
                signed: !unsigned);
            if (op != null && srcBits == 32)
                op = unsigned
                    ? EmitTempOp(OpCode.And, op, new Immediate(0xFFFFFFFFL), 64)
                    : EmitTempUnary(OpCode.SignExtend32, op, 64);
            operands[lane] = op;
            proven &= op != null;
        }

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        var destName = Normalize(insn.Op0Reg);
        var slotsUsed = destLanes * destBits / 32;

        if (!proven)
        {
            for (var slot = 0; slot < slotsUsed; slot++)
                dest.SetSlot(slot,  null);
            for (var slot = slotsUsed; slot < 4; slot++)
                dest.SetSlot(slot,  new LaneSlice(Zero, 0));
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} has unproven lane provenance; scalarization skipped.");
            return true;
        }

        var narrow = destBits < 32 ? new List<PendingLane>() : null;
        for (var lane = 0; lane < destLanes; lane++)
        {
            var value = operands[lane]!;
            if (insn.Op2Imm != 0)
                value = EmitTempOp(OpCode.ShiftLeft, value, new Immediate(insn.Op2Imm), destBits);
            EmitLaneValue(dest, destName, destBits, lane, value, narrow, integerLanes: true);
        }
        if (narrow != null)
        {
            for (var slot = 0; slot < slotsUsed; slot++)
                dest.SetSlot(slot,  null);
            FlushNarrowLanes(dest, destName, destBits, narrow);
        }
        for (var slot = slotsUsed; slot < 4; slot++)
            dest.SetSlot(slot,  new LaneSlice(Zero, 0));
        SyncScalarView(dest, destName);
        return true;
    }

    /// <summary>
    /// XTN/XTN2: each written destination lane is the low half of the source
    /// lane — a plain mask. XTN2 writes the destination's high lanes and leaves
    /// the low half (and its provenance) untouched.
    /// </summary>
    private bool LowerNarrow(Arm64Instruction insn)
    {
        var (destBits, destLanes) = Arrangement(insn.Op0Arrangement);
        var (srcBits, srcLanes) = Arrangement(insn.Op1Arrangement);
        if (destBits == 0 || srcBits != 2 * destBits || srcLanes > destLanes)
            return false;

        var upper = insn.Mnemonic == Arm64Mnemonic.XTN2;
        var source = LaneState(insn.Op1Reg);
        var destState = Ensure(insn.Op0Reg);

        var operands = new IOperand?[srcLanes];
        var proven = true;
        for (var lane = 0; lane < srcLanes; lane++)
        {
            operands[lane] = LaneValueOperand(source, srcBits, lane, signed: false);
            proven &= operands[lane] != null;
        }

        ClaimDest(insn.Op0Reg);
        var destName = Normalize(insn.Op0Reg);
        var slotsUsed = destLanes * destBits / 32;
        var firstWritten = upper ? srcLanes : 0;

        if (!proven)
        {
            for (var slot = firstWritten * destBits / 32; slot < slotsUsed; slot++)
                destState.SetSlot(slot,  null);
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} has unproven lane provenance; scalarization skipped.");
            return true;
        }

        var narrow = new List<PendingLane>();
        var mask = (1L << destBits) - 1;
        for (var lane = 0; lane < srcLanes; lane++)
        {
            var value = operands[lane]! is Immediate { } laneValue
                ? new Immediate(laneValue.Value & mask,
                    Math.Min(laneValue.EffectiveProvenBytes, destBits / 8))
                : EmitTempOp(OpCode.And, operands[lane]!, new Immediate(mask), 32);
            EmitLaneValue(destState, destName, destBits, firstWritten + lane, value, narrow, integerLanes: true);
        }
        FlushNarrowLanes(destState, destName, destBits, narrow);
        if (!upper)
            for (var slot = slotsUsed; slot < 4; slot++)
                destState.SetSlot(slot,  new LaneSlice(Zero, 0));
        SyncScalarView(destState, destName);
        return true;
    }

    /// <summary>
    /// ADDV/SMINV/SMAXV/UMINV/UMAXV: a whole-vector reduction into a scalar
    /// register. Every lane must be proven — a partial fold cannot name the
    /// remaining addends. Unsigned min/max compares are only expressible on
    /// zero-extended lanes (8/16-bit); wider unsigned lanes stay diagnostic.
    /// </summary>
    private bool LowerReduction(Arm64Instruction insn)
    {
        var (srcBits, srcLanes) = Arrangement(insn.Op1Arrangement);
        var destBits = RegisterBytes(insn.Op0Reg) * 8;
        if (srcBits == 0 || destBits == 0)
            return false;

        var unsigned = insn.Mnemonic is Arm64Mnemonic.UMINV or Arm64Mnemonic.UMAXV;
        if (unsigned && srcBits > 16)
        {
            // CIL clt/cgt are signed; on zero-extended <=16-bit lanes they are
            // exact, but on wider lanes an unsigned compare cannot be emitted.
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} on {srcBits}-bit lanes is an unsigned compare CIL cannot express; scalarization skipped.");
            return true;
        }

        var source = LaneState(insn.Op1Reg);

        var operands = new IOperand?[srcLanes];
        var proven = true;
        for (var lane = 0; lane < srcLanes; lane++)
        {
            operands[lane] = LaneValueOperand(source, srcBits, lane,
                insn.Mnemonic is Arm64Mnemonic.SMINV or Arm64Mnemonic.SMAXV);
            proven &= operands[lane] != null;
        }

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        if (!proven)
        {
            // a scalar write zeroes the vector above the scalar; the scalar
            // itself cannot be named, so only window 0 loses provenance.
            dest.SetSlot(0,  null);
            for (var slot = 1; slot < 4; slot++)
                dest.SetSlot(slot,  new LaneSlice(Zero, 0));
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} has unproven lane provenance; scalarization skipped.");
            return true;
        }

        var acc = operands[0]!;
        var width = srcBits < 32 ? 32 : srcBits;
        for (var lane = 1; lane < srcLanes; lane++)
        {
            if (insn.Mnemonic == Arm64Mnemonic.ADDV)
            {
                acc = EmitTempOp(OpCode.Add, acc, operands[lane]!, width);
                continue;
            }
            // min(a,b) = b ^ ((a^b) & -(a<b)); unsigned lanes are zero-extended
            // so the signed CIL compare is exact.
            var cmp = insn.Mnemonic is Arm64Mnemonic.SMINV or Arm64Mnemonic.UMINV
                ? OpCode.CheckLess
                : OpCode.CheckGreater;
            var diff = EmitTempOp(OpCode.Xor, acc, operands[lane]!, width);
            var mask = EmitTempUnary(OpCode.Negate,
                EmitTempOp(cmp, acc, operands[lane]!, width), width);
            var sel = EmitTempOp(OpCode.And, diff, mask, width);
            acc = EmitTempOp(OpCode.Xor, operands[lane]!, sel, width);
        }

        WriteScalarElement(insn.Op0Reg, destBits, acc);
        return true;
    }

    /// <summary>
    /// CMEQ/CMGE/CMGT/CMHS/CMHI/CMLT/CMLE lane-wise integer compares: each lane
    /// folds to a Check* op negated into the hardware's all-ones/zero mask.
    /// CMHI/CMHS are unsigned and only expressible on zero-extended lanes
    /// (&lt;=16-bit); wider unsigned compares stay explicit diagnostics.
    /// </summary>
    private bool LowerVectorCompare(Arm64Instruction insn)
    {
        var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
        if (laneBits == 0)
            return false;

        var unsigned = insn.Mnemonic is Arm64Mnemonic.CMHI or Arm64Mnemonic.CMHS;
        if (unsigned && laneBits > 16)
        {
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} on {laneBits}-bit lanes is an unsigned compare CIL cannot express; scalarization skipped.");
            return true;
        }

        var sourceA = LaneState(insn.Op1Reg);
        VectorState? sourceB = null;
        var zeroCompare = false;
        if (insn.Op2Kind == Arm64OperandKind.Register)
            sourceB = LaneState(insn.Op2Reg);
        else if (insn.Op2Kind == Arm64OperandKind.Immediate && insn.Op2Imm == 0)
            zeroCompare = true;
        else
            return false;

        // signed compares read sign-extended elements so a lane's sign bit is
        // real; unsigned and equality compare the raw lane value.
        var signed = !unsigned && insn.Mnemonic != Arm64Mnemonic.CMEQ;
        var aOps = new IOperand?[laneCount];
        var bOps = new IOperand?[laneCount];
        for (var lane = 0; lane < laneCount; lane++)
        {
            aOps[lane] = LaneValueOperand(sourceA, laneBits, lane, signed);
            bOps[lane] = zeroCompare ? new Immediate(0) : LaneValueOperand(sourceB, laneBits, lane, signed);
        }

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        var destName = Normalize(insn.Op0Reg);
        var slotsUsed = laneCount * laneBits / 32;
        var narrow = laneBits < 32 ? new List<PendingLane>() : null;

        var primary = insn.Mnemonic switch
        {
            Arm64Mnemonic.CMGT or Arm64Mnemonic.CMHI => OpCode.CheckGreater,
            Arm64Mnemonic.CMGE or Arm64Mnemonic.CMHS => OpCode.CheckGreaterOrEqual,
            Arm64Mnemonic.CMEQ => OpCode.CheckEqual,
            Arm64Mnemonic.CMLE => OpCode.CheckLessOrEqual,
            _ => OpCode.CheckLess
        };

        var unprovenLanes = 0;
        for (var lane = 0; lane < laneCount; lane++)
        {
            if (aOps[lane] == null || bOps[lane] == null)
            {
                unprovenLanes++;
                if (narrow == null)
                    for (var w = lane * laneBits / 32; w < (lane + 1) * laneBits / 32; w++)
                        dest.SetSlot(w,  null);
                continue;
            }
            var laneReg = ElementRegister(destName, laneBits, lane);
            // Check* yields boolean 0/1; Negate produces the all-ones mask.
            _add(_address, primary, [laneReg, aOps[lane]!, bOps[lane]!]);
            var negated = _add(_address, OpCode.Negate, [laneReg, laneReg]);
            if (laneBits == 32)
                negated.NativeIntegerWidthBits = 32;
            _emitted = true;
            if (laneBits >= 32)
            {
                dest.SetSlot(lane * laneBits / 32,  new LaneSlice(laneReg, 0));
                if (laneBits == 64)
                    dest.SetSlot(lane * 2 + 1,  new LaneSlice(laneReg, 32));
            }
            else
            {
                _add(_address, OpCode.And, [laneReg, laneReg, new Immediate((1L << laneBits) - 1)])
                    .NativeIntegerWidthBits = 32;
                narrow!.Add(new PendingLane(laneBits * lane / 32, laneBits * lane % 32, laneReg));
            }
        }
        if (narrow != null)
        {
            for (var slot = 0; slot < slotsUsed; slot++)
                dest.SetSlot(slot,  null);
            FlushNarrowLanes(dest, destName, laneBits, narrow);
        }
        for (var slot = slotsUsed; slot < 4; slot++)
            dest.SetSlot(slot,  new LaneSlice(Zero, 0));
        SyncScalarView(dest, destName);
        if (unprovenLanes > 0)
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} has unproven lane provenance; scalarized {laneCount - unprovenLanes} of {laneCount} lanes.");
        return true;
    }

    /// <summary>
    /// SMIN/SMAX/UMIN/UMAX lane-wise: a branchless select per lane,
    /// b ^ ((a^b) &amp; -(a&lt;b)). Unsigned forms compare exactly only on
    /// zero-extended &lt;=16-bit lanes; wider unsigned lanes stay diagnostic.
    /// </summary>
    private bool LowerVectorMinMax(Arm64Instruction insn)
    {
        var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
        if (laneBits == 0)
            return false;

        var unsigned = insn.Mnemonic is Arm64Mnemonic.UMIN or Arm64Mnemonic.UMAX;
        if (unsigned && laneBits > 16)
        {
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} on {laneBits}-bit lanes is an unsigned compare CIL cannot express; scalarization skipped.");
            return true;
        }

        var sourceA = LaneState(insn.Op1Reg);
        var sourceB = LaneState(insn.Op2Reg);

        var signed = !unsigned;
        var aOps = new IOperand?[laneCount];
        var bOps = new IOperand?[laneCount];
        for (var lane = 0; lane < laneCount; lane++)
        {
            aOps[lane] = LaneValueOperand(sourceA, laneBits, lane, signed);
            bOps[lane] = LaneValueOperand(sourceB, laneBits, lane, signed);
        }

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        var destName = Normalize(insn.Op0Reg);
        var slotsUsed = laneCount * laneBits / 32;
        var narrow = laneBits < 32 ? new List<PendingLane>() : null;
        var compare = insn.Mnemonic is Arm64Mnemonic.SMIN or Arm64Mnemonic.UMIN
            ? OpCode.CheckLess
            : OpCode.CheckGreater;
        var width = laneBits < 32 ? 32 : laneBits;

        var unprovenLanes = 0;
        for (var lane = 0; lane < laneCount; lane++)
        {
            if (aOps[lane] == null || bOps[lane] == null)
            {
                unprovenLanes++;
                if (narrow == null)
                    for (var w = lane * laneBits / 32; w < (lane + 1) * laneBits / 32; w++)
                        dest.SetSlot(w,  null);
                continue;
            }
            var diff = EmitTempOp(OpCode.Xor, aOps[lane]!, bOps[lane]!, width);
            var mask = EmitTempUnary(OpCode.Negate,
                EmitTempOp(compare, aOps[lane]!, bOps[lane]!, width), width);
            var sel = EmitTempOp(OpCode.And, diff, mask, width);
            var value = EmitTempOp(OpCode.Xor, bOps[lane]!, sel, width);
            EmitLaneValue(dest, destName, laneBits, lane, value, narrow, integerLanes: true);
        }
        if (narrow != null)
        {
            for (var slot = 0; slot < slotsUsed; slot++)
                dest.SetSlot(slot,  null);
            FlushNarrowLanes(dest, destName, laneBits, narrow);
        }
        for (var slot = slotsUsed; slot < 4; slot++)
            dest.SetSlot(slot,  new LaneSlice(Zero, 0));
        SyncScalarView(dest, destName);
        if (unprovenLanes > 0)
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} has unproven lane provenance; scalarized {laneCount - unprovenLanes} of {laneCount} lanes.");
        return true;
    }

    /// <summary>
    /// USHL/SSHL Vd.T, Vn.T, Vm.T — variable per-lane shifts. The shift amount
    /// is the sign-extended low byte of each Vm lane: a positive amount is a
    /// truncating left shift (result 0 past the lane width), a negative amount
    /// is a truncating right shift — logical for USHL (the fill bits are masked
    /// since `shr` is arithmetic), arithmetic for SSHL with the count clamped
    /// to lane width so a magnitude at/over the width still sign-fills.
    /// Each side is emitted unconditionally and selected with the branchless
    /// mask -(count&lt;0) / -(count&gt;=0).
    /// </summary>
    private bool LowerVectorShift(Arm64Instruction insn)
    {
        var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
        if (laneBits == 0)
            return false;

        var sourceV = LaneState(insn.Op1Reg);
        var sourceS = LaneState(insn.Op2Reg);

        var signed = insn.Mnemonic == Arm64Mnemonic.SSHL;
        var width = laneBits < 32 ? 32 : laneBits;
        var vOps = new IOperand?[laneCount];
        var sOps = new IOperand?[laneCount];
        for (var lane = 0; lane < laneCount; lane++)
        {
            vOps[lane] = LaneValueOperand(sourceV, laneBits, lane, signed);
            // the count is the lane's low byte regardless of provenance flavour
            sOps[lane] = LaneValueOperand(sourceS, laneBits, lane, signed: false);
        }

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        var destName = Normalize(insn.Op0Reg);
        var slotsUsed = laneCount * laneBits / 32;
        var narrow = laneBits < 32 ? new List<PendingLane>() : null;

        var unprovenLanes = 0;
        for (var lane = 0; lane < laneCount; lane++)
        {
            if (vOps[lane] == null || sOps[lane] == null)
            {
                unprovenLanes++;
                if (narrow == null)
                    for (var w = lane * laneBits / 32; w < (lane + 1) * laneBits / 32; w++)
                        dest.SetSlot(w,  null);
                continue;
            }
            var value = EmitVectorShiftLane(vOps[lane]!, sOps[lane]!, laneBits, signed);
            EmitLaneValue(dest, destName, laneBits, lane, value, narrow, integerLanes: true);
        }
        if (narrow != null)
        {
            for (var slot = 0; slot < slotsUsed; slot++)
                dest.SetSlot(slot,  null);
            FlushNarrowLanes(dest, destName, laneBits, narrow);
        }
        for (var slot = slotsUsed; slot < 4; slot++)
            dest.SetSlot(slot,  new LaneSlice(Zero, 0));
        SyncScalarView(dest, destName);
        if (unprovenLanes > 0)
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} has unproven lane provenance; scalarized {laneCount - unprovenLanes} of {laneCount} lanes.");
        return true;
    }

    private IOperand EmitVectorShiftLane(IOperand value, IOperand shiftLane, int laneBits, bool signed)
    {
        var w = laneBits < 32 ? 32 : laneBits;
        var s = ShiftCountOperand(shiftLane, w);
        var zero = new Immediate(0);
        var negative = EmitTempUnary(OpCode.Negate,
            EmitTempOp(OpCode.CheckLess, s, zero, w), w);
        var nonnegative = EmitTempUnary(OpCode.Negate,
            EmitTempOp(OpCode.CheckGreaterOrEqual, s, zero, w), w);
        var negated = EmitTempUnary(OpCode.Negate, s, w);
        // magnitude |s| without a branch: s<0 ? -s : s
        var magnitude = EmitTempOp(OpCode.Xor, s,
            EmitTempOp(OpCode.And, EmitTempOp(OpCode.Xor, s, negated, w), negative, w), w);

        // left shift by min(s, w), gated by s in [0, w)
        var mL = MinOp(magnitude, w);
        var lft = EmitTempOp(OpCode.And,
            EmitTempOp(OpCode.ShiftLeft, value, mL, w),
            EmitTempOp(OpCode.And, nonnegative,
                EmitTempUnary(OpCode.Negate, EmitTempOp(OpCode.CheckLess, s, new Immediate(w), w), w), w), w);

        // right shift by min(|s|, bound): bound is w for a logical shift (a
        // count of w must produce 0 through the mask) and w-1 for SSHL (the
        // arithmetic shift by w-1 keeps sign-filling).
        var bound = signed ? w - 1 : w;
        var nC = MinOp(magnitude, bound);
        var shifted = EmitTempOp(OpCode.ShiftRight, value, nC, w);
        IOperand rgt;
        if (signed)
        {
            rgt = EmitTempOp(OpCode.And, shifted, negative, w);
        }
        else
        {
            var wc = EmitTempOp(OpCode.Subtract, new Immediate(w), nC, w);
            var dm = EmitTempOp(OpCode.Subtract,
                EmitTempOp(OpCode.ShiftLeft, new Immediate(1), wc, w), new Immediate(1), w);
            rgt = EmitTempOp(OpCode.And, EmitTempOp(OpCode.And, shifted, dm, w), negative, w);
        }
        return EmitTempOp(OpCode.Or, lft, rgt, w);

        IOperand MinOp(IOperand x, long hi) => EmitTempOp(OpCode.Xor, new Immediate(hi),
            EmitTempOp(OpCode.And, EmitTempOp(OpCode.Xor, x, new Immediate(hi), w),
                EmitTempUnary(OpCode.Negate, EmitTempOp(OpCode.CheckLess, x, new Immediate(hi), w), w), w), w);
    }

    /// <summary>
    /// Same-width lane-wise conversions (UCVTF/SCVTF/FCVT*): each lane's write
    /// is a Move into the destination's element local — the same convention the
    /// scalar path applies to its converts.
    /// </summary>
    private bool LowerConvert(Arm64Instruction insn)
    {
        var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
        if (laneBits is not (32 or 64))
            return false;

        var source = LaneState(insn.Op1Reg);

        var operands = new IOperand?[laneCount];
        var proven = true;
        for (var lane = 0; lane < laneCount; lane++)
        {
            operands[lane] = LaneOperand(source, laneBits, lane);
            proven &= operands[lane] != null;
        }

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        var destName = Normalize(insn.Op0Reg);
        var slotsUsed = laneCount * laneBits / 32;

        if (!proven)
        {
            for (var slot = 0; slot < slotsUsed; slot++)
                dest.SetSlot(slot,  null);
            for (var slot = slotsUsed; slot < 4; slot++)
                dest.SetSlot(slot,  new LaneSlice(Zero, 0));
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} has unproven lane provenance; scalarization skipped.");
            return true;
        }

        // FCVT* produce integer lanes; SCVTF/UCVTF float lanes.
        var integer = insn.Mnemonic is not (Arm64Mnemonic.UCVTF or Arm64Mnemonic.SCVTF);
        for (var lane = 0; lane < laneCount; lane++)
            EmitLaneValue(dest, destName, laneBits, lane, operands[lane]!, null, integerLanes: integer);
        for (var slot = slotsUsed; slot < 4; slot++)
            dest.SetSlot(slot,  new LaneSlice(Zero, 0));
        SyncScalarView(dest, destName);
        return true;
    }

    /// <summary>
    /// Lane-wise floating-point ops (FMAXNM/FMINNM, FABD, FRINT*/FSQRT/FABS
    /// vector forms): the caller supplies the per-lane emission — a resolved
    /// managed Math call — and this pass handles provenance, the element-local
    /// writes and the partial-fold diagnostic.
    /// </summary>
    public bool TryLaneWiseFloatMath(Arm64Instruction insn,
        Func<ulong, OpCode, List<IOperand>, Instruction> add,
        Action<IOperand, IOperand, IOperand?> emitLane)
    {
        InstallEmitter(add);
        _address = insn.Address;
        _emitted = false;

        var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
        if (laneBits is not (32 or 64)
            || insn.Op0Kind != Arm64OperandKind.Register
            || !IsVectorRegister(insn.Op0Reg)
            || insn.Op1Kind != Arm64OperandKind.Register
            || insn.Op2Kind is not (Arm64OperandKind.Register or Arm64OperandKind.None))
            return false;

        var binary = insn.Op2Kind == Arm64OperandKind.Register;
        var sourceA = LaneState(insn.Op1Reg);
        var sourceB = binary ? LaneState(insn.Op2Reg) : null;

        var provenLanes = 0;
        for (var lane = 0; lane < laneCount; lane++)
            if (CanFloatLane(sourceA, laneBits, lane)
                && (!binary || CanFloatLane(sourceB, laneBits, lane)))
                provenLanes++;
        if (provenLanes == 0)
        {
            var poison = Ensure(insn.Op0Reg);
            ClaimDest(insn.Op0Reg);
            var used = laneCount * laneBits / 32;
            for (var slot = 0; slot < used; slot++)
                poison.SetSlot(slot,  null);
            for (var slot = used; slot < 4; slot++)
                poison.SetSlot(slot,  new LaneSlice(Zero, 0));
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} has unproven lane provenance; scalarization skipped.");
            return true;
        }

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        var destName = Normalize(insn.Op0Reg);
        var slotsUsed = laneCount * laneBits / 32;

        for (var lane = 0; lane < laneCount; lane++)
        {
            var a = FloatLaneOperand(sourceA, laneBits, lane);
            var b = binary ? FloatLaneOperand(sourceB, laneBits, lane) : null;
            if (a == null || (binary && b == null))
            {
                for (var w = lane * laneBits / 32; w < (lane + 1) * laneBits / 32; w++)
                    dest.SetSlot(w,  null);
                continue;
            }
            var laneReg = ElementRegister(destName, laneBits, lane);
            emitLane(laneReg, a, b);
            _emitted = true;
            dest.SetSlot(lane * laneBits / 32,  new LaneSlice(laneReg, 0));
            if (laneBits == 64)
                dest.SetSlot(lane * 2 + 1,  new LaneSlice(laneReg, 32));
        }
        for (var slot = slotsUsed; slot < 4; slot++)
            dest.SetSlot(slot,  new LaneSlice(Zero, 0));
        SyncScalarView(dest, destName);
        if (provenLanes < laneCount)
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} has unproven lane provenance; scalarized {provenLanes} of {laneCount} lanes.");
        return true;
    }

    /// <summary>
    /// ST1 (single element form): the source lane must be proven — its value
    /// moves to memory verbatim. Other ST* structure forms are left for the
    /// caller's normal path.
    /// </summary>
    private bool LowerElementStore(Arm64Instruction insn)
    {
        var source = LaneState(insn.Op0Reg);

        var element = insn.Op0VectorElement;
        var bits = ElementBits(element);
        var op = LaneValueOperand(source, bits, element.Index, signed: false);
        if (op == null)
        {
            Diagnostic($"ARM64 SIMD lane {Normalize(insn.Op0Reg)}.{ElementLetter(bits)}{element.Index} is unproven; store is not safe.");
            return true;
        }

        var bytes = bits / 8;
        IOperand mem = insn.MemBase == Arm64Register.X31
            ? new StackOffset((int)insn.MemOffset)
            : new MemoryOperand(Reg(insn.MemBase), addend: insn.MemOffset, accessSize: bytes);
        _add(_address, OpCode.Move, [mem, op]).NativeMemoryAccessSize = bytes;
        _emitted = true;
        return true;
    }

    /// <summary>
    /// A 32-bit window of a register, for permute sources: the proven slice
    /// when the register is lane-tracked, an extraction from the whole-register
    /// local when only the whole vector is materialized, else null.
    /// </summary>
    private IOperand? WindowOperand(VectorState? state, Arm64Register reg, int window)
    {
        if (state == null)
            // Element 0 of an untracked register is its scalar home — the
            // register local, when an argument or caller write defined it.
            // A clobbered register's local is stale: unproven.
            return window == 0 && !_clobbered.Contains(Normalize(reg)) ? Reg(reg) : null;
        if (state.Slots[window] != null)
            return SlotOperand(state, window);
        if (MaterializedBitsOf(state.Name) >= 32 * (window + 1))
            return WholeLaneOperand(reg, 32, window);
        return state.Whole ? WholeLaneOperand(reg, 32, window) : null;
    }

    /// <summary>
    /// One permute element of <paramref name="reg"/>: the proven lane operand
    /// when lane-tracked, an extraction from the whole-register local when the
    /// whole vector is materialized, else null.
    /// </summary>
    private IOperand? PermuteSourceOperand(VectorState? state, Arm64Register reg, int laneBits, int lane)
    {
        if (state == null)
            return lane * laneBits == 0 && !_clobbered.Contains(Normalize(reg)) ? Reg(reg) : null;
        if (LaneValueOperand(state, laneBits, lane, signed: false) is { } op)
            return op;
        if (MaterializedBitsOf(state.Name) >= laneBits * (lane + 1))
            return WholeLaneOperand(reg, laneBits, lane);
        return state.Whole ? WholeLaneOperand(reg, laneBits, lane) : null;
    }

    /// <summary>
    /// A lane read straight out of the materialized whole-register local —
    /// the register holds every bit, so a shift exposes any lane honestly.
    /// </summary>
    private IOperand WholeLaneOperand(Arm64Register reg, int laneBits, int lane)
    {
        var shift = laneBits * lane;
        if (shift == 0)
            return Reg(reg);
        return EmitTempOp(OpCode.ShiftRight, Reg(reg), new Immediate(shift), laneBits);
    }

    /// <summary>
    /// One element read out of the whole-register local: a shift plus a mask
    /// or sign-extension for sub-32-bit elements.
    /// </summary>
    private IOperand WholeRegisterElement(Arm64Register reg, int bits, int index, bool unsigned)
    {
        var shift = bits * index;
        IOperand op = Reg(reg);
        if (shift != 0)
            op = EmitTempOp(OpCode.ShiftRight, op, new Immediate(shift), 32);
        if (bits >= 32)
            return op;
        return unsigned
            ? EmitTempOp(OpCode.And, op, new Immediate((1 << bits) - 1), 32)
            : EmitTempOp(OpCode.ShiftRight,
                EmitTempOp(OpCode.ShiftLeft, op, new Immediate(32 - bits), 32),
                new Immediate(32 - bits), 32);
    }

    /// <summary>
    /// EXT Vd.T, Vn.T, Vm.T, #i: a byte-wise concatenate-and-extract — each
    /// destination window is a verbatim copy of one source window, so proven
    /// source windows move straight into the destination's element registers.
    /// </summary>
    private bool LowerExt(Arm64Instruction insn)
    {
        var slotCount = insn.Op0Arrangement == Arm64ArrangementSpecifier.SixteenB ? 4 : 2;
        var byteShift = insn.Op3Imm;
        if (byteShift % 4 != 0)
            return false; // a byte-misaligned extract is not a window permutation
        var windowShift = (int)(byteShift / 4);
        var stateA = LaneState(insn.Op1Reg);
        var stateB = LaneState(insn.Op2Reg);
        if (stateA == null && stateB == null)
            return false;

        // gather every source operand before any destination write: EXT may
        // write a register it also reads
        var ops = new IOperand?[slotCount];
        var proven = 0;
        for (var window = 0; window < slotCount; window++)
        {
            var source = window + windowShift;
            ops[window] = source < 4
                ? WindowOperand(stateA, insn.Op1Reg, source)
                : WindowOperand(stateB, insn.Op2Reg, source - 4);
            if (ops[window] != null)
                proven++;
        }
        StageAliasedSources(insn, ops, 32);

        var destName = Normalize(insn.Op0Reg);
        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        for (var window = 0; window < slotCount; window++)
            if (ops[window] is { } op)
                EmitLaneValue(dest, destName, 32, window, op, null);
            else
                dest.SetSlot(window,  null);
        for (var slot = slotCount; slot < 4; slot++)
            dest.SetSlot(slot,  new LaneSlice(Zero, 0));
        SyncScalarView(dest, destName);
        if (proven < slotCount)
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} has unproven lane provenance; scalarized {proven} of {slotCount} windows.");
        return true;
    }

    /// <summary>
    /// ZIP1/ZIP2, UZP1/UZP2, TRN1/TRN2 and REV64: pure lane permutations —
    /// each destination element is a verbatim copy of one source element, so a
    /// proven source lane moves straight into the destination's element local.
    /// </summary>
    private bool LowerPermute(Arm64Instruction insn)
    {
        var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
        if (laneBits is not (32 or 64) || laneCount == 0)
            return false;
        var twoSources = insn.Mnemonic != Arm64Mnemonic.REV64;
        var stateA = LaneState(insn.Op1Reg);
        var stateB = twoSources ? LaneState(insn.Op2Reg) : null;
        if (stateA == null && stateB == null)
            return false;

        var half = laneCount / 2;
        (VectorState? State, Arm64Register Reg, int Elem) Source(int lane)
        {
            var (second, elem) = insn.Mnemonic switch
            {
                // ZIP: interleave the halves; UZP: gather evens/odds; TRN:
                // transpose pairs; REV64: reverse within 64-bit groups
                Arm64Mnemonic.ZIP1 => (lane % 2 == 1, lane / 2),
                Arm64Mnemonic.ZIP2 => (lane % 2 == 1, half + lane / 2),
                Arm64Mnemonic.UZP1 => lane < half ? (false, 2 * lane) : (true, 2 * (lane - half)),
                Arm64Mnemonic.UZP2 => lane < half ? (false, 2 * lane + 1) : (true, 2 * (lane - half) + 1),
                Arm64Mnemonic.TRN1 => lane % 2 == 0 ? (false, lane) : (true, lane - 1),
                Arm64Mnemonic.TRN2 => lane % 2 == 0 ? (false, lane + 1) : (true, lane),
                _ => (false, (lane / (64 / laneBits)) * (64 / laneBits) + (64 / laneBits - 1 - lane % (64 / laneBits)))
            };
            return second ? (stateB, insn.Op2Reg, elem) : (stateA, insn.Op1Reg, elem);
        }

        // gather every source operand before any destination write: a permute
        // may write a register it also reads
        var ops = new IOperand?[laneCount];
        var proven = 0;
        for (var lane = 0; lane < laneCount; lane++)
        {
            var (state, reg, elem) = Source(lane);
            ops[lane] = PermuteSourceOperand(state, reg, laneBits, elem);
            if (ops[lane] != null)
                proven++;
        }
        StageAliasedSources(insn, ops, laneBits);

        var destName = Normalize(insn.Op0Reg);
        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        for (var lane = 0; lane < laneCount; lane++)
            if (ops[lane] is { } op)
                EmitLaneValue(dest, destName, laneBits, lane, op, null);
            else
                for (var w = lane * laneBits / 32; w < (lane + 1) * laneBits / 32; w++)
                    dest.SetSlot(w,  null);
        for (var slot = laneCount * laneBits / 32; slot < 4; slot++)
            dest.SetSlot(slot,  new LaneSlice(Zero, 0));
        SyncScalarView(dest, destName);
        if (proven < laneCount)
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} has unproven lane provenance; scalarized {proven} of {laneCount} lanes.");
        return true;
    }

    /// <summary>
    /// When a permute writes a register it also reads, every gathered operand
    /// is first staged into a temp so the writes cannot clobber a source.
    /// </summary>
    private void StageAliasedSources(Arm64Instruction insn, IOperand?[] ops, int laneBits)
    {
        var destName = Normalize(insn.Op0Reg);
        if (destName != Normalize(insn.Op1Reg)
            && (insn.Op2Kind != Arm64OperandKind.Register || destName != Normalize(insn.Op2Reg)))
            return;
        for (var i = 0; i < ops.Length; i++)
            if (ops[i] is { } op && op is not Immediate)
            {
                var temp = Temp();
                var staged = _add(_address, OpCode.Move, [temp, op]);
                if (laneBits == 32)
                    staged.NativeFloatWriteBits = 32;
                ops[i] = temp;
            }
        foreach (var op in ops)
            _emitted |= op != null;
    }

    /// <summary>
    /// LD1R (single register): broadcast a loaded element to every lane — one
    /// memory read materialized into every destination element local.
    /// </summary>
    private bool LowerReplicateLoad(Arm64Instruction insn)
    {
        var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
        if (laneBits is not (32 or 64) || laneCount == 0)
            return false;
        var bytes = laneBits / 8;
        IOperand mem = insn.MemBase == Arm64Register.X31
            ? new StackOffset((int)insn.MemOffset)
            : new MemoryOperand(Reg(insn.MemBase), addend: insn.MemOffset, accessSize: bytes);

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        var destName = Normalize(insn.Op0Reg);
        for (var lane = 0; lane < laneCount; lane++)
            EmitLaneValue(dest, destName, laneBits, lane, mem, null);
        for (var slot = laneCount * laneBits / 32; slot < 4; slot++)
            dest.SetSlot(slot,  new LaneSlice(Zero, 0));
        SyncScalarView(dest, destName);
        return true;
    }

    /// <summary>
    /// LD1 (single element to one lane): the load materializes the element
    /// local directly; other lanes keep their values.
    /// </summary>
    private bool LowerElementLoad(Arm64Instruction insn)
    {
        var element = insn.Op0VectorElement;
        var bits = ElementBits(element);
        var bytes = bits / 8;
        IOperand mem = insn.MemBase == Arm64Register.X31
            ? new StackOffset((int)insn.MemOffset)
            : new MemoryOperand(Reg(insn.MemBase), addend: insn.MemOffset, accessSize: bytes);

        var elementReg = ElementRegister(Normalize(insn.Op0Reg), bits, element.Index);
        _add(_address, OpCode.Move, [elementReg, mem]).NativeMemoryAccessSize = bytes;
        _emitted = true;

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg, element.Index * bits);
        if (bits == 32)
            dest.SetSlot(element.Index,  new LaneSlice(elementReg, 0));
        else if (bits == 64)
        {
            dest.SetSlot(element.Index * 2,  new LaneSlice(elementReg, 0));
            dest.SetSlot(element.Index * 2 + 1,  new LaneSlice(elementReg, 32));
        }
        else
            dest.SetSlot(bits * element.Index / 32,  null); // a partial window is unproven
        dest.Whole = false;
        return true;
    }

    /// <summary>
    /// LD1 (multiple structures, one or more registers): a contiguous load —
    /// register k's element j reads mem + k*regBytes + j*elementBytes. Each
    /// covered window materializes as the register's element local, so later
    /// lane consumers see proven values.
    /// </summary>
    private bool LowerStructureLoad(Arm64Instruction insn)
    {
        var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
        if (laneBits is not (32 or 64) || laneCount == 0)
            return false;
        var regBytes = laneCount * laneBits / 8;
        var elementBytes = laneBits / 8;

        var dests = new List<Arm64Register>();
        for (var i = 0; i < 4; i++)
        {
            var (kind, reg) = i switch
            {
                0 => (insn.Op0Kind, insn.Op0Reg),
                1 => (insn.Op1Kind, insn.Op1Reg),
                2 => (insn.Op2Kind, insn.Op2Reg),
                _ => (insn.Op3Kind, insn.Op3Reg)
            };
            if (kind == Arm64OperandKind.Memory)
                break;
            if (kind != Arm64OperandKind.Register || !IsVectorRegister(reg))
                return false;
            dests.Add(reg);
        }
        if (dests.Count == 0)
            return false;

        for (var r = 0; r < dests.Count; r++)
        {
            var name = Normalize(dests[r]);
            var dest = Ensure(dests[r]);
            ClaimDest(dests[r]);
            _clobbered.Remove(name);
            var baseOffset = insn.MemOffset + r * regBytes;
            // the whole-register local is materialized too, mirroring the
            // caller's normal-path Move for whole-vector loads
            IOperand whole = insn.MemBase == Arm64Register.X31
                ? new StackOffset((int)baseOffset)
                : new MemoryOperand(Reg(insn.MemBase), addend: baseOffset, accessSize: regBytes);
            _add(_address, OpCode.Move, [Reg(dests[r]), whole]).NativeMemoryAccessSize = regBytes;
            for (var lane = 0; lane < laneCount; lane++)
            {
                IOperand mem = insn.MemBase == Arm64Register.X31
                    ? new StackOffset((int)(baseOffset + lane * elementBytes))
                    : new MemoryOperand(Reg(insn.MemBase), addend: baseOffset + lane * elementBytes, accessSize: elementBytes);
                EmitLaneValue(dest, name, laneBits, lane, mem, null);
            }
            for (var slot = laneCount * laneBits / 32; slot < 4; slot++)
                dest.SetSlot(slot,  new LaneSlice(Zero, 0));
            dest.Whole = true;
            dest.MaterializedBits = regBytes * 8;
        }
        _emitted = true;
        return true;
    }

    /// <summary>
    /// The single operand a paired S-store writes when both lanes came from
    /// halves of one value: adjacent fields of one local (the two floats of a
    /// Vector2/Vector3 arg, say) resolve to that local; a register's low half
    /// and its canonical high-half element or shift temporary resolve to the
    /// register. Two unrelated lanes return null — the pair stays per-window.
    /// </summary>
    private IOperand? PairStoreOperand(LaneSlice lo, LaneSlice hi)
    {
        var loOp = CopyOrigin(lo.Operand);
        var hiOp = CopyOrigin(hi.Operand);
        if (loOp is FieldReference { Containers.Count: 0 } loField
            && hiOp is FieldReference { Containers.Count: 0 } hiField
            && loField.Local == hiField.Local
            && loField.Field.Offset + 4 == hiField.Field.Offset)
            return loField.Local;
        if (loOp is Register { Name: { } loName }
            && hiOp is Register { Name: { } hiName })
        {
            if (hiName == loName + ".S1")
                return loOp;
            // element registers for the two 32-bit halves of one register
            if (loName.EndsWith(".S0") && hiName == loName[..^1] + "1")
                return new Register(null, loName[..^3]);
            if (_shiftTemps.TryGetValue($"{loOp}|32", out var shiftTemp)
                && shiftTemp.Equals(hiOp))
                return loOp;
        }
        return null;
    }

    /// <summary>
    /// STR/STUR/STP of a vector register: a fully proven vector is stored as
    /// per-window scalar Moves, a partially proven one is diagnosed, and an
    /// opaque one falls through to the caller's path.
    /// </summary>
    private bool LowerStore(Arm64Instruction insn)
    {
        var first = State(insn.Op0Reg);
        if (first == null)
        {
            // a clobbered register's local is stale: the caller's whole-
            // register store would read garbage with no diagnostic
            if (!_clobbered.Contains(Normalize(insn.Op0Reg)))
                return false;
            Diagnostic($"ARM64 SIMD store of {Normalize(insn.Op0Reg)} reads a register whose value an opaque control-flow event clobbered; not safe.");
            return true;
        }
        var pair = insn.Mnemonic == Arm64Mnemonic.STP;
        var second = pair ? State(insn.Op1Reg) : null;
        if (pair && second == null)
        {
            if (!_clobbered.Contains(Normalize(insn.Op1Reg)))
                return false;
            Diagnostic($"ARM64 SIMD store of {Normalize(insn.Op1Reg)} reads a register whose value an opaque control-flow event clobbered; not safe.");
            return true;
        }

        var bytes = RegisterBytes(insn.Op0Reg);
        if (bytes < 4)
            return false;

        var slots = bytes / 4;

        var proven = true;
        for (var slot = 0; slot < slots; slot++)
            proven &= first.Slots[slot] != null;
        if (pair)
            for (var slot = 0; slot < slots; slot++)
                proven &= second!.Slots[slot] != null;

        // a load-into-store whole-register copy keeps its source memory as
        // provenance; a whole-register store whose load address was not
        // recorded keeps the caller's whole-register move, correct whenever
        // the local was materialized. Check before any emission: a false
        // here must not leave a half-emitted pair.
        if (first.Whole && first.LoadMemory == null
            || pair && second!.Whole && second.LoadMemory == null)
            return false;

        if (!proven)
        {
            // the caller's fallback reads the register local whole — honest
            // only while the local was materialized on this path; a lane-only
            // vector would read an unwritten or stale local silently
            if (MaterializedBitsOf(first.Name) > 0 && (!pair || MaterializedBitsOf(second!.Name) > 0))
                return false;
            Diagnostic($"ARM64 SIMD store of {Normalize(insn.Op0Reg)} has unproven lanes and no materialized register local; not safe.");
            return true;
        }

        // a pre/post-indexed access runs at the unindexed base — MemOffset is
        // the writeback, not the addend — and the base update must be emitted
        // here because a scalarized store never reaches the caller's
        // EmitWriteback: before the stores for pre-index, after for post.
        var storeOff = insn.MemIndexMode == Arm64MemoryIndexMode.Offset ? insn.MemOffset : 0;
        if (insn.MemIndexMode == Arm64MemoryIndexMode.PreIndex)
            EmitIndexWriteback(insn);

        // an STP S,S is one 8-byte store: when both lanes came from halves of
        // one value — adjacent fields of one local, or a register's low and
        // high halves — the write names that value so the slot keeps its
        // aggregate type; two unrelated singles keep per-window writes.
        if (pair && slots == 1
            && first.Slots[0] is { } pairLo && second!.Slots[0] is { } pairHi
            && PairStoreOperand(pairLo, pairHi) is { } pairOperand
            && RegisterReadable(pairOperand, 32))
        {
            IOperand pairMem = insn.MemBase == Arm64Register.X31
                ? new StackOffset((int)storeOff)
                : new MemoryOperand(Reg(insn.MemBase), addend: storeOff, accessSize: 8);
            _add(_address, OpCode.Move, [pairMem, pairOperand]).NativeMemoryAccessSize = 8;
            _emitted = true;
        }
        // two registers still holding adjacent slices of one loaded range are
        // one contiguous struct copy — emit a single memory-to-memory move so
        // the resolver can store the whole aggregate (LDELEM/STOBJ shape)
        // instead of truncating to the first covered field.
        else if (pair && insn.MemBase != Arm64Register.X31
            && first.LoadMemory is { } firstSource && second!.LoadMemory is { } secondSource
            && firstSource.AccessSize >= bytes && secondSource.AccessSize >= bytes
            && firstSource.Base is Register { Name: { } sourceBase }
            && secondSource.Base is Register { Name: { } secondBase } && secondBase == sourceBase
            && firstSource.Index == null && secondSource.Index == null
            && firstSource.Addend + bytes == secondSource.Addend)
        {
            var copy = _add(_address, OpCode.Move,
            [
                new MemoryOperand(Reg(insn.MemBase), addend: storeOff, accessSize: 2 * bytes),
                new MemoryOperand(firstSource.Base, addend: firstSource.Addend, accessSize: 2 * bytes)
            ]);
            copy.NativeMemoryAccessSize = 2 * bytes;
            copy.NativeStoreWidthBytes = 2 * bytes;
            _emitted = true;
        }
        else
        {
            for (var r = 0; r < (pair ? 2 : 1); r++)
            {
                var state = r == 0 ? first : second!;
                if (!EmitStore(insn, state, storeOff + r * bytes, bytes, slots))
                    return false;
            }
        }

        if (insn.MemIndexMode == Arm64MemoryIndexMode.PostIndex)
            EmitIndexWriteback(insn);
        return true;
    }

    /// <summary>
    /// The base-register update of a pre/post-indexed access, mirroring the
    /// caller's EmitWriteback — a scalarized store skips the caller's path,
    /// so the scalarizer emits the update itself on the correct side of the
    /// stores.
    /// </summary>
    private void EmitIndexWriteback(Arm64Instruction insn)
    {
        if (insn.MemBase == Arm64Register.X31)
            _add(_address, OpCode.ShiftStack, [new Immediate(insn.MemOffset)]);
        else
            _add(_address, OpCode.Add,
                [Reg(insn.MemBase), Reg(insn.MemBase), new Immediate(insn.MemOffset)]);
    }

    /// <summary>
    /// Emits one register's part of a store. Wide forms first: a memory-to-
    /// memory copy for a 128-bit register that still holds a whole-load's
    /// source, a single whole-value move when every lane names the same
    /// operand or adjacent fields of one aggregate, whole-width
    /// zero/immediate stores for constant lanes (the resolver splits them per
    /// field or merges zero runs into initobj). Anything else keeps the
    /// per-window writes so an adjacent-fields target resolves each member.
    /// A 64-bit register whose lanes came from a load also stores per-window:
    /// the resolver narrows each window back to the loaded field, which a
    /// single eight-byte copy could not name. Returns false only for an
    /// opaque whole-register store the caller's normal path must emit.
    /// </summary>
    private bool EmitStore(Arm64Instruction insn, VectorState state, long baseOff, int bytes, int slots)
    {
        if (bytes == 16
            && state.LoadMemory is { AccessSize: var loaded } source && loaded >= bytes
            && insn.MemBase != Arm64Register.X31)
        {
            var copy = _add(_address, OpCode.Move,
            [
                StoreMem(insn, baseOff, bytes),
                new MemoryOperand(source.Base, source.Index, source.Addend, source.Scale, bytes)
            ]);
            copy.NativeMemoryAccessSize = bytes;
            copy.NativeStoreWidthBytes = bytes;
            _emitted = true;
            return true;
        }
        if (bytes == 16 && state.Whole)
            return false;

        if (slots > 1 && AllSlotsConstant(state, slots))
        {
            if (bytes == 16 && IsAllZero(state, slots))
            {
                // one 4-byte store per window, not a whole-width store: a base
                // whose element type is not yet proven resolves a wide store to
                // the single field at its addend and drops the rest, while a
                // typed base merges adjacent zero windows into initobj or the
                // per-field split all the same.
                for (var slot = 0; slot < slots; slot++)
                {
                    var zero = _add(_address, OpCode.Move,
                        [StoreMem(insn, baseOff + slot * 4, 4), new Immediate(0, 4)]);
                    zero.NativeStoreWidthBytes = 4;
                }
            }
            else
            {
                for (var group = 0; group < slots / 2; group++)
                {
                    var bits = state.WindowConstant(group * 2)!.Value
                               | state.WindowConstant(group * 2 + 1)!.Value << 32;
                    var constant = _add(_address, OpCode.Move,
                        [StoreMem(insn, baseOff + group * 8, 8),
                         new Immediate(unchecked((long)bits), 8)]);
                    constant.NativeStoreWidthBytes = 8;
                }
            }
            _emitted = true;
            return true;
        }

        if (slots == 4
            && WholeVectorStoreOperand(state) is { } vectorOperand
            && RegisterReadable(vectorOperand, 32))
        {
            var vectorMove = _add(_address, OpCode.Move, [StoreMem(insn, baseOff, 16), vectorOperand]);
            vectorMove.NativeStoreWidthBytes = 16;
            _emitted = true;
            return true;
        }

        // a 64-bit store whose two lanes are the low and high halves of one
        // operand names that operand whole — an 8-byte field or aggregate
        // resolves without reading a lane-typed local. A register the lanes
        // came from by loading keeps the per-window stores instead: its
        // windows narrow back to the fields the load covered.
        if (slots == 2
            && state.Slots[0] is { } low && state.Slots[1] is { } high
            && low.BitOffset == 0 && high.BitOffset == 32
            && SameOperand(low.Operand, high.Operand)
            && !(low.Operand is Register { Name: { } laneReg }
                 && _vectors.TryGetValue(laneReg, out var laneState) && laneState.Loaded)
            && RegisterReadable(low.Operand, 64))
        {
            var wide = _add(_address, OpCode.Move, [StoreMem(insn, baseOff, 8), low.Operand]);
            wide.NativeStoreWidthBytes = 8;
            _emitted = true;
            return true;
        }

        for (var slot = 0; slot < slots; slot++)
        {
            var op = SlotOperand(state, slot);
            if (op == null)
                continue;
            // every proven 32-bit window is its own four-byte store: a window
            // that is itself a slice of a wider load narrows back to the field
            // it covered, and an element local already carries the field's
            // float width — either way the destination member resolves.
            var window = _add(_address, OpCode.Move, [StoreMem(insn, baseOff + slot * 4, 4), op]);
            window.NativeMemoryAccessSize = 4;
            window.NativeStoreWidthBytes = 4;
            _emitted = true;
        }
        return true;
    }

    private IOperand StoreMem(Arm64Instruction insn, long addend, int accessSize)
        => insn.MemBase == Arm64Register.X31
            ? new StackOffset((int)addend)
            : new MemoryOperand(Reg(insn.MemBase), addend: addend, accessSize: accessSize);

    /// <summary>Two lane slices spelling one operand's low and high halves.</summary>
    private static bool SameOperand(IOperand a, IOperand b) => (a, b) switch
    {
        (Register left, Register right) => left.Name == right.Name,
        _ => ReferenceEquals(a, b)
    };

    private static bool AllSlotsConstant(VectorState state, int slots)
    {
        for (var slot = 0; slot < slots; slot++)
            if (state.WindowConstant(slot) == null)
                return false;
        return true;
    }

    private static bool IsAllZero(VectorState state, int slots)
    {
        for (var slot = 0; slot < slots; slot++)
            if (state.WindowConstant(slot) != 0)
                return false;
        return true;
    }

    private static bool IsSlotConstant(LaneSlice slice) => slice.Operand is Immediate or FloatLiteral or DoubleLiteral;

    /// <summary>The raw 32 bits a constant lane slice carries.</summary>
    private static ulong SlotConstantBits(LaneSlice slice) => slice.Operand switch
    {
        Immediate { UnsignedValue: var bits } when slice.BitOffset == 0 => bits & 0xFFFFFFFF,
        Immediate { UnsignedValue: var bits } when slice.BitOffset == 32 => bits >> 32,
        FloatLiteral { Value: var value } when slice.BitOffset == 0
            => unchecked((uint)BitConverter.SingleToInt32Bits(value)),
        DoubleLiteral { Value: var value } when slice.BitOffset == 0
            => unchecked((ulong)BitConverter.DoubleToInt64Bits(value)) & 0xFFFFFFFF,
        DoubleLiteral { Value: var value } when slice.BitOffset == 32
            => unchecked((ulong)BitConverter.DoubleToInt64Bits(value)) >> 32,
        _ => 0
    };

    /// <summary>
    /// The operand naming a 128-bit register's whole value for a wide store:
    /// the register local when every lane is its own slice (a whole-register
    /// copy — the local really holds all sixteen bytes), or the aggregate
    /// when every lane is a field of one local at consecutive 4-byte offsets.
    /// Constant lanes stay per-window: a Vector128Literal cannot spell into
    /// a non-vector destination the way four member stores can.
    /// </summary>
    private IOperand? WholeVectorStoreOperand(VectorState state)
    {
        var slots = new List<LaneSlice>(4);
        var allRegister = true;
        for (var slot = 0; slot < 4; slot++)
        {
            var slice = state.Slots[slot]!.Value;
            slots.Add(slice);
            allRegister &= slice.BitOffset == slot * 32
                           && slice.Operand is Register { Name: not null } reg
                           && reg.Name == state.Name;
        }
        if (allRegister)
            return new Register(null, state.Name);
        // every lane a field of one local, at consecutive 4-byte offsets:
        // the store writes the aggregate whole.
        if (CopyOrigin(slots[0].Operand) is FieldReference { Containers.Count: 0, Local: { } owner } firstField)
        {
            var baseOffset = firstField.Offset;
            var adjacent = true;
            for (var slot = 1; slot < 4; slot++)
                adjacent &= CopyOrigin(slots[slot].Operand) is FieldReference
                            {
                                Containers.Count: 0, Local: { } other, Offset: var off
                            }
                            && ReferenceEquals(other, owner) && off == baseOffset + slot * 4;
            if (adjacent)
                return owner;
        }
        return null;
    }

    private static int RegisterBytes(Arm64Register reg) => reg switch
    {
        >= Arm64Register.B0 and <= Arm64Register.B31 => 1,
        >= Arm64Register.H0 and <= Arm64Register.H31 => 2,
        >= Arm64Register.W0 and <= Arm64Register.W31 or >= Arm64Register.S0 and <= Arm64Register.S31 => 4,
        >= Arm64Register.X0 and <= Arm64Register.X31 or >= Arm64Register.D0 and <= Arm64Register.D31 => 8,
        >= Arm64Register.V0 and <= Arm64Register.V31 => 16,
        _ => 0
    };

    /// <summary>
    /// Whole-vector loads whose normal-path emission materializes the register
    /// local wholesale (LDR/LDUR/LDP/LD1 of V registers). Lane windows stay
    /// opaque, but a later full-width store may read the register local.
    /// </summary>
    private static bool WholeVectorLoad(Arm64Instruction insn) => insn switch
    {
        { Mnemonic: Arm64Mnemonic.LDR or Arm64Mnemonic.LDUR or Arm64Mnemonic.LDP or Arm64Mnemonic.LD1,
          Op0Kind: Arm64OperandKind.Register, Op0Reg: >= Arm64Register.V0 and <= Arm64Register.V31 } => true,
        _ => false
    };

    /// <summary>
    /// Whole-register writes whose emitted local holds a plain scalar of the
    /// given width — the register local may safely stand in for its lanes.
    /// </summary>
    private static bool ScalarWholeRegisterWrite(Arm64Instruction insn, out int bits)
    {
        bits = 0;
        // Op0 is a read operand here, never a write: FP compares only set the
        // flags, and a store leaves its source register unchanged. Seeding
        // lanes for either would fabricate provenance the register never had.
        if (insn.Mnemonic is Arm64Mnemonic.FCMP or Arm64Mnemonic.FCMPE
                or Arm64Mnemonic.FCCMP or Arm64Mnemonic.FCCMPE
            || insn.MnemonicCategory is Arm64MnemonicCategory.Comparison
            || (insn.MnemonicCategory is Arm64MnemonicCategory.FloatingPointComparison
                && insn.Mnemonic is not Arm64Mnemonic.FCSEL)
            || insn.Mnemonic.ToString().StartsWith("ST", StringComparison.Ordinal))
            return false;
        bits = insn.Mnemonic switch
        {
            Arm64Mnemonic.LDRB or Arm64Mnemonic.LDURB
                or Arm64Mnemonic.LDRSB or Arm64Mnemonic.LDURSB => 8,
            Arm64Mnemonic.LDRH or Arm64Mnemonic.LDURH
                or Arm64Mnemonic.LDRSH or Arm64Mnemonic.LDURSH => 16,
            Arm64Mnemonic.LDR or Arm64Mnemonic.LDUR or Arm64Mnemonic.LDP => insn.Op0Reg switch
            {
                >= Arm64Register.B0 and <= Arm64Register.B31 => 8,
                >= Arm64Register.H0 and <= Arm64Register.H31 => 16,
                >= Arm64Register.S0 and <= Arm64Register.S31 => 32,
                >= Arm64Register.D0 and <= Arm64Register.D31 => 64,
                _ => 0 // 128-bit loads are opaque
            },
            // any other write to a scalar-width FP register (FADD/FDIV/FCSEL/
            // SCVTF/FMOV S,D / reductions) rewrites the register local as a
            // plain scalar — hardware zeroes the rest of the vector for S/D
            _ => insn.Op0Reg switch
            {
                >= Arm64Register.S0 and <= Arm64Register.S31 => 32,
                >= Arm64Register.D0 and <= Arm64Register.D31 => 64,
                _ => 0
            }
        };
        return bits != 0;
    }
}
