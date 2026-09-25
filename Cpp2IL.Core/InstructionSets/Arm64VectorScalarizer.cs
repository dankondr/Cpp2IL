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
/// bit width. Permutes, sub-32-bit element writes, wide loads and opaque or
/// unsupported vector ops leave the corresponding windows unproven.
/// Provenance resets at branch targets since a merge may join paths that
/// built the register differently, and at an unproven consumption the pass
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
        public bool Whole;
    }

    private readonly Dictionary<string, VectorState> _vectors = new();
    private readonly Dictionary<string, Register> _shiftTemps = new();
    private readonly HashSet<ulong> _mergeTargets = new();
    private readonly HashSet<string> _claimedDests = new();
    private int _tempCounter;
    private bool _sawIndirectJump;

    private Func<ulong, OpCode, List<IOperand>, Instruction> _add = null!;
    private ulong _address;
    private bool _emitted;

    private static readonly Immediate Zero = new(0);

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

    /// <summary>
    /// Called once per method before conversion. Records every intra-method
    /// branch target so provenance can be dropped where control flow merges.
    /// </summary>
    public void Begin(IReadOnlyList<Arm64Instruction> instructions)
    {
        _vectors.Clear();
        _shiftTemps.Clear();
        _mergeTargets.Clear();
        _claimedDests.Clear();
        _tempCounter = 0;
        _sawIndirectJump = false;

        foreach (var insn in instructions)
        {
            switch (insn.Mnemonic)
            {
                case Arm64Mnemonic.B:
                    _mergeTargets.Add(insn.BranchTarget);
                    break;
                case Arm64Mnemonic.BC:
                    _mergeTargets.Add(insn.Op0PcRelImm);
                    break;
                case Arm64Mnemonic.CBZ or Arm64Mnemonic.CBNZ:
                    _mergeTargets.Add((ulong)((long)insn.Address + insn.Op1Imm));
                    break;
                case Arm64Mnemonic.TBZ or Arm64Mnemonic.TBNZ:
                    _mergeTargets.Add((ulong)((long)insn.Address + insn.Op2Imm));
                    break;
            }
        }
    }

    /// <summary>
    /// Called before each instruction is converted. A branch target may be
    /// reached by a path that built each vector differently, so all lane state
    /// is dropped there; the same applies after an indirect jump whose targets
    /// cannot be enumerated.
    /// </summary>
    public void BeginInstruction(ulong address)
    {
        _claimedDests.Clear();
        if (_mergeTargets.Contains(address) || _sawIndirectJump)
            _vectors.Clear();
    }

    /// <summary>
    /// Attempt to emit scalar equivalents for <paramref name="insn"/>. Returns
    /// true when the instruction was fully handled — folded to lane ops or
    /// reported via an explicit diagnostic — and false when the caller should
    /// run its normal lowering path.
    /// </summary>
    public bool TryConvert(Arm64Instruction insn,
        Func<ulong, OpCode, List<IOperand>, Instruction> add,
        Func<Arm64Instruction, int, IOperand> convertOperand)
    {
        _add = add;
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
        if (insn.Mnemonic is Arm64Mnemonic.BR or Arm64Mnemonic.BLR)
            _sawIndirectJump = true; // jump-table targets cannot be enumerated

        // stores read the register rather than writing it — no invalidation
        if (insn.Mnemonic is Arm64Mnemonic.STR or Arm64Mnemonic.STUR or Arm64Mnemonic.STP
            or Arm64Mnemonic.STRB or Arm64Mnemonic.STRH or Arm64Mnemonic.STURB or Arm64Mnemonic.STURH)
            return;

        if (insn.Op0Kind != Arm64OperandKind.Register || !IsVectorRegister(insn.Op0Reg))
            return;

        var name = Normalize(insn.Op0Reg);
        if (_claimedDests.Remove(name))
            return; // lane state was already written by this pass

        if (WholeVectorLoad(insn))
        {
            // plainly offset-addressed loads also materialize each 32-bit window
            // as its own element local, so downstream lane ops see real
            // provenance instead of an opaque blob.
            var windowed = insn.Mnemonic != Arm64Mnemonic.LD1
                && insn.MemIndexMode == Arm64MemoryIndexMode.Offset
                && insn.MemAddendReg == Arm64Register.INVALID
                && insn.MemBase != Arm64Register.INVALID;
            RecordVectorLoad(insn, insn.Op0Reg, insn.MemOffset, windowed);
            if (insn.Mnemonic is Arm64Mnemonic.LDP or Arm64Mnemonic.LD1
                && insn.Op1Kind == Arm64OperandKind.Register && IsVectorRegister(insn.Op1Reg))
            {
                RecordVectorLoad(insn, insn.Op1Reg, insn.MemOffset + 16, windowed);
            }
            return;
        }

        if (ScalarWholeRegisterWrite(insn, out var writtenBits))
        {
            var state = Ensure(insn.Op0Reg);
            for (var i = 0; i < 4; i++)
                state.Slots[i] = 32 * i < writtenBits ? new LaneSlice(Reg(insn.Op0Reg), 32 * i) : new LaneSlice(Zero, 0);
            state.Whole = false; // the local now holds only the narrow scalar

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
                        second.Slots[i] = 32 * i < secondBits ? new LaneSlice(Reg(insn.Op1Reg), 32 * i) : new LaneSlice(Zero, 0);
                    second.Whole = false;
                }
            }
            return;
        }

        if (_vectors.TryGetValue(name, out var existing))
        {
            for (var i = 0; i < 4; i++)
                existing.Slots[i] = null; // opaque write: lanes no longer provable
            existing.Whole = false;
        }
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
            _vectors[name] = state = new();
        return state;
    }

    private void ClaimDest(Arm64Register reg)
    {
        _claimedDests.Add(Normalize(reg));
        // a lane-level write leaves the whole-register local stale
        if (_vectors.TryGetValue(Normalize(reg), out var state))
            state.Whole = false;
    }

    /// <summary>
    /// Records what a whole-vector load proved about <paramref name="reg"/>.
    /// Windowed loads emit one element-local Move per 32-bit window so lane
    /// ops and extracts can read real locals; other loads mark only the whole
    /// register local as current and leave every window unproven.
    /// </summary>
    private void RecordVectorLoad(Arm64Instruction insn, Arm64Register reg, long offset, bool windowed)
    {
        var state = Ensure(reg);
        if (!windowed)
        {
            for (var i = 0; i < 4; i++)
                state.Slots[i] = null; // lanes opaque, but the local itself is current
            state.Whole = true;
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
            state.Slots[i] = new LaneSlice(laneReg, 0);
        }
        state.Whole = true; // the caller's normal-path Move materialized Vn too
    }

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
    private IOperand? SlotOperand(VectorState state, int slot)
    {
        if (state.Slots[slot] is not { } slice)
            return null;

        var (operand, offset) = slice;
        if (operand is Immediate imm)
            return new Immediate(unchecked((int)(uint)(imm.UnsignedValue >> offset)));
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
    private IOperand? Lane64Operand(VectorState state, int lane)
    {
        var lo = state.Slots[2 * lane];
        var hi = state.Slots[2 * lane + 1];
        if (lo == null || hi == null)
            return null;

        if (lo.Value.BitOffset == 0 && hi.Value.BitOffset == 32
            && lo.Value.Operand.Equals(hi.Value.Operand))
            return lo.Value.Operand; // one operand already covers the whole lane

        var loOp = SlotOperand(state, 2 * lane);
        var hiOp = SlotOperand(state, 2 * lane + 1);
        if (loOp == null || hiOp == null)
            return null;

        var loMasked = Temp();
        _add(_address, OpCode.And, [loMasked, loOp, new Immediate(0xFFFFFFFFL)]);
        var hiShifted = Temp();
        _add(_address, OpCode.ShiftLeft, [hiShifted, hiOp, new Immediate(32)]);
        var composed = Temp();
        _add(_address, OpCode.Or, [composed, hiShifted, loMasked]);
        return composed;
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

    private IOperand? NarrowElementOperand(VectorState state, int slot, int offsetInSlot, int bits)
    {
        var slotOp = SlotOperand(state, slot);
        if (slotOp == null)
            return null;
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
        // (value << (32 - off - bits)) >> (32 - bits): arithmetic shift sign-extends.
        var left = Temp();
        _add(_address, OpCode.ShiftLeft, [left, slotOp, new Immediate(32 - offset % 32 - bits)]);
        var extended = Temp();
        _add(_address, OpCode.ShiftRight, [extended, left, new Immediate(32 - bits)]);
        return extended;
    }

    private void EmitLaneOp(OpCode opCode, string destName, int laneBits, int lane,
        IOperand left, IOperand right, VectorState dest, bool isFloat = false)
    {
        var destReg = ElementRegister(destName, laneBits, lane);
        var emitted = _add(_address, opCode, [destReg, left, right]);
        if (!isFloat && laneBits == 32)
            emitted.NativeIntegerWidthBits = 32;
        _emitted = true;
        dest.Slots[lane * laneBits / 32] = new LaneSlice(destReg, 0);
        if (laneBits == 64)
            dest.Slots[lane * 2 + 1] = new LaneSlice(destReg, 32);
    }

    private static bool IsLaneWiseBinop(Arm64Mnemonic mnemonic) => mnemonic is
        Arm64Mnemonic.AND or Arm64Mnemonic.ORR or Arm64Mnemonic.EOR
        or Arm64Mnemonic.BIC or Arm64Mnemonic.ORN or Arm64Mnemonic.EON
        or Arm64Mnemonic.ADD or Arm64Mnemonic.SUB or Arm64Mnemonic.MUL
        or Arm64Mnemonic.MLA or Arm64Mnemonic.MLS or Arm64Mnemonic.ADDP
        or Arm64Mnemonic.FADD or Arm64Mnemonic.FSUB or Arm64Mnemonic.FMUL or Arm64Mnemonic.FDIV;

    private static bool IsBitwise(Arm64Mnemonic mnemonic) => mnemonic is
        Arm64Mnemonic.AND or Arm64Mnemonic.ORR or Arm64Mnemonic.EOR
        or Arm64Mnemonic.BIC or Arm64Mnemonic.ORN or Arm64Mnemonic.EON;

    private static bool InvertsSecondOperand(Arm64Mnemonic mnemonic)
        => mnemonic is Arm64Mnemonic.BIC or Arm64Mnemonic.ORN or Arm64Mnemonic.EON;

    private static bool IsFloatLaneOp(Arm64Mnemonic mnemonic) => mnemonic is
        Arm64Mnemonic.FADD or Arm64Mnemonic.FSUB or Arm64Mnemonic.FMUL or Arm64Mnemonic.FDIV;

    private bool TryConvertCore(Arm64Instruction insn, Func<Arm64Instruction, int, IOperand> convertOperand)
    {
        if (IsLaneWiseBinop(insn.Mnemonic)
            && insn.Op0Kind == Arm64OperandKind.Register
            && insn.Op1Kind == Arm64OperandKind.Register
            && insn.Op2Kind == Arm64OperandKind.Register
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
                // unreachable until Disarm decodes shift-right-by-immediate
                // (Task 1); meanwhile exercised via manual fixtures
                return LowerShiftImmediate(insn, OpCode.ShiftRight);

            case Arm64Mnemonic.STR or Arm64Mnemonic.STUR or Arm64Mnemonic.STP
                when insn.Op0Kind == Arm64OperandKind.Register
                    && IsVectorRegister(insn.Op0Reg)
                    && insn.MemIndexMode == Arm64MemoryIndexMode.Offset
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
        _add = add;
        _address = insn.Address;
        _emitted = false;

        if (insn.Op0Kind != Arm64OperandKind.Register
            || insn.Op0Arrangement == Arm64ArrangementSpecifier.None)
            return false;

        var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
        var destName = Normalize(insn.Op0Reg);

        IOperand source;
        if (insn.Op1Kind == Arm64OperandKind.Register)
            source = convertOperand(insn, 1);
        else if (insn.Op1Kind == Arm64OperandKind.VectorRegisterElement)
        {
            var sourceState = State(insn.Op1Reg);
            source = sourceState != null ? ElementOperand(sourceState, insn.Op1VectorElement) : null;
            source ??= ElementRegister(Normalize(insn.Op1Reg), ElementBits(insn.Op1VectorElement), insn.Op1VectorElement.Index);
        }
        else
            return false;

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);

        var slotsUsed = laneCount * laneBits / 32;
        for (var lane = 0; lane < laneCount; lane++)
        {
            var laneReg = ElementRegister(destName, laneBits, lane);
            _add(_address, OpCode.Move, [laneReg, source]);
            _emitted = true;
            if (laneBits == 32)
                dest.Slots[lane] = new LaneSlice(laneReg, 0);
            else if (laneBits == 64)
            {
                dest.Slots[lane * 2] = new LaneSlice(laneReg, 0);
                dest.Slots[lane * 2 + 1] = new LaneSlice(laneReg, 32);
            }
            // 8/16-bit lanes cannot be represented at 32-bit granularity: the
            // element Moves are still emitted faithfully, slots stay unproven.
        }
        if (laneBits < 32)
            for (var slot = 0; slot < slotsUsed; slot++)
                dest.Slots[slot] = null; // bytes rewritten at sub-window granularity
        for (var slot = slotsUsed; slot < 4; slot++)
            dest.Slots[slot] = new LaneSlice(Zero, 0); // 64-bit forms zero the upper half

        if (!_emitted)
            _add(_address, OpCode.Nop, []);
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
        ClaimDest(insn.Op0Reg);

        var element = insn.Op0VectorElement;
        var elementBits = ElementBits(element);
        var destName = Normalize(insn.Op0Reg);
        var elementReg = ElementRegister(destName, elementBits, element.Index);

        IOperand source;
        if (insn.Op1Kind == Arm64OperandKind.VectorRegisterElement)
        {
            var sourceState = State(insn.Op1Reg);
            source = sourceState != null ? ElementOperand(sourceState, insn.Op1VectorElement) : null;
            source ??= ElementRegister(Normalize(insn.Op1Reg), ElementBits(insn.Op1VectorElement), insn.Op1VectorElement.Index);
        }
        else
            source = convertOperand(insn, 1);

        _add(_address, OpCode.Move, [elementReg, source]);
        _emitted = true;

        switch (elementBits)
        {
            case 32:
                dest.Slots[element.Index] = new LaneSlice(elementReg, 0);
                break;
            case 64:
                dest.Slots[element.Index * 2] = new LaneSlice(elementReg, 0);
                dest.Slots[element.Index * 2 + 1] = new LaneSlice(elementReg, 32);
                break;
            default:
                dest.Slots[elementBits * element.Index / 32] = null; // partial-window write
                break;
        }
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
        if (source == null)
            return false; // opaque vector: caller's normal path

        var element = insn.Op1VectorElement;
        var bits = ElementBits(element);
        var laneOp = unsigned ? ElementOperand(source, element) : SignedElementOperand(source, element);
        if (laneOp == null)
        {
            Diagnostic($"ARM64 SIMD lane {Normalize(insn.Op1Reg)}.{ElementLetter(bits)}{element.Index} is unproven; extraction is not safe.");
            return true;
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
                _add(_address, OpCode.Move, [laneReg, laneLiteral]);
                _emitted = true;
                if (laneBits == 32)
                    dest.Slots[lane] = new LaneSlice(laneReg, 0);
                else if (laneBits == 64)
                {
                    dest.Slots[lane * 2] = new LaneSlice(laneReg, 0);
                    dest.Slots[lane * 2 + 1] = new LaneSlice(laneReg, 32);
                }
            }
            if (laneBits < 32)
                for (var slot = 0; slot < slotsUsed; slot++)
                    dest.Slots[slot] = null;
            for (var slot = slotsUsed; slot < 4; slot++)
                dest.Slots[slot] = new LaneSlice(Zero, 0);
            return true;
        }

        // scalar GPR -> FP: FMOV Sd/Dd, Wn/Xn — a scalar-defining write
        if (destIsScalarFp && insn.Op1Kind == Arm64OperandKind.Register && IsGpr(insn.Op1Reg))
        {
            _add(_address, OpCode.Move, [convertOperand(insn, 0), convertOperand(insn, 1)]);
            _emitted = true;
            var dest = Ensure(insn.Op0Reg);
            var width = insn.Op0Reg is >= Arm64Register.D0 and <= Arm64Register.D31 ? 64 : 32;
            for (var i = 0; i < 4; i++)
                dest.Slots[i] = 32 * i < width ? new LaneSlice(Reg(insn.Op0Reg), 32 * i) : new LaneSlice(Zero, 0);
            ClaimDest(insn.Op0Reg);
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
            _add(_address, OpCode.Move, [convertOperand(insn, 0), laneOp]);
            _emitted = true;
            var dest = Ensure(insn.Op0Reg);
            for (var i = 0; i < 4; i++)
                dest.Slots[i] = 32 * i < (width64 ? 64 : 32) ? new LaneSlice(Reg(insn.Op0Reg), 32 * i) : new LaneSlice(Zero, 0);
            ClaimDest(insn.Op0Reg);
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
            _add(_address, OpCode.Move, [convertOperand(insn, 0), new Immediate(value)]);
            _emitted = true;
            dest.Slots[0] = new LaneSlice(Reg(insn.Op0Reg), 0);
            dest.Slots[1] = new LaneSlice(Reg(insn.Op0Reg), 32);
            dest.Slots[2] = new LaneSlice(Zero, 0);
            dest.Slots[3] = new LaneSlice(Zero, 0);
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
                _add(_address, OpCode.Move, [laneReg, new Immediate(lane64)]);
                _emitted = true;
                dest.Slots[lane * 2] = new LaneSlice(laneReg, 0);
                dest.Slots[lane * 2 + 1] = new LaneSlice(laneReg, 32);
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
                _add(_address, OpCode.Move, [laneReg, new Immediate(window)]);
                _emitted = true;
                dest.Slots[slot] = new LaneSlice(laneReg, 0);
            }
        }
        for (var slot = slotsUsed; slot < 4; slot++)
            dest.Slots[slot] = new LaneSlice(Zero, 0);
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
                dest.Slots[slot] = null;
            for (var slot = slotsUsed; slot < 4; slot++)
                dest.Slots[slot] = new LaneSlice(Zero, 0);
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
            dest.Slots[slot] = new LaneSlice(laneReg, 0);
        }
        for (var slot = slotsUsed; slot < 4; slot++)
            dest.Slots[slot] = new LaneSlice(Zero, 0);
        return true;
    }

    /// <summary>SHL/USHR/SSHR Vd.T, Vn.T, #imm: a per-lane shift at the element width.</summary>
    private bool LowerShiftImmediate(Arm64Instruction insn, OpCode op)
    {
        var (laneBits, laneCount) = Arrangement(insn.Op0Arrangement);
        var source = LaneState(insn.Op1Reg);
        if (source == null)
            return false;

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        var destName = Normalize(insn.Op0Reg);
        var slotsUsed = laneCount * laneBits / 32;

        var proven = laneBits is 32 or 64;
        var operands = new IOperand?[laneCount];
        if (proven)
            for (var lane = 0; lane < laneCount; lane++)
            {
                operands[lane] = laneBits == 32 ? SlotOperand(source, lane) : Lane64Operand(source, lane);
                proven &= operands[lane] != null;
            }

        if (!proven)
        {
            for (var slot = 0; slot < slotsUsed; slot++)
                dest.Slots[slot] = null;
            for (var slot = slotsUsed; slot < 4; slot++)
                dest.Slots[slot] = new LaneSlice(Zero, 0);
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} has unproven lane provenance; scalarization skipped.");
            return true;
        }

        for (var lane = 0; lane < laneCount; lane++)
            EmitLaneOp(op, destName, laneBits, lane, operands[lane]!, new Immediate(insn.Op2Imm), dest);
        for (var slot = slotsUsed; slot < 4; slot++)
            dest.Slots[slot] = new LaneSlice(Zero, 0);
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

        var sourceA = LaneState(insn.Op1Reg);
        var sourceB = LaneState(insn.Op2Reg);
        var sourceD = accumulates ? LaneState(insn.Op0Reg) : null;

        if (sourceA == null && sourceB == null && sourceD == null)
            return false; // fully opaque chain: caller's normal path

        var dest = Ensure(insn.Op0Reg);
        ClaimDest(insn.Op0Reg);
        var destName = Normalize(insn.Op0Reg);

        var supported = bitwise || laneBits is 32 or 64;
        var rows = bitwise ? vectorSlots : laneCount;
        var aOps = new IOperand?[rows];
        var bOps = new IOperand?[rows];
        var dOps = new IOperand?[rows];
        var anyLaneProven = false;

        for (var lane = 0; lane < rows; lane++)
        {
            if (insn.Mnemonic == Arm64Mnemonic.ADDP)
            {
                // out[i] = in1[2i]+in1[2i+1] for the lower half, in2 for the upper
                var pairSource = lane < laneCount / 2 ? sourceA : sourceB;
                var pair = lane < laneCount / 2 ? lane : lane - laneCount / 2;
                aOps[lane] = LaneOperand(pairSource, laneBits, 2 * pair);
                bOps[lane] = LaneOperand(pairSource, laneBits, 2 * pair + 1);
            }
            else if (bitwise)
            {
                aOps[lane] = sourceA == null ? null : SlotOperand(sourceA, lane);
                bOps[lane] = sourceB == null ? null : SlotOperand(sourceB, lane);
            }
            else
            {
                aOps[lane] = LaneOperand(sourceA, laneBits, lane);
                bOps[lane] = LaneOperand(sourceB, laneBits, lane);
            }

            if (accumulates)
                dOps[lane] = bitwise ? SlotOperand(sourceD!, lane) : LaneOperand(sourceD, laneBits, lane);

            var laneProven = aOps[lane] != null && bOps[lane] != null
                && (!accumulates || dOps[lane] != null);
            anyLaneProven |= laneProven;
        }

        if (!supported || !anyLaneProven)
        {
            for (var slot = 0; slot < vectorSlots; slot++)
                dest.Slots[slot] = null;
            for (var slot = vectorSlots; slot < 4; slot++)
                dest.Slots[slot] = new LaneSlice(Zero, 0);
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
                    dest.Slots[lane] = null;
                else
                    for (var w = lane * laneBits / 32; w < (lane + 1) * laneBits / 32; w++)
                        dest.Slots[w] = null;
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
                    destName, laneBits, lane, dOps[lane]!, product, dest);
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
            EmitLaneOp(op, destName, bitwise ? 32 : laneBits, lane, a, b, dest, isFloat);
        }
        for (var slot = vectorSlots; slot < 4; slot++)
            dest.Slots[slot] = new LaneSlice(Zero, 0);
        if (unprovenLanes > 0)
            Diagnostic($"ARM64 SIMD {insn.Mnemonic} has unproven lane provenance; scalarized {rows - unprovenLanes} of {rows} lanes.");
        return true;
    }

    private IOperand? LaneOperand(VectorState? state, int laneBits, int lane)
        => state == null ? null : laneBits == 32 ? SlotOperand(state, lane) : Lane64Operand(state, lane);

    /// <summary>
    /// STR/STUR/STP of a vector register: a fully proven vector is stored as
    /// per-window scalar Moves, a partially proven one is diagnosed, and an
    /// opaque one falls through to the caller's path.
    /// </summary>
    private bool LowerStore(Arm64Instruction insn)
    {
        var first = State(insn.Op0Reg);
        if (first == null)
            return false;
        var pair = insn.Mnemonic == Arm64Mnemonic.STP;
        var second = pair ? State(insn.Op1Reg) : null;
        if (pair && second == null)
            return false;

        var bytes = RegisterBytes(insn.Op0Reg);
        if (bytes < 4)
            return false;

        // an unproven store is left to the caller's normal path: it emits the
        // whole-register move the baseline produced — correct whenever the
        // register local was materialized by a load or a scalar write.
        if (bytes == 16 && first.Whole && (!pair || second!.Whole))
            return false;

        var slots = bytes / 4;

        var proven = true;
        for (var slot = 0; slot < slots; slot++)
            proven &= first.Slots[slot] != null;
        if (pair)
            for (var slot = 0; slot < slots; slot++)
                proven &= second!.Slots[slot] != null;

        if (!proven)
            return false;

        for (var r = 0; r < (pair ? 2 : 1); r++)
        {
            var state = r == 0 ? first : second!;
            for (var slot = 0; slot < slots; slot++)
            {
                var op = SlotOperand(state, slot);
                if (op == null)
                    continue;
                IOperand mem = insn.MemBase == Arm64Register.X31
                    ? new StackOffset((int)(insn.MemOffset + r * bytes + slot * 4))
                    : new MemoryOperand(Reg(insn.MemBase), addend: insn.MemOffset + r * bytes + slot * 4, accessSize: 4);
                _add(_address, OpCode.Move, [mem, op]).NativeMemoryAccessSize = 4;
                _emitted = true;
            }
        }
        return true;
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
