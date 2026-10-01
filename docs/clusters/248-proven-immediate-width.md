# An immediate proves as many bytes as the instruction that wrote it (castle-recovery#248)

A register write only proves the bytes it wrote. Before this rule the
generator guessed provenance from the value itself — an immediate that fit in
`uint` claimed four bytes — so a `movz x8` of a whole Double pattern kept its
diagnostic even though the X write proved every byte of the slot it filled,
while an `fmov s0, w8` could not tell a downstream `D` slot that only four
bytes were ever real.

Rules, in the arm64 lifter (`NewArmV8InstructionSet`, `Arm64VectorScalarizer`,
`ImmediateWriteWidth`), with `IlGenerator` only reading the result:

- `Immediate` carries `ProvenBytes`: how many bytes of `Value` the producing
  instruction provably describes. It is metadata, not identity — equality and
  hashing compare the value only, so SSA deduplication and constant folding
  are unchanged. `EffectiveProvenBytes` falls back to the old size-based guess
  when no provenance was recorded, so a 4-byte proof is never widened to 8.
- `MOV`/`MOVZ`/`MOVN` of an immediate writes the whole register: the lifted
  operand records `RegisterWidthBytes(Op0Reg)` proven bytes — eight for an X
  write, four for a W write. (Disarm folds `movk` chains into the `Or` the
  lifter already emits, so the composed value keeps the movz operand's width.)
  A scalar `MOVI`/`MVNI` records eight.
- `FMOV` into a scalar SIMD/FP destination marks the emitted `Move` with
  `NativeFloatWriteBits` (32 for `S`, 64 for `D`) — the S/D write width that
  would otherwise be erased. It is deliberately *not* `NativeFloatWidthBits`:
  that field seeds the local's managed type before inference, and a register
  written as `S` may be read back as a wider vector, so the write must not
  claim the whole local. `fmov s0, #imm` lifts as an untyped
  `Immediate(bit pattern, proven 4)`, not a `FloatLiteral`: a typed float
  literal would silently convert into a wider `Double` slot.
- The vector scalarizer propagates provenance through its folds: an extracted
  or composed lane records `min(inputs, lane width)`, an `fmov` GPR→FP
  forwarding `Move` and an `FP→FP` copy are marked with the write width, and
  `S`-window writes record four.
- `ImmediateWriteWidth.ApplyToMove` runs at lift time wherever a marked `Move`
  is emitted, in `InstructionSets/**`: the write width
  (`NativeFloatWriteBits` ?? `NativeIntegerWidthBits`) caps both the claim and
  the value — `filled = min(EffectiveProvenBytes, min(writeBytes, lane
  extent))`, and the recorded value keeps the write's low bytes sign-extended
  back to the long, so a lane that spelled -1 reads -1. A `V0.S1`-style lane
  destination caps at its own extent. Crucially the cap never extends: only
  the bytes the write produced are recorded, so a wider slot read of a
  narrower write stays diagnosed — zero-extension is not the slot's bytes.
- The `Double`/`Single` slot arm in `IlGenerator` accepts a literal only when
  `EffectiveProvenBytes` covers the slot: eight proven bytes emit
  `Int64BitsToDouble`/`Int32BitsToSingle` of the bit pattern, anything less
  stays diagnosed. A D/X-width write, or a movz/movk chain proving all eight
  bytes, fills a `Double` slot; an S/W write never fills it. This keeps the
  rule of #178: the binary must prove all bytes of the value it names.

Tests: `Cpp2IL.Core.Tests/Regression/ProvenWidthLiteralTests.cs` — `FMOV s0,
#imm` lifts as a 4-byte-proven bit pattern that fills a `Single` slot and stays
diagnosed read as `Double`; `MOVZ`/`MOVK` then `FMOV s0` marks 32 and `FMOV
d0` after a four-`MOVK` chain marks 64; a movz `x8` chain fills a `Double`
slot while the same value through a `w8` write or an `S` write stays
diagnosed; a narrow write keeps only its own bytes of the value. The
synthetic-slot tests thread the lifter's own marked `Move`, so they compile on
`development` and fail at runtime there.

Known gaps:

- `ConstantFolder` rewrites a folded `Or`/`Move` operand as `new Immediate(v)`,
  dropping recorded provenance — a `Move v2, Imm` inserted by a later pass
  inherits the 4-byte fallback and can stay diagnosed, and a movk-composed
  `Or` folded to a `uint`-sized value loses the X write's eight-byte claim.
  Preserving provenance there is a types-ssa-side change.
- A `MOVK`-composed `Or` records the unmasked composed value; the recorded
  value can exceed the register width the instruction actually wrote.
- Pass-inserted moves whose operand only becomes an `Immediate` after lifting
  never see `ApplyToMove`: such an immediate carries its own proven bytes
  unmasked by the write width. Routing it through the lifter's normalizer is
  types-ssa-side (the pass owns the move).
- The stricter S/W-write rule unmasked pre-existing slot-type defects: locals
  inference typed `Double`/`Int32` for what the binary wrote as a 4-byte S/W
  pattern (e.g. `float.NaN` bit patterns) now stay diagnosed instead of being
  filled by zero-extension. 74 of 98 methods that lost
  `Literal operand cannot fill` under the old zext rule relied on it; the
  remaining diagnoses belong to lane:types-ssa (`#249`), which owns the slot
  typing — `CastleClashers.Game CastleMaker::GetImpactedObjects` (float-NaN
  pattern typed `Double`, seven sites) and
  `CastleMaker::GetBottomPartAverageUpgradeLevel` (same pattern now typed
  `Int32`, emitting the honest bits `2143289344` plus one `Double` diagnosis
  elsewhere in the method) are examples.
