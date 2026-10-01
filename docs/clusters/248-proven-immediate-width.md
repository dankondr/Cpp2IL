# An immediate proves as many bytes as the instruction that made it (castle-recovery#248)

A 32-bit move writes four bytes; a whole-register literal proves eight. Before
this rule the generator guessed provenance from the value itself — an immediate
that fit in `uint` claimed four bytes — so a `fmov s0, w8` of a full Single, or
a `movz x8` of a whole Double pattern, kept its diagnostic even though the
instruction proved every byte of the slot it filled.

Rules, in the arm64 lifter (`NewArmV8InstructionSet`, `Arm64VectorScalarizer`)
and the `Move` arm of `IlGenerator`:

- `Immediate` carries `ProvenBytes`: how many bytes of `Value` the producing
  instruction provably describes. It is metadata, not identity — equality and
  hashing compare the value only, so SSA deduplication and constant folding are
  unchanged. `EffectiveProvenBytes` falls back to the old size-based guess when
  no provenance was recorded, so a 4-byte proof is never widened to 8.
- `MOV`/`MOVZ`/`MOVN` of an immediate writes the whole register: the lifted
  operand records eight proven bytes (Disarm folds `movk` chains into the `Or`
  the lifter already emits, so the composed value keeps the `movz` operand's
  width). `MOVI` of a scalar or `D` lane likewise records eight.
- `FMOV` into a scalar SIMD/FP destination marks the emitted `Move` with
  `NativeFloatWriteBits` (32 for `S`, 64 for `D`) — the S/D write width that
  normalization erased. It is deliberately *not* `NativeFloatWidthBits`: that
  field seeds the local's managed type before inference, and a register written
  as `S` may be read back as a wider vector, so the write must not claim the
  whole local. A `DoubleLiteral` folded into an `S` destination is a
  `FloatLiteral`.
- The vector scalarizer propagates provenance through its folds: an extracted
  or composed lane records `min(inputs, lane width)`, an `fmov` GPR→FP
  forwarding `Move` and an `FP→FP` copy are marked with the write width, and
  `S`-window writes record four.
- In `IlGenerator`, every `Move` of an immediate is normalized against the
  write that produced it: `NativeFloatWriteBits` (an S/D write) or
  `NativeIntegerWidthBits` sets the write width, and a `V0.S1`-style lane
  extent caps it. `filled = min(extent, 8)` when the source's proven bytes
  cover the write — an S write zero-extends, so all eight bytes of a later D
  read are proven — else `min(proven, extent)`; the recorded value is masked
  to the write width. A move carrying no mark is a pass-inserted copy and the
  source's proven bytes stand.
- The `Double`/`Single` slot arm accepts a literal only when `ProvenBytes`
  covers the slot: eight proven bytes emit `Ldc_R8`/`Ldc_R4` of the bit
  pattern, anything less stays diagnosed. This keeps the rule of #178: the
  binary must prove all bytes of the value it names.

Tests: `Cpp2IL.Core.Tests/Regression/ProvenWidthLiteralTests.cs` — `FMOV s0, #imm`
lifts as a `FloatLiteral` carrying a 32-bit write mark; `MOVZ`/`MOVK` then
`FMOV s0` marks 32 and `FMOV d0` after a four-`MOVK` chain marks 64; an
S-write immediate zero-extends to fill a `Double` slot via
`Int64BitsToDouble`, masking anything the write never took; a 4-byte proof
into a `Double` slot keeps the diagnostic. The synthetic-slot tests thread
the lifter's own marked `Move`, so they compile on `development` and fail at
runtime there.

Known gaps:

- `ConstantFolder` rewrites a folded `Or`/`Move` operand as `new Immediate(v)`,
  dropping recorded provenance — a `Move v2, Imm` inserted by a later pass
  inherits the 4-byte fallback and can stay diagnosed. Preserving provenance
  there is a types-ssa-side change.
- A `MOVK`-composed `Or` records the unmasked composed value; the recorded
  value can exceed the register width the instruction actually wrote.
