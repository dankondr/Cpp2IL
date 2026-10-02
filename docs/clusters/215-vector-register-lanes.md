# #215 — vector register as a tuple of lanes

Cluster: `vector-lane diagnostics` from `docs/P1_ROOT_CAUSES.md` mechanism 7 —
the compiler vectorises struct arithmetic (`Vector2/3`, `Color`), and the
lifter could not follow a lane through a branch, an `INS`/`DUP`, a permute, or
a narrow `LDR D`/`LDR S` window.

## Rule

A vector register is a tuple of lanes. `Arm64VectorScalarizer` tracks each
register as four 32-bit windows, each a `LaneSlice(operand, bitOffset)` naming
the local that provably holds that window's bits — never a slice of a
whole-register local, which may be a managed aggregate.

- A packed operation is one scalar op per lane (`fmul v0.2s,…` →
  `Multiply V0.S0, V0.S0, V2.S0` + `Multiply V0.S1, V0.S1, V2.S1`).
- `INS`/`MOV` element writes, `DUP` broadcasts, `EXT`, `ZIP1/ZIP2`,
  `UZP1/UZP2`, `TRN1/TRN2`, `REV64`, `LD1R` broadcasts, `LD1` element writes
  and `LD1` multi-structure loads are lane permutations or materializations —
  each emits the element-local `Move` and records which window it fills.
- Plainly offset-addressed narrow loads (`LDR/LDUR/LDP` S/D) materialize each
  covered window as an element local against the real memory operand, so a
  `D` load into a two-float location gives two honest lanes and a `D` store
  writes the fields one per lane — no `TEMP_VEC` shift of the register local.
- A merge of two definitions is a merge per lane. At every branch the proven
  windows are canonicalized so each outgoing edge carries real locals: window
  0's canonical home is the register local itself (`Move V0, value` — its low
  32 bits are the lane, and the field-recovery layer already resolves a
  whole-register read as that window); windows 1-3 live in their element
  registers (`Vn.Si`). At every branch target the incoming edges meet window
  by window — a window survives only when every converted predecessor proves
  it. A not-yet-converted (backward) edge contributes only what the loop body
  can change: the registers the span from the merge target through the
  back-edge's source may write — the header op itself, a vector
  destination, a call's clobber, an undecoded word, or a reachable inner
  merge — stay unproven, and every other register's proven lanes merge
  over the converted edges alone (the back-edge hands the same lanes back
  at the fixpoint). A span that cannot be bounded leaves the whole
  register unproven: consumers diagnose rather than guess.
- A constant window's bits ride beside the lane slice, so canonicalization
  rewriting an `Immediate`/`FloatLiteral` lane into its element register
  keeps the constant's provenance: merges meet window constants by equality
  across edges, and a store whose windows all carry equal bits stores the
  constant per 32-bit window rather than dropping to a diagnosed SIMD
  store — `MOVI Vn.2D,#0` feeding a loop of `STP`/`STR` zero stores writes
  each field window.
- Until the first clobber, an unwritten register's lanes are the entry lanes:
  window 0 is the register local itself, higher windows the entry element
  locals (undefined ones report `undefined local`, never guessed). A `BL`/call
  clobbers V0-V7 and V16-V31 outright and the upper halves of callee-saved
  V8-V15 — reads after the call can no longer spell stale pre-call lanes.
- A lane whose value is not proven stays diagnosed — `scalarized n of m
  lanes` or an `unproven` diagnostic. Nothing materializes an element local
  that no edge or instruction wrote.

## Test

`Cpp2IL.Core.Tests/Isil/Arm64VectorScalarizerTests.cs` lifts synthetic ARM64
words through the real conversion path:

- `MergedLaneFromTwoPredecessorsFeedsPackedMultiply` — a `DUP` path and an
  `LDR D` path meet at an `FMUL V0.2S`; both lanes multiply per-lane.
- `InsAndDupFeedPackedDivide` — `INS`/`DUP` element moves feed a packed
  `FDIV`.
- `ReloadedRegisterStoresFieldsAgain` — two `LDR D`→`STR D` copies move four
  fields as element locals with zero `ShiftRight`.
- `SingleStructureLoadProvesLanes`, `StructureLoadMaterializesLanes`,
  `ReplicateLoadBroadcastsEveryLane`, `PermutesMoveLanesIntoElementLocals`.
- `ProvenanceResetsAtMergeTargets`, `BackwardEdgeLeavesLanesUnproven` — a
  window unproven on any edge stays diagnosed; nothing is guessed.
- `LoopInvariantZeroVectorStoresPerWindow` — `MOVI V0.2D,#0` above a loop
  whose only stores are `STP`/`STR` of `V0`: the back edge does not clobber
  it, every 32-bit window stores `Immediate 0`, and the post-index
  writeback survives.
