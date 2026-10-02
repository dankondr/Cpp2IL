# #272 — aggregate lane reads typed by the covered field

Cluster: `type: no legal conversion` and `type: synthetic default in
operand slot` residuals of the form `Aggregate→Scalar` /
`Scalar→Aggregate` where the scalar reads or fills a declared field's
bytes inside the aggregate (castle-recovery#272). Prior slice:
castle-recovery#262 → `0589ade7`.

## Rule

A read of 4 (or 8) bytes from a local whose inferred type is an aggregate —
`List<T>.Enumerator`, `Vector3`, a `KeyValuePair` — is typed by the field
the bytes cover, not by the aggregate, whenever that covered field is
proven. Before, a whole-local operand kept the aggregate's type, so a
`Move singleDest, enumLocal` diagnosed `Enumerator→Vector3`/`KVP→Single`
even though the bytes read are a declared member.

`SplitMoveOperandViews` (in `LocalVariables.SplitScalarOperandViews`) now
applies the same covered-field rule on both sides of a `Move`:

- **Scalar destination, aggregate source**: `LaneOperand` resolves the
  field path covering `[byteOffset, byteOffset + laneWidth)` via
  `MetadataResolver.FindCoveredInstanceFieldPathAtOffset` — a flat leaf
  whose storage size equals the access, else a nested path through
  value-typed containers down to an exact-width leaf — and rewrites the
  operand to `local.<path>` (or `field.<containers>.<path>` for a
  field-typed operand). `byteOffset` is the operand's own `Vn.Sk` lane
  view when present (`LaneViewByteOffset`), else the destination slot's
  lane offset, so `Move V0.S2, v1662` reads `v1662`'s bytes at 8.
- **Aggregate destination, narrower source**: the store's *proven* width
  (`NativeMemoryAccessSize`, else a typed operand's storage size, a
  floating literal's encoding, or `Immediate.ProvenBytes`) selects the
  covered field and the destination becomes `local.<covered>` — an
  `AggregateFieldWritableFrom`-gated member store. An unproven source
  width keeps the whole-destination diagnostic: `Move span, 0` stays a
  whole-aggregate default, not a guessed 8-byte `_pointer` store.
- **Aggregate destination, wider source**: the source narrows to the
  field covering the destination's bytes — the same covered-field rule.

Four gates keep the projection honest:

- `LocalAggregateTypeSettled` — the aggregate type must not be a register
  guess a later inference can restamp: a computed definition (arithmetic,
  bitwise, shifts, conversions, `ShiftStack`) vetoed transitively through
  `Move`/`Phi` copies, while call/`Newobj`/copy-defined and undefined
  root locals count their declared type as settled. A restamped slot
  would leave the projected member dangling and substitute a default
  where control read the real value. A `Move`/`Phi` copy only carries the
  claim forward when its source holds the same type — `v3 = scalar`
  takes its type from the slot it stores into, so the scalar source's own
  computed definition cannot unsettle it. A computed definition itself
  still vetoes unless every operand carries the marked type (`v3 = v2 +
  v1`), or — for `Multiply`/`Divide` only — the other operands are scalar
  lanes or literals (`v3 = v2 * s` is a real vector scaling; `v = base -
  1` is address arithmetic that proves a width, not the base's type).
- `LaneValueSpellable` — the lane spells only when the host does, now
  extended for the `_current` leaf of an inlined generic enumerator:
  `Move v3878, dictEnum._current` makes `v3878` spellable through
  `get_Current` (`InlinedEnumeratorCurrentCandidate`, now internal), so
  `v3878.key.x` projects once and the referent-memo machinery reports a
  single named operand slot instead of one conversion per use.
- `CoveredStoreValueCompatible` — a covered-field store must be a value
  the leaf can honestly hold: a typed source needs the leaf's exact type
  for value-typed members or assignability for reference members, and an
  untyped source (a raw pointer expression) only lands in a leaf whose
  type is a primitive or enum — never a managed reference member, which
  would lose the unmanaged-memory diagnostic the pointer carries.
- The whole-value guard — a store through a scalar field slot whose
  source already spells the slot's whole aggregate value (the writable
  container reference the emitter substitutes for the member, per
  `IlGenerator.WholeValueContainerReference`) stays a whole-value store
  instead of being re-split onto the member's lane; only genuinely
  narrower sources split the scalar sources. The deferral applies only
  when the leaf the store targets covers the container's whole minimum
  size and the container field is writable from the method — a 4-byte
  `x` leaf does not cover a 12-byte `Vector3` container, so `x/y/z`
  lane-store runs stay split where `InlinedMemberRecovery` can re-pack
  them into one whole-struct store.
- `LocalDefinedBytesCover` — a scalar store narrows to the covered
  member only when the destination local's bytes were all materialized
  by the program: member stores union their written spans, whole-value
  `Move`/`Call`/`Newobj` definitions cover the slot, a `Phi` contributes
  the bytes every input covers, and a computed op contributes its
  proven width. When uncovered bytes remain — e.g. the second lane of
  an `FMOV`/`FCSEL` pair the decoder never emitted — the operand keeps
  its aggregate type and the conversion stays diagnosed instead of
  emitting `default` plus partial field stores as clean.

Reads and stores whose covered field is *not* proven — private members
the method cannot spell, whole-struct phi merges (`Enumerator→Vector3`,
`V3→Color`) where no single field covers the bytes — keep their
diagnostic unchanged.

## Register-lane typing gate

Aggregate types travel `Move`/`Phi` edges only where the copy's own
width can carry them. `TypeFitsRegisterLane` (in `LocalVariables`)
now caps any aggregate type propagated onto a `V`/`Q` vector register
or a `Vn.Sk`/`Vn.Dk` lane view at that register's whole-lane coverage
(`RegisterCoverageBytes`: V/Q = 16) or the lane view's element width —
a `mov v0.16b` copies 16 bytes, so a 24-byte `Enumerator` on `V0`
cannot be the register's value type. Scalar registers (`W`/`X`/`S`/`D`),
virtual names and `stack_*` cells carry types by convention (pointer to
the aggregate, or the value itself), so they pass through unchanged.
The gate applies on `PropagateMove`/`PropagatePhi` in both directions,
`Move local,field`/`field,local`, element loads/stores and array
elements, and the hidden-return-buffer alias walk
(`ResolveHiddenReturnBuffers`).

## Covered-span note (emit side)

A `Move` whose own width — `NativeMemoryAccessSize` when marked (`0`
is the float/vector "unmarked" convention, not a width), else the
stack slot's whole type, the lane view's element width, or the
register's coverage — is narrower than the source's declared value
type cannot deliver the whole value. `IlGenerator` now names that
honestly: `A N-byte move covers only part of the M-byte T value
(covered members): the uncovered span is an implicit fill, not a
stored value`, and the slot gets `default` instead of a
whole-type conversion the move cannot satisfy. Same-type copies are
whole copies and are exempt.

## Numbers (gate control `18a7d759` vs branch `5b4a2b47`, r241 /
Castle Busters 1.11.1 — re-measured after `origin/development`
adopted #200 vector-register lanes)

Pre-merge gate (`tools/codeverify/gate.py`, control = merge base
`18a7d759`, branch = `5b4a2b47`): **Verdict PASS** — game-owned
methods **cleared 20, regressed 57** (every regressed method named
below); ILVerify transitions **none**; silent wrong-recovery compare
`empty-diamond` **4 → 3 (0 new, 1 gone)**, `uninit-read` 16 → 16,
no new silent hits in any class; corpus oracle **0 match→mismatch**
(359/623 matched on both, per-lane deltas all 0).

Every cleared method is a genuine covered-field recovery: control's
diagnostics on each were `Aggregate→scalar`/`scalar→Aggregate`
conversions or `Unrecoverable` ops on vector-typed operands that the
covered-field typing resolves (`EnemyAimController::IsFinite`,
`GetXPos`, `FromUnitData`, `GetMinMaxX`, `TriggerShoot`,
`EncodeMovement`, `ScreenSizeUtils::GetResolutionUnityToNativeRatio`,
the `ChestRewardManager` pair, `SegInt`/`OnSeg`, `CacheCastleBounds`
×2, `ProcessFragment`, `CheckAndAutoClaimPendingReward`,
`WheelUpgradeAvailable`, `EnforceCategoryDiversity`,
`CleanCastleTopSweepMovement::Init`, `AddPartAtIndex`,
`<ToggleLogType>b__0` — an enum-slot recovery). No previously
diagnosed method moved to clean through the partial-materialization
path — the `default`+partial-store toggle form is gone.

Regressions (57 game-owned, all exposure of defects control hid):

- **52 conversion notes** on previously-clean methods —
  `Single→Vector3` ×24, `Single→Vector2` ×12, `Single→Color` ×4,
  `Single→Vector4` ×1, `Vector2/Vector3→Single` ×4, `Object→Single`
  combinations ×6, `ObscuredFloat↔ObscuredInt` ×1
  (`HumanLikeBotController::UpdateWinIndex`). These are the
  `Color color = default; color.r = 1f` fabrications the control
  emitted silently: the aggregate's uncovered lanes were never
  materialized by the binary (the `FMOV`/`FCSEL` lane-materialization
  gap, `lane:decode`), so the operand keeps its conversion note.
  Includes the coordinator-named `AddProjectileToPortal` and
  `<PlayAutomatedAiming>d__9::MoveNext`: on `development` both emit
  the silently-wrong `Vector2 v = default; v.x = x` form, so their
  honest note is the required outcome of the materialization rule.
- **3 covered-span notes** — `AttributionAdsDebugScreen::CreateWidgets`,
  `AmplitudeProvider::GetDebugInfo`, `ConditionParser::ReadValue`:
  same wrong-width emission family as round 0, still diagnosed.
- **1 unmanaged-memory family** — `ProductUI::IsVisible`: `Vector3[]`
  element reads at intra-element offsets (+0x20/0x24/0x38/0x3C) now
  name the unmanaged loads the covered-field split makes explicit
  where control emitted a silent whole-element copy.
- **1** `CastleMaker::WhereCanUpgrade` (`Single→Vector3`) — same
  partial-materialization family; stays `ilverify-valid`.

Milestone scope (the four castle-building types + nested,
`CastleClashers.Game` — 280 methods):

- methods with diagnostics: **52 → 52**; newly clean:
  `CastleBuildingController::AddPartAtIndex`; newly dirty (1):
  `CastleMaker::WhereCanUpgrade` (`Single→Vector3`, partial
  materialization — exposure).
- `CastleMaker::SpawnShields`: `Enumerator→scalar`-family conversions
  **24 → 16**; total diagnostics 314 → 314.
- `CastleMaker::SpawnShieldsFromPlacements`: `Enumerator→scalar`-family
  **8 → 1**.
- `CastleMaker::MarkCastleShieldPositionsInUpgradeData`: 3 → 0;
  `CastleMaker::Build`: 2 → 2.

`CastleClashers.Game` (`diag_families --assemblies`): methods with
diagnostics **2029 → 2055** (+26 — the honest notes above, including
the 57-method regressed set's CastleClashers.Game share).

## Tests

`Cpp2IL.Core.Tests/Regression/AggregateLaneReadTests.cs`:

- `ScalarReadOfAggregateLocalNamesCoveredField` — `Move Single dest,
  Outer src` emits `ldflda src.inner` + `ldfld x` (**fails on control**:
  the operand keeps the aggregate type).
- `LaneViewReadAtOffsetNamesCoveredField` — `Move V0.S1 dest, Outer src`
  emits `ldflda src.inner` + `ldfld y`, typing the read at byte offset 4
  by the field at offset 4 (**fails on control**).
- `ScalarStoreIntoAggregateNamesCoveredField` — `Move Outer dst, Single
  src` emits `stfld inner.x` (**fails on control**).
- `UnspellableCoveredFieldKeepsDiagnostic` — private members keep the
  operand's diagnostic and emit no synthetic default.
- `ThreeLaneAggregateStoreStaysWholeStructStore` — an `x`/`y`/`z`
  lane-store run into an aggregate collapses back to one whole-struct
  store through `InlinedMemberRecovery` (**fails on `f0baeda0`**: the
  leaf projection won over composite packing).
- `PartiallyMaterializedAggregateKeepsConversionDiagnostic` — a
  `Color` local whose only materialized bytes come from a 4-byte
  literal store keeps the conversion diagnostic (**fails on
  `f0baeda0`**: emitted `default`+partial stores cleanly).
- `LocalLifetimeSplitTests.ScalarCopyIntoAggregateLocalKeepsDiagnostic`
  — the same materialization rule on the lifetime-split path.

Guard tests kept passing: `PackedRegisterFieldTests.
FieldReadOnRestampedPrimitiveSlotStaysDiagnosed` (a Subtract-defined
local's register guess is unsettled — the read stays whole) and
`SpanDataPointerRecoveryTests.ZeroSpanStoreWithoutArrayProvenanceKeepsDiagnostic`
(an unproven-width source keeps the whole-span store diagnosed).
