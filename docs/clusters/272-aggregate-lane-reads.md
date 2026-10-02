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
  narrower sources split the scalar sources.

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

## Numbers (control `0589ade7` vs branch, r241 / Castle Busters 1.11.1)

Milestone scope (`CastleBuildingController`,
`TimedCastleBuildingController`, `CastleMaker`, `EngineersController`
+ nested, `CastleClashers.Game` — 286 methods):

- methods with diagnostics: **67 → 66**; newly clean:
  `CastleMaker::Paint`; newly dirty: **0**
- `CastleMaker::SpawnShields`: diagnostics 439 → 365;
  `Enumerator→scalar`-family conversions **67 → 7** (+17 covered-span
  notes)
- `CastleMaker::SpawnShieldsFromPlacements`: 424 → 374;
  `Enumerator→scalar`-family **47 → 1** (+8 covered-span notes)
- survivors are non-`Move` unproven edges (`Enumerator→ShieldType`,
  `Enumerator→Int32`, `Enumerator→Vector2Int`, `Int32→Enumerator` on
  Convert/field-store/call-arg shapes) — the covered-field rule cannot
  prove them, so they stay diagnosed by design; the `→Vector3`
  direction is fully gone.

`CastleClashers.Game` (`diag_families --assemblies`): methods with
diagnostics **2236 → 2154**; `no legal conversion` 1184 → 1075
methods (5316 → 4388 occurrences); `synthetic default` 467 → 440;
`unrecoverable op` 443 → 414; `zero on phi edge` 90 → 66; `receiver
not recovered` 39 → 75 (async `d__` receivers now typed and named —
see Exposure); `undefined local` 515 → 516.

Assembly-wide (`codeverify`, control vs branch):

- `verified` **31515 → 31859 (+344)**, `compiles_unverified` 21188 →
  21397, `incomplete` 15604 → 15050 (−554), `fails_compile` 226 → 227
  (+1, named), `invalid_il` **388 → 388 — 0 valid→invalid transitions,
  membership identical**; `missing`/`no_body`/`stub` flat.
- cluster nets: `No legal conversion` −4100 occurrences, phi-edge
  zero −836, `Unmanaged memory load` −430, `Operand slot synthetic
  default` −388, `Unrecoverable` Add/Multiply/ShiftRight/comparisons
  −104/−92/−82/−76/−60; covered-span notes +~780 (new family);
  `Receiver instance` +420; `Inaccessible field store` +64;
  `hidden shared-generic` +2; `Undefined local` net −26.

### Regressions (all named, all exposure or reclassification)

- `verified → incomplete` ×6 — `Voodoo.Sauce.Internal.Analytics.
  AmplitudeProvider::GetDebugInfo`, `TinyJson.JSONParser::
  ParseAnonymousValue`, `EventRuleset.ConditionParser::ReadValue`,
  `AttributionAdsDebugScreen::CreateWidgets`, `Nakama.TinyJson.
  JsonParser::ParseAnonymousValue`, `MoreMountains.Tools.
  MMPersistent::GetCurrentComponents`. The covered-span note and the
  `Undefined local` note now name copies whose own width is narrower
  than the source's declared type (1-byte of `Int32`, 4-byte of
  `Double`/`Int64`, 8-byte `LDP` half of a 16-byte `ComponentData`)
  where control emitted a compilable whole-value conversion the move
  cannot satisfy — previously-silent wrong-width emission, now
  diagnosed.
- `compiles_unverified → incomplete` ×1 —
  `Google.Protobuf.Collections.ProtobufEqualityComparers+
  BitwiseSingleEqualityComparerImpl::GetHashCode(System.Single)`: a
  4-byte move of an 8-byte `Double` — same honest covered-span note.
- `incomplete → fails_compile` ×1 —
  `CW.Common.CwFollow::UpdatePosition`: the `Unrecoverable operation:
  Multiply` vector diagnostics cleared (the method now emits code);
  the remaining `CS0117 'Math' does not contain 'E'/'PI'` is a
  preexisting regenerated-mscorlib member gap present identically in
  control — lateral reclassification, not new breakage.
- `fails_compile` +1 total; compile-error deltas `Voodoo.Nakama` +2,
  `VoodooTuneSDK` +1 — all `CS0246 <>c__DisplayClassNN_0` missing
  generated-closure types (the tree does not emit them), on
  already-failing assemblies; `RootMotion` −2, `DOTweenModules` −1.
- Cluster growth on already-`incomplete` methods: `Receiver instance`
  +420 (`d__` async state-machine locals now settle their real struct
  type, so receiver-recovery failure names it, replacing
  `Int32→slot` conversion notes), `Inaccessible field store` +64
  (aggregate types settling on locals resolve stores to unwritable
  fields), `hidden shared-generic` +2, `DebugException` backing +1 —
  same mechanism, diagnosed either way.
- 1 new `ilverify:StackUnexpected` finding on
  `NakamaServer+<Authenticate>d__62::MoveNext` — on an already-
  `incomplete` method; `invalid_il` membership unchanged.

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

Guard tests kept passing: `PackedRegisterFieldTests.
FieldReadOnRestampedPrimitiveSlotStaysDiagnosed` (a Subtract-defined
local's register guess is unsettled — the read stays whole) and
`SpanDataPointerRecoveryTests.ZeroSpanStoreWithoutArrayProvenanceKeepsDiagnostic`
(an unproven-width source keeps the whole-span store diagnosed).
