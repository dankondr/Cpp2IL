# 340 — stores through addressed storage and the statics dereference

Cluster: `lane:memory` — the stores the addressed-storage model introduced for
loads (#215) had no store side, and the static form of field-address recovery
(`Add x, [klass + static_fields], off` → `&T.s`) left every `&T.s`-shaped
operand as a raw pointer. Follows #319 (`4b162c47`), which fixed the
control-flow windows; the shapes below are what survived it.

## The shapes

1. **Store through a proven address-of** (`this+off` / `X8+off` drops in
   `CastleMaker::InitRefs`, `CastleMaker::SpawnShields`). #215's
   `ResolveAddressedStorage` bound `[v]` loads to `&t` / `&f` operands, but
   stores through the same locals stayed `Store through unmanaged memory form`
   drops. `StoreThroughAddressed` (in `MetadataResolver`'s load/store pass,
   same schedule as the load side) resolves `[v = &f, +k]` = the field itself,
   the sibling field at `f + k` on the same host, or the frame cell holding
   the byte when `v` is a stack local — including member paths inside
   value-typed cells and cells the compiler spilled without a surviving
   local (materialised as `stack_N` temps). Unproven shapes keep their
   `MemoryOperand` and their diagnostic.

2. **Multi-definition same-address aliases**. A `v = &f` re-taken per
   iterator call is still the same storage; the single-definition chase
   missed it. Every definition of `v` naming the same `AddressOf` target
   folds the group to the shared target before the single-def chase runs.

3. **`[klass + static_fields]` non-call operands**. The classic schedule
   (`PropagateStaticFieldStorage`) types `Move x, [base + B8]` only when
   `base` is `RuntimeClass`-typed — seeded once, before the fixpoint. Bases
   whose class constant was created after seeding (an arm-2
   `Move x, typeof(T)` product, an edge copy, a phi the class type claimed
   before a `RuntimeClass` input propagated) hold the same pointer but can
   never reach the rule — `SetTypeIfUnknown` is monotonic.
   `NormalizeStaticFieldStorage` (`MetadataResolver.ResolveFieldOffsets`)
   stands in a `StaticFieldStorageTypeAnalysisContext` local per owner type
   and folds `[klass + static_fields]` to it when the base provably holds a
   class constant (`ClassConstant`, moved to file scope) and the operand is
   pointer arithmetic (any arm) or the base is provably unseeded
   (`UnseededConstant`: leaf `Move _,Type` on a non-`RuntimeClass` local,
   or a phi already claimed by a non-`RuntimeClass` type). Call operands
   keep the classic `&T.s` emission. `Move x, [klass]` folds to
   `Move x, typeof(T)` — the class object itself — for non-call destinations.

4. **Aggregate element stores split across lanes** (`stp`-lowered 16-byte
   element writes in 2-D grids). Once `[p + 0]` resolved to the whole
   element (`value` naming the element type), `[p + 8] = upper-lane` was a
   second store of bytes the implicit-definition register already put in
   `value` — dropped by `UpperLaneOf`. Multi-definition element addresses
   (`p` from `a + b` on several defs of the same `Add`) fold like (2).

5. **`Move &t` stores unwrap the address-of** (`IlGenerator`'s store
   emission): `Move [p], v` resolved to `Move &f, v` operand-wise needed
   the store arms to see `f`, not `&f`.

## Scope result (castle building, CastleClashers.Game)

`CastleMaker::InitRefs` 53 → 45 diagnostics, `CastleMaker::SpawnShields`
314 → 308, `CastleBuildingController::AddNewUnit` 7 → 6,
`CastleBuildingController+<FullyBuildCastlesIE>d__139::MoveNext` 1 → 0
(cleared — the #236 frame-store exposure). Scope: 53 → 52 of 280 methods
diagnosed; the two named methods stay diagnosed on other families
(`Unmanaged memory load` rows in `InitRefs`; the `Enumerator._list`/`_current`
member stores in `SpawnShields` now resolve to compiler-internal fields and
read as `access: inaccessible member` — the store is understood, the member
is not emittable from the caller's context).

Whole game: 205100 → 204674 diagnostics; 44 methods diagnosed→clean,
0 clean→diagnosed. `memory: unmanaged store dropped` family on
CastleClashers.Game: 326 methods/1952 occurrences → 269/1590.

## The tests

`Cpp2IL.Core.Tests/Regression/ResidualStoreRecoveryTests.cs`:

- `StoreThroughMergedFieldAddressResolves` — `[v + 4] = v` through a
  multi-def `v = &panel.frame.origin` → `origin.y` member store.
- `StoreThroughStaticFieldAddressResolves` — `[p] = v` with
  `p = statics + 0` → `stsfld Holder.count`.
- `ClassPointerDereferencesResolveThroughCopy` — `Add s, [klass + B8], 0`
  folds to the statics stand-in through copy chains; `Move x, [klass + B8]`
  on a `RuntimeClass`-seeded base keeps its MemoryOperand for the classic
  schedule; `Move x, [klass]` → `Move x, typeof(T)`.
- `StaticsLoadThroughClassClaimedPhiResolves` — the unseeded-constant arm:
  `Move x, [phi + B8]` where the phi is claimed by the class type folds to
  the stand-in.
- `AggregateElementStoreSplitAcrossLanes` — the stp-lowered element write
  resolves to `grid[x, y] = value` and drops the upper lane.

Each fails on `development` (the operand stays a `MemoryOperand`, the field
never binds, or the lane store survives) and passes on this branch.
