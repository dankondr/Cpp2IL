# 319 — memory-store windows follow control flow

Cluster: `lane:memory` — stores the game's code actually makes must survive to
emission. Four confirmed shapes dropped values or turned into unmanaged-memory
notes, and all share one root cause: effective positions computed from the
linear instruction list instead of control flow.

## The shapes

1. **Frame-temp stores whose address is passed on** (`MainIngamePanel::UpdateRounds`,
   `*::SetTimeText`, `HumanLikeCastleBuilder.<DistributeUpgrades>b__21_0/1`).
   A hoisted `mov ptr, &slot` at a block that ends with the pointer live and no
   slot definition: the store sat in a dominated successor — a conditional-select
   diamond joining between the hoist and the store. The take bound the stale
   pre-store version, so the real store died unread in dead-code elimination.

2. **x8 struct returns copied with q registers** (`QuestController::CreateInstance`,
   `MaxMediationAdapter::On*FailedToDisplay`). Each arm of a branch calls a
   >16-byte-struct-returning method through the hidden sret pointer into the same
   stack cell, then LDP/STP-copies the result on. The hidden-return rewrite window
   was a flat index range: the first arm's copies sat below the next arm's call in
   list order, so one call claimed reads belonging to another — or claimed none —
   and the shared destination local ended up undefined on some paths.

3. **Pre-indexed stores into get-only instance auto-properties in `.ctor`**
   (`DiagnosticEntry`, `ChestOpenResult`, `MatchResultPayload`). A bump chain on a
   scratch copy — `add x19, x20, #0x20` / `mov x19, x19` / `sub x19, x19, #0x10` —
   where the alias folded only one `Add`/`Subtract` level deep: copies and second
   bumps stayed aliases of an unowned register, so the store resolved to unmanaged
   memory.

4. **Struct-part copies (`LayerMask` pairs)** — cleared by the same two window
   fixes: the copies and selects over `m_Mask` halves only bound once the
   address-take and hidden-return windows followed dominance.

## The rules

- `SsaForm.SinkHoistedAddressTakes`: when a block ends with a take's pointer live
  and no same-block slot def, and every read of the pointer sits in one dominated
  successor, sink the take to just before that first dominated read. The address
  it publishes is path-invariant; the new position binds the version the
  dereference actually sees.
- `LocalVariables.ResolveHiddenReturnBuffers` / `SharpenHiddenReturnBuffers`: the
  window for result resolution and operand rewriting is the flat list range
  extended by every block the call's block dominates, minus reads a rival call
  on the same cell reaches last — a rival shadows a read when its block
  dominates the read's (or it precedes the read inside the read's block) and it
  does not precede this call. Inside one block the ordering is the instruction
  order.
- `MetadataResolver.AddressAlias`: an alias chains through `Move` copies and
  composes nested `Add`/`Subtract` displacements; a local with no defining
  instruction (a parameter, a live-in) is its own root.

## The tests

- `MemoryStoreWindowTests.AddressTakeSinksIntoDominatedReadBlock` — a hoisted take
  with its only read in a dominated successor lands there; the store binds.
- `MemoryStoreWindowTests.HiddenReturnCopiesBindTheirOwnArm` — two arms sharing a
  buffer cell each keep their own result: `callN.Destination` is the arm's local
  and the buffer copy reads it, not the other arm's.
- `AddressAliasRecoveryTests.AddressAliasThroughCopyAndSecondBump` — the copy +
  second-bump chain on an undefined (parameter) root folds to the field.

Each fails on `development` at the merge base and passes on this branch.
