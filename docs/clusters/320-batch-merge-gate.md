# 320 — combined gate of the nine-PR batch (bd1dddc5 → b8d7536c)

Cluster: measurement, ROADMAP direction C, level L3.
Catalog: none. Oracle baseline `tools/forward-model/reports/corpus-6b992535/roundtrip.json`.

## What was measured

`tools/codeverify/gate.py` comparing the CLI at `bd1dddc5` (control, the
merge of #223) against the CLI at `b8d7536c` (the merge of #226, the batch
tip), on the r241 evidence, with the forward-model corpus oracle. The batch
is nine merges landed after #223: #228 `dc5e658d`, #229 `a06dff85`,
#225 `7f75e4bb`, #231 `7d6d674f`, #230 `935fab3c`, #232 `1a791e80`,
#233 `252baea5`, #227 `ba15aae6`, #226 `b8d7536c`.

`development` did not compile from `935fab3c` to `252baea5` (CS0136, a
duplicate `addressedParameter` added by both #230 and #231; the #227 merge
resolved it). All bisect sweeps at those commits used the merge's shipped
resolution — the guarded `ldarga` plus a `ldloca` fallback — so every
midpoint measure reflects what the combination would have emitted.

## Result

`## Verdict` is **FAIL: 1 ILVerify valid->invalid**. Headline numbers:
cleared 230, regressed 90 of game-owned methods; ILVerify transitions
invalid→valid 2, valid→invalid 1, valid→None 1; silent scanner 0 new hits,
1 branch-only exposed hit in a method that was already diagnosed in
control; corpus 353/623 → 359/623 (+6, zero match→mismatch).

Every regressed item is attributed below. One real defect is routed to the
owning lane; everything else is exposure with the mechanism named.

## Attribution

### #227 `ba15aae6` (callconv/byref-struct-args) — real defect, routed

Nine methods regressed with `No legal conversion from E& operand to T
slot; substituting a synthetic default value.` The call in control passed
`ldarg A1` — the AAPCS64 caller-owned copy of a wide by-value composite —
and the batch now spells the argument `&stack_-NN` of the callee's frame
copy. The frame model fragments a wide struct copy into per-word cells and
types the head cell by its first field (`Int32` for `ExplosionRecord`,
`Boolean` for `GrantResult`, `String` for `MatchSetupInfo`, `LogType` for
`LogMessage`, `AnalyticsGdprConsent` for `AnalyticsProviderInfo`), so
`&cell` emits `E&`, `ByReferenceArgumentRecovery.Referent` cannot spell a
`T` referent, and emission substitutes `initobj T` — the caller's value is
dropped and the callee sees a zeroed struct. Some methods additionally
gain dead first-field projections (`ldarga A1; ldfld field0`) on the
source param. Bisect-proven: absent at `252baea5`, present at `ba15aae6`;
a debug-instrumented `ba15aae6` sweep printed the operand shapes
(`AddressOf{LocalVariable{Type:E} stack_-NN}` with untyped sibling cells
inside the T span).

- `CleanProjectile::RecordExplosionForPvp(CastleClashers.PvP.ExplosionRecord)`
- `CastleClashers.PvP.PvpMatchBootstrap::HandleMatchSetup(CastleClashers.PvP.MatchSetupInfo)`
- `CastleClashers.Rewards.RewardGrantService::Publish(CastleClashers.Rewards.GrantResult)`
- `Voodoo.Sauce.Internal.Analytics.AdjustWrapper::Initialize(System.String, System.Boolean, Voodoo.Sauce.Internal.Analytics.AnalyticsProviderInfo)`
- `Voodoo.Sauce.Debugger.IssuesCounter::LogsTrackerOnIssueMessageReceived(Voodoo.Sauce.Debugger.LogMessage)`
- `Voodoo.Sauce.Debugger.LogConsoleDebugScreen::LogsTrackerOnIssueMessageReceived(Voodoo.Sauce.Debugger.LogMessage)`
- `Voodoo.Sauce.Debugger.LogConsoleDebugScreen::OnMessageListClicked(Voodoo.Sauce.Debugger.LogMessage)`
- `Voodoo.Sauce.Debugger.LogConsoleDebugScreen::ShowLogMessagePopup(Voodoo.Sauce.Debugger.LogMessage)`
- `Voodoo.Sauce.Internal.DebugScreen.DebugIssueNumberBadge::LogsTrackerOnIssueMessageReceived(Voodoo.Sauce.Debugger.LogMessage)`

**Routing:** the fix belongs to the operand-typing layer (lane
`types-ssa`, owned by castle-recovery#272), not to a consumer-side patch.
`Referent`/`TypeFrameSlot` can only respell what the frame model names —
retyping the head cell to `T` without merging the sibling cells would emit
`ldloc` of a local whose other words live under different names (wrong
value, worse than the diagnostic). What the lane must change: when a wide
by-value composite argument's frame copy is provably filled whole (memcpy
or per-cell moves of the param's bytes), the copy's cells must carry the
copy's type — merge or alias the span cells under one `T`-typed slot — so
`&copy` spells `ldloc T` (or `ldobj T` at the fill's source address).

### #230 `935fab3c` (honest-merges-2) — exposure, 69 methods

All 69 carry only `Undefined local <v> @ <reg> (<T>) on some path: a read
is reached by no store on one path from the method entry.` — the new
definite-assignment pass in `IlGenerator`. Sampled IL diffs
(`CastleMaker::MirrorFoundationPositions`, `CastleMaker::
GetAverageUpgradeLevel`, `InfiniteScrollRect::GetVisibleIndexRange`,
`PaperPlaneTools.RateBoxPrefabScript::Start`, `MenuDailyWinRewardsView::
SetData`, `ForgePanel::Build`, `LoginStreakController::
HandleNextRewardDay`, `MenuArenaProgressTracker::{LayoutProgressPoints,
LayoutProgressPointsWithLayoutElement}`) show the branch body identical
to control with an appended `ldstr <note>; call NoteDecompilerIssue;
ldnull; throw` tail: control silently emitted a read of a local no store
could reach (the game can't hit that path either, or control would have
thrown a NullReference at runtime); the branch names the dead read
honestly. Exposure, not a defect — no silent wrong recovery introduced.

Methods (69): the family list is reproduced in the gate report comment on
castle-recovery#10; every `Undefined local … on some path` line in the
regressed set belongs here. Notable members: `BattleController::
CreateRuleset`, `UnitDestructionTestingGroundsHarness::
FindCastleManagerWithMaker`, `CastleMaker::MirrorFoundationPositions`,
`CastleMaker::GetAverageUpgradeLevel`, `CastleClashers.Rewards.
ChestRoller::AllocatePieces`, `ChestController::AllocatePieces`, coroutine
`MoveNext` bodies, and `Triangulator::.ctor`.

### #232 `1a791e80` (cctor-static-autoprop) — exposure, 12 methods

All 12 carry only `Store through unmanaged memory form [<v> @ <reg>] could
not be emitted; the value was dropped.` — the `IlGenerator` narrowing that
only emits `stloc` for `MemoryOperand{Base: local}` stores when the local
is an integral/non-float value type. In control those stores emitted
`stloc V` where `V` is the *base* local — i.e. control overwrote the
pointer variable itself and silently dropped the write to the pointee; the
branch pops the value and notes it. Sampled diffs
(`MatchResultPayload::.ctor` `[v27 @ X20_v2]`, `ChestOpenResult::.ctor`
`[v55 @ X19_v2]`, `BotTurnContext::.ctor` `[v30 @ X0_v3]`/`[v32 @
X21_v2]`, `TutorialOverrideResult::.ctor`, `PanelController::
SyncFindingMatchPanelAbVariant`, `WeeklyLeaderboardPanel+
<MovePlayerShowcaseTo>d__25::MoveNext`) are all `stloc V` → `pop; note`.
Exposure — the control hid a silent wrong value.

Methods (12): `BotTurnContext::.ctor`, `MatchResultPayload::.ctor`,
`ChestOpenResult::.ctor`, `RotatingLocalizedNotificationSelection::.ctor`,
`LogMessage::.ctor`, `DiagnosticEntry::.ctor`, `PanelController::
SyncFindingMatchPanelAbVariant`, `TournamentController::
InitFromFeatureInstances`, `AdnAdsSignalsCollector::UpdateLoadRequestInfo`,
and the coroutine `MoveNext` bodies `UIShineFlashController+FlashRoutine`,
`UIUpgradeFlash+FlashRoutine`, `WeeklyLeaderboardPanel+
MovePlayerShowcaseTo`.

### #231 `7d6d674f` (285-subclass-fields-after-isinst) — ILVerify valid→invalid, routed

`GooglePlayGames.PlayGamesUserProfile::Equals(System.Object)` is the gate
report's single `valid -> invalid` transition. The batch's type-test
narrowing now recovers the comparer access through the `isinst` check and
emits `callvirt System.Boolean System.OrdinalCaseSensitiveComparer::
Equals(...)`; the declaring type is `internal` in .NET, so the call is a
member the emitted assembly cannot name — ILVerify reports the method
inaccessible. Bisect-proven: control (70 instrs) had no such callvirt;
`7d6d674f` emits it (73 instrs), as do `252baea5` and `ba15aae6`. The
emission path has no visibility fallback for a narrowed receiver whose
declaring type is not public. The operand typing that picks
`OrdinalCaseSensitiveComparer` as the call target's declaring type lives
in `MetadataResolver`/operand typing — lane `types-ssa`, owned by
castle-recovery#272 — so this is routed, not fixed here. What the lane
must change: a narrowed callvirt whose resolved declaring type is not
visible from the caller must downgrade to a callable form (base-declared
method, or the pre-narrowing receiver with a note).

### #232 `1a791e80` — ILVerify valid→None (dead stub removal, not a defect)

`Google.Protobuf.JsonToken::.ctor()` was a synthesized 3-instruction stub
(`ldarg.0; call System.Object::.ctor(); ret`) — a parameterless ctor on a
struct that nothing calls. Bisect-proven: emitted at `7d6d674f` (#231) and
`935fab3c` (#230), gone at `1a791e80` (#232). A sweep of the branch output
finds no `newobj` reference to it anywhere; `initobj` is the verifiable
form for `default(JsonToken)`. Removing a dead unverifiable-shape member
is a behaviour-neutral improvement; the `None` transition is the member
disappearing, not a verification failure.

### silent scanner — 1 exposed hit, no new-class regression

`Voodoo.Sauce.Internal.Analytics.VoodooAnalyticsProvider::
TrackPerformanceMetrics` gains `uninit-read` hits at five sites — but the
method's body grew 76 → 285 instructions with all ~20 control diagnostics
removed, so the hits live in newly recovered code (the scanner's
`exposed` class: the method already carried diagnostics in control).
No silent hit appears in a method that was clean in control: the
silent-wrong-recovery bar is met.

## Improvements measured (batch net-positive)

- `il2cpp-type-test` corpus 5/11 → 7/11, `llvm-struct-abi` 33/73 → 37/73;
  6 new matches, 0 match→mismatch (the win is #231's isinst narrowing and
  #227/#226 packed/callconv work).
- ILVerify invalid→valid ×2: `Google.Protobuf.ParseContext::Initialize`
  and `CastleClashers.Game.PlayerBattleProfileInfoPanel::SetData`.
- `PvpProtocol::EncodeMatchResult` now spells `ldarga; ldfld LocalWon;
  call ForBool`; `GrantResult::ForChest` and `GrantResult+ChestData::
  .ctor` lose the dropped-store/undef-local diagnostics.
- Silent classes `empty-diamond`, `param-without-ldarg`, `no-exit`,
  `list-clear-truncated` all went to zero new hits; `uninit-read` 85→16.

## Castle scope

Scope: `CastleBuildingController`, `TimedCastleBuildingController`,
`CastleMaker`, `EngineersController` and nested types. Status moves
against control:

Regressed (0 → ≥1, both `undef-somepath` exposure from #230 — verified
note-only tails):

- `CastleMaker::MirrorFoundationPositions(List<FoundationData>, int)` — 0→1
- `CastleMaker::GetAverageUpgradeLevel()` — 0→1

Cleared (→ 0):

- `CastleBuildingController::.cctor` — 1→0
- `CastleMaker+<>c::<GenerateFoundationsForBot>b__54_0` — 2→0

Improved (fewer diagnostics): `CastleMaker::SpawnShields` 315→314,
`CastleMaker::SpawnShieldsFromPlacements` 278→276,
`CastleMaker::CheckIfBannerAtThisPosition` 4→2.

More diagnostics but still unfinished (all `undef-somepath`/`store-
unmanaged` exposure, no gate failure): `CastleBuildingController::
LoadFromSave` 1→2, `ShowUpgradeAdditions` 42→43; `CastleMaker::InitRefs`
53→54, `BuildFoundations` 3→4, `MarkCastleShieldPositionsInUpgradeData`
17→18, `CheckIfCanAddAt` 1→3; `EngineersController::GetAvaiableEngineer`
9→10. Net castle-scope diagnostic count ≈ flat (−6 by count, +2 methods
crossing to/from zero).

## The test

This task's deliverable is the measurement itself: `docs/clusters/320-
batch-merge-gate.md` names every regressed item, its causing merge, and
its class (exposure vs routed defect). The gate verdict fails on the one
routed item above; every other regression is exposure with the mechanism
named. Verification commands and outputs are in the PR body and in the
report comment on castle-recovery#10.

## Gaps

- The `T&`-operand defect (#227) and the invisible-callvirt defect (#231)
  are routed to `types-ssa` (#272) — the required change lives in operand
  typing/frame-cell modelling and in the callvirt visibility fallback,
  which this task does not own. Fixes there should re-gate against this
  report's list.
- Bisect checkpoints `935fab3c` and `1a791e80` needed the #227 merge's
  CS0136 resolution to build; measured with that resolution applied (same
  as shipped `ba15aae6`), noted rather than swept around.
