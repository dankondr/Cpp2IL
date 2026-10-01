# EH region recovery (206, slice 2)

## Round 7: development receiver fixes and barrier-only frame facts (2026-10-01)

**Draft: 8,996 owned pad warnings remain; target ≤7,768.** Development removes
461 pads, and the EH increment removes another eight. Total reduction from
15,537 is 6,541 (42.1%); another 1,228 are required. This round stops at the
remaining proof/dataflow boundaries described below. The target is not achieved.

### Change and controls

Merged development `f71e694ab2219acb68bfd555dd79f4f44cc33c9f` into the existing
branch, producing `b54a4dc7b0db68cf42910549038db5676099f1ac`.
This includes #185, #191, #193, #194, #195 and #196. #181 remains open.
EH commit: `55cad8e6`.

The EH frame tracker now uses the existing structurally proven
`WriteBarrierAliases` set and the existing barrier-only helper contract.
The core and its pure B veneers perform GC bookkeeping after a separate store;
they do not write the addressed frame slot. Heap facts are still invalidated.
Unknown calls, hidden result stores and the exported setter retain their previous
invalidation. Normal helper recognition, calling conventions and normal-dataflow passes
are unchanged.

A saved cleanup receiver after an earlier addressed barrier call was previously
lost. The existing width fixture now tests the named core, a proven alias, and
the exported setter. On unchanged EH code, the two positive barrier cases fail
and the other five cases pass. With the fix, all seven pass; the setter still
refuses the stale receiver. The full EH suite passes 66/66.

| Stage | Owned pads | Newly clean owned methods | Clean regressions owned |
|---|---:|---:|---:|
| Prior draft `d1317ee5` | 9,465 | — | — |
| Merge development | 9,004 | 82 | 3 inherited from development |
| Barrier-only EH increment | 8,996 | 0 | 0 |
| Auxiliary seed investigation | 8,996 | 0 | 0 |
| Protected-range investigation | 8,996 | 0 | 0 |

Full control: `astra206-r13-control`, frozen binary `astra206-r13-control-bin`,
built from **exactly** development `f71e694a` without this draft's EH changes.
Full branch: `astra206-r13-final`, frozen binary `astra206-r13-final-bin`.
Both completed **69,982/69,982** native methods and output 183 assemblies with
178,273 reported methods. The intermediate merge sweep is `astra206-r13-merged`.
The barrier experiment (`astra206-r13-barrier`) has the same diagnostic/pad
results as the final uninstrumented production sweep.

### Fresh paired measurements

| Scope | Diagnosed control → branch | Newly clean | Clean regressions | Pads control → branch |
|---|---:|---:|---:|---:|
| All | 15,642 → 15,642 | 0 | 0 | 46,642 → 40,856 |
| Game-owned | 3,739 → 3,739 | 0 | 0 | 10,319 → 8,996 |
| CastleClashers.Game | 2,266 → 2,266 | 0 | 0 | 6,290 → 5,831 |
| Castle-building owners + nested types | 72 → 72 | 0 | 0 | 684 → 684 |

No added diagnostics in the paired comparison. Both required `diag_families.py`
scopes were run with `--count 'Exception landing pad at'` (including
`--assemblies CastleClashers.Game`). Both ILVerify scans have **170,143 valid,
416 invalid, 7,714 partial**, identical method identities, **0 status transitions,
0 valid→invalid**. Bootstrap reachability remains blocked at 29/29.

The prior round reported one more method: the clean Google.Play.Games
`AndroidNearbyConnectionClient.OnGameThreadDiscoveryListener.<>c__DisplayClass3_0.<OnEndpointLost>b__0`
(token `0600033e`, native `66B131C`) is absent from both fresh recovery manifests.
This is a development output change, excluded explicitly from the prior-head
identity comparison; it is not counted as a newly clean method or a regression.

### Native and IL review

The owned EH improvement is `CrashReportManager.SelectCrashReporter`
(native `3AEB370`), **17 → 9 pads**. Native finally coverage grows **40 → 48**.
Its emitted IL has two finally clauses with the actual enumerator receivers:
`Enumerator<System.Type>.Dispose` at IL `03EB` and
`Enumerator<ICrashlyticsProvider>.Dispose` at IL `06D0`, each followed by
`endfinally`; normal exits use `leave`. The normal bucket enumerator Dispose
copies remain where their region shape is still refused. No warning was hidden.

Ten methods newly clean after development were read against native instructions:

| Method | Native anchor | Checked IL behavior |
|---|---|---|
| CastleBuildElements.GetSpriteElement | `3C889AC`; get_Item `3C88A8C` | Array lengths, element selection, WallType and AttachDirection comparisons, index/null throws |
| CastleDamageTracker.OnTurnStart | `3D5F524`; round conversion `3D5F5D0` | FlushDamage, health scaling, Truncate/Ceiling/Floor and numeric conversions |
| CastleDamageTracker.FlushDamage | `3D5F664`; TrackCastleDamage `3D5F850` | Original ID and damage value reach MVPTracker; rounding inputs retain their scalar types |
| CastleMaker.CheckIfBelongsToAnyFoundation | `3E601BC`; grid conversion `3E60284` | Two-dimensional grid reads, ObscuredInt conversion, FoundationData lookup |
| CastleMaker.CheckIfHasFoundationAbove | `3E64E68`; get_Item `3E64F18` | Foundation loop, numeric comparisons and original count/index checks |
| CastleMaker.WhereCanUpgrade | `3E69350`; grid reads `3E69474`, `3E694B4`, `3E69514` | Array.GetLength, grid Get, ObscuredInt conversions and Vector3 list addition |
| CastleMaker.GetBottomPartAverageUpgradeLevel | `3E6B2F8`; grid reads `3E6B3A0`, `3E6B3DC` | Grid reads and average/rounding retain their inputs |
| CastleMaker.GetImpactedObjects | `3E6B4F4`; get_Item `3E6B62C` | Foundation lookup, child/localPosition calls, list population and rounding |
| CastleMaker.AddFoundation | `3E6C428`; get_Item `3E6C4FC` | Foundation creation/list Add and SaveFoundation after the original searches |
| CastleMaker.RemoveFoundation | `3E6C7C0`; get_Item `3E6C880` | Original searches, RemoveAt and SaveFoundation |

These are development improvements, reproduced in the fresh control. Logs:
`astra206-r13-reviewed-native.log`, `astra206-r13-reviewed-il.log`,
`astra206-r13-crash-native.log`, `astra206-r13-crash-il.log`.

### State machines: native shapes before method counts

The same 133-method cohort still has **3,162 remaining pads**. Before this EH
increment, the 972 directly observed post-type scaffolding failures split into
612 indexed exception stores (30 methods), 344 zero stores through an unknown
address (22 methods), and 16 exception stores through an unknown address
(two methods). Shapes overlap methods.

After the barrier fix, this first-failure step is **697 pads / 37 methods**:

| Native shape | Pads | Methods |
|---|---:|---:|
| `Move [base], 0` through an unknown loaded pointer | 430 | 22 |
| `Move [frameBase + index * 8], exception` | 251 | 16 |
| `Move [base], exception` through an unknown loaded pointer | 16 | 2 |

The recovered index permits further analysis; most affected pads then hit an
argument or callee gate, so it does not make these state machines clean.

`Bootstrap.<StartNakamaLoginFlow>.MoveNext` (`3C7F984`): index initialization
is at `3C7FAC8` (`stack[28] = 0`), load at `3C8053C`, exception-store base at
`3C80544` (`&stack[18]`), store at **`3C80548`**, increment/store at `3C80550`.
The same outer-handler shape occurs at `3C80648`–`3C8065C`, with indexed store
**`3C80654`**. The traced loss was at **`3C80040`**, which receives `&stack[0]`;
its target `37C2A24` is a pure B veneer of the already recognized GC barrier
`37C3F8C`. That barrier does not write the index. This was an EH invalidation
error, not evidence that the index cell itself was written through an escaped
address. Unknown addressed writers continue to invalidate their full unknown
extent; frame value/type information still needs the owner when those block a
proof. Reference-pointer zero stores are real effects and are not discarded as
scaffolding.

A temporary experiment bound actual normal SSA reference-field reads to their
native reaching values, combined with the barrier fix. It produced **zero new
state-machine proofs** and was discarded. No fresh heap reload or inferred
capture is shipped.

### Auxiliary handlers and the shared builder hypothesis

The old 680-pad description mixed auxiliary/unsupported catch paths. Direct
instrumentation now records **550 pads in 56 methods** with no normal-path
seed; another **603 pads across all 133 methods** remain in auxiliary,
selector or epilogue shapes not assigned a more precise first-failure category.
These counts are not claims of new proof coverage.

The no-seed protected ranges lie in catch/cleanup code reached by exceptional
edges, which NormalStates intentionally does not traverse. Common native
site shapes include the null-reference throw helper (`37C2D20`),
`__cxa_end_catch` (`7CD5490`), unwind/rethrow machinery (`7CD54B0`), type tests,
metadata initialization and method-specific managed calls. They do not reduce
to one directly identified SetException site. A normal state cannot be copied
onto these exceptional edges without proving the enclosing handler's effects
and frame state.

The builder target at **`398913C`** is still missing from the managed address
map; the handler passes the builder field, exception, and **null MethodInfo**.
In the login method the call is at **`3C80678`**; in InitializeVoodooLive it is
at **`3C7F824`**. The metadata-backed SetException at `6F03E38` is not an exact
body/forwarding match. No managed signature is assigned by behavioral similarity.
A shared builder seed therefore has no sound prerequisite proof yet.

Remaining first-failure categories (disjoint by pad):

| Gate | Pads | Methods |
|---|---:|---:|
| Unknown frame/scaffolding store after the type test | 697 | 37 |
| Other auxiliary/selector/epilogue shape | 603 | 133 |
| No normal seed (directly observed) | 550 | 56 |
| Unproven managed call argument | 491 | 27 |
| Unresolved managed callee | 380 | 43 |
| Call before catch type proof | 199 | 13 |
| Type mismatch does not prove unwind | 92 | 3 |
| Normal merge is not a proven void epilogue | 71 | 6 |
| Branch in managed handler | 38 | 4 |
| Branch before type proof | 37 | 1 |
| Native proof; IL refused | 4 | 2 |

### Proven ranges with no reachable emitted protected instruction

Of the **original 812 pads / 62 methods**, 32 pads are now removed. Of the
780 remaining pads, **773 still have the no-reachable-seed refusal** and seven
in SelectCrashReporter now fail another region gate. Every current no-seed
candidate has normal code **both lifted and emitted**. There are **zero methods
with the whole candidate protected range absent from normal ISIL**, and **zero
with the whole range lifted but absent from the IL instruction map**. The missing
piece is emitted reachability, not a missing protected call. Individual setup
instructions can still be folded normally.

The fresh disjoint materialization classification contains **1,145 no-seed pads
in 61 methods**, because receiver/local fixes let more previously unusable
candidates reach this later gate. All their mapped emitted units are unreachable
from IL entry. A full method/range table is below for the normal-dataflow owner.

Examples of the earlier barriers:

- `CastleMaker.Build` (`3E597DC`): protected decoration range begins
  `3E5C028`–`3E5C030`, with calls through `3E5C2D8`–`3E5C2E0`;
  the interior map range is `3E5E5D0`–`3E5E5D8` / `3E5E5F8`–`3E5E5FC`.
  These calls are present in IL. Earlier normal emission terminates on an
  unresolved array load at **`3E59FF0`**, grid Add at **`3E5A2C8`**, and other
  unresolved memory/arithmetic shapes. It is not sound to mark these units
  reachable in EH.
- `SDFSpriteGenerator_SR.RefreshPointsFromChildren` (`3B8CFC0`): native
  ranges include `3B8D670`–`3B8D678` and `3B8D7B0`–`3B8D7B8`.
  Emitted execution stops earlier at **`3B8D350`**, where a scalar comparison
  was typed as a Vector3 comparison and emitted as an unrecoverable-operation
  throw.
- `CastleShieldsView.PopulateShields` (`3ED6384`): later enumeration ranges
  include `3ED6678`–`3ED6680`; the reachable emitted paths terminate in earlier
  cast/null/allocation guards. The lifted loop is still present. This needs
  normal type/control-flow evidence, not a guessed EH reachability edge.

Logs: `astra206-r13-material-run.log`, `astra206-r13-blocker-il.log`,
`astra206-r13-no-seed-ranges.json`, `astra206-r13-final-material-run.log`.

### Gaps

Fresh native proof coverage is **7,092 finally + 1,306 catch = 8,398 pads**.
No previous native proof disappears; the eight additional pads materialize.
**1,857 proven pads in 103 methods remain unmaterialized**:

| First materialization refusal | Pads | Methods |
|---|---:|---:|
| No reachable emitted protected unit | 1145 | 61 |
| Return/live entry/uncovered call crossing | 455 | 22 |
| Cleanup local not assigned at try entry (owner lane) | 128 | 13 |
| Unusable/different cleanup IL (owner lane) | 117 | 4 |
| Shared coverage or global region gate | 8 | 5 |
| Catch merge/seed/handler unavailable | 4 | 2 |

The 455 crossing pads are not safely handled by wrapping each call in its own
finally: that would execute cleanup earlier and potentially more than once.
The full native cleanup extent and all normal exits must agree first.
Reserved receiver/slot/type passes remain untouched. `SpawnShieldsFromPlacements`
is still among the four methods with unusable/different cleanup IL; the owner
can inspect its normal copies after #195. The current 128 unassigned-local pads
are still the owner's bucket. No EH workaround for either bucket is shipped.

### Castle-building scope

| Method | Pads fresh control → branch |
|---|---:|
| ``System.Void CastleBuildingController::ShowUpgradeAdditions()`` | 35 → 35 |
| ``System.Void CastleBuildingController::TriggerInterior()`` | 35 → 35 |
| ``System.Void CastleBuildingController::RelocateUnitsToValidPositions()`` | 41 → 41 |
| ``System.Nullable`1<UnityEngine.Vector2Int> CastleMaker::PickBestAvailablePosition(System.Collections.Generic.List`1<UnityEngine.Vector2Int>, System.Collections.Generic.HashSet`1<UnityEngine.Vector2Int>, CastleClashers.HumanLikeBots.BotTier, System.Boolean)`` | 12 → 12 |
| ``System.Void CastleMaker::Build(System.Boolean, System.Boolean, System.Boolean)`` | 43 → 43 |
| ``System.Void CastleMaker::SpawnShields(System.Boolean)`` | 224 → 224 |
| ``System.Void CastleMaker::SpawnShieldsFromPlacements(System.Collections.Generic.List`1<EnemyShieldPlacement>)`` | 217 → 217 |
| ``System.Void CastleMaker::SaveShieldsData()`` | 47 → 47 |
| ``System.Void CastleMaker::SetShieldTypeForGridPos(UnityEngine.Vector2Int, System.Int32)`` | 14 → 14 |
| ``System.Void CastleMaker::MarkCastleShieldPositionsInUpgradeData()`` | 7 → 7 |
| ``UnityEngine.GameObject[0..., 0...] CastleMaker::BuildGridAuto(System.Collections.Generic.List`1<UnityEngine.Transform>, System.Boolean, System.Single)`` | 9 → 9 |

### Development regressions and clean methods

Compared with the prior draft, development makes 356 methods clean, including
82 owned and eight castle-building methods. It introduces 40 clean-to-diagnosed
transitions, including three owned; all reproduce with their exact diagnostics
in the fresh development control. None is caused by this EH increment.
The merge also adds diagnostics to 1,274 already/now diagnosed method records
(342 owned); those lists are preserved in `astra206-r13-merge-metrics.json`.
No ILVerify status changes accompany them.

Owned regressions:

- `HelperItemSO.GetPricesForLevel` (`3D63244`) and
  `WheelData.GetPricesForLevel` (`3DBB8E4`): V9/V11/V10 Single locals are used
  after the numeric conversion changes but have no remaining definitions.
  These are normal scalar-conversion/dataflow failures; pads are unchanged.
- `FindingMatchPanel.<FadeInImages>.MoveNext` (`3CAC5DC`): a Single operand
  reaches a Vector2 slot, requiring a diagnosed default. This is a normal
  packed-value/type failure; pads are unchanged.

The complete clean-regression list below identifies each emitted failure family.
They are inherited from the merged development range; this report does not claim
an isolated causal commit for every external method. Preserving the warnings is
part of the result.

<details>
<summary>All 40 clean regressions after development</summary>

| Assembly / method | Current diagnostic families |
|---|---|
| CastleClashers.Game: ``HelperItemSO::GetPricesForLevel`` | Undefined scalar local |
| CastleClashers.Game: ``WheelData::GetPricesForLevel`` | Undefined scalar local |
| CastleClashers.Game: ``FindingMatchPanel+<FadeInImages>d__41::MoveNext`` | Unavailable/illegal operand conversion |
| Mono.Security: ``Mono.Security.X509.X509Certificate::get_RSA`` | Unavailable/illegal operand conversion |
| Voodoo.Nakama: ``Nakama.Protobuf.Battle+BattleClient::BattleSendResult`` | Unavailable/illegal operand conversion |
| Voodoo.Nakama: ``Nakama.Protobuf.Battle+BattleClient::BattleSendResultAsync`` | Unavailable/illegal operand conversion |
| Voodoo.Nakama: ``Nakama.Protobuf.CastleClashersInventory+CastleClashersInventoryClient::Snapshot`` | Unavailable/illegal operand conversion |
| Voodoo.Nakama: ``Nakama.Protobuf.CastleClashersInventory+CastleClashersInventoryClient::SnapshotAsync`` | Unavailable/illegal operand conversion |
| Voodoo.Nakama: ``Nakama.Protobuf.CastleClashersInventory+CastleClashersInventoryClient::SubmitEvents`` | Unavailable/illegal operand conversion |
| Voodoo.Nakama: ``Nakama.Protobuf.CastleClashersInventory+CastleClashersInventoryClient::SubmitEventsAsync`` | Unavailable/illegal operand conversion |
| Voodoo.Nakama: ``Nakama.Protobuf.CastleClashersRelay+CastleClashersRelayClient::CastleClashersRelayInit`` | Unavailable/illegal operand conversion |
| Voodoo.Nakama: ``Nakama.Protobuf.CastleClashersRelay+CastleClashersRelayClient::CastleClashersRelayInitAsync`` | Unavailable/illegal operand conversion |
| Voodoo.Nakama: ``Nakama.Protobuf.CastleClashersRelay+CastleClashersRelayClient::CastleClashersRelayStream`` | Unavailable/illegal operand conversion |
| Voodoo.Nakama: ``Nakama.Protobuf.FriendsBattle+FriendsBattleClient::FriendsBattleOpponentHistory`` | Unavailable/illegal operand conversion |
| Voodoo.Nakama: ``Nakama.Protobuf.FriendsBattle+FriendsBattleClient::FriendsBattleOpponentHistoryAsync`` | Unavailable/illegal operand conversion |
| Microsoft.Extensions.Logging.Abstractions: ``Microsoft.Extensions.Logging.LoggerMessage+<>c__DisplayClass12_0`2::<Define>g__Log\|0`` | Unavailable/illegal operand conversion |
| Microsoft.Extensions.Logging.Abstractions: ``Microsoft.Extensions.Logging.LoggerMessage+<>c__DisplayClass14_0`3::<Define>g__Log\|0`` | Unavailable/illegal operand conversion |
| AdjustSdk.Scripts: ``AdjustSdk.AdjustUtils::ConvertReadOnlyCollectionOfPairsToJson`` | Unproven EH pads |
| AdjustSdk.Scripts: ``AdjustSdk.AdjustUtils::ConvertReadOnlyCollectionOfTripletsToJson`` | Unproven EH pads |
| MoreMountains.Tools: ``MoreMountains.FeedbacksForThirdParty.MMF_UIToolkitFontSize::SetValue`` | Unavailable/illegal operand conversion |
| MoreMountains.Tools: ``MoreMountains.Feedbacks.MMTimeManager::OnMMFreezeFrameEvent`` | Unavailable/illegal operand conversion |
| VoodooTuneSDK: ``Voodoo.Tune.Internal.AsyncHelpers::RunSync`` | Unproven EH pads |
| Google.Play.Games: ``GooglePlayGames.Android.AndroidNearbyConnectionClient+EndpointDiscoveryCallback::onEndpointFound`` | Unavailable/illegal operand conversion |
| Google.Play.Games: ``GooglePlayGames.Android.AndroidNearbyConnectionClient+<>c__DisplayClass31_0`1::<ToOnGameThread>b__0`` | Unemitted native store; Unresolved delegate target; Unresolved native memory |
| Google.Play.Games: ``GooglePlayGames.Android.AndroidNearbyConnectionClient+<>c__DisplayClass31_1`1::<ToOnGameThread>b__1`` | Unresolved native memory; Unresolved call/dispatch |
| Google.Play.Games: ``GooglePlayGames.Android.AndroidNearbyConnectionClient+<>c__DisplayClass32_0`2::<ToOnGameThread>b__0`` | Unresolved call/dispatch; Class-pointer/type-handle mismatch; Unresolved native memory; Unavailable/illegal operand conversion; Stack failure |
| Google.Play.Games: ``GooglePlayGames.Android.AndroidNearbyConnectionClient+<>c__DisplayClass32_1`2::<ToOnGameThread>b__1`` | Class-pointer/type-handle mismatch; Unresolved native memory; Unresolved call/dispatch; Undefined scalar local; Stack failure |
| Google.Play.Games: ``GooglePlayGames.Android.AndroidSavedGameClient+AndroidConflictResolver::ResolveConflict`` | Unavailable/illegal operand conversion; Unresolved native memory; Undefined scalar local; A hidden shared-generic argument landed in parameter slot System.String; the real argument was dropped upstream.; Unproven EH pads |
| Google.Play.Games: ``GooglePlayGames.Android.AndroidSavedGameClient+AndroidConflictResolver::<ResolveConflict>b__8_1`` | Unavailable/illegal operand conversion |
| Google.Play.Games: ``GooglePlayGames.Android.AndroidSavedGameClient+AndroidConflictResolver::<ChooseMetadata>b__9_1`` | Unavailable/illegal operand conversion |
| Google.Play.Games: ``GooglePlayGames.Android.AndroidSavedGameClient+<>c__DisplayClass10_0::<FetchAllSavedGames>b__0`` | Unavailable/illegal operand conversion; A hidden shared-generic argument landed in parameter slot System.String; the real argument was dropped upstream.; Undefined scalar local; Unresolved native memory; Unproven EH pads |
| Google.Play.Games: ``GooglePlayGames.Android.AndroidSavedGameClient+<>c__DisplayClass4_0::<OpenWithAutomaticConflictResolution>b__0`` | Unresolved native memory; Unresolved call/dispatch |
| Google.Play.Games: ``GooglePlayGames.Android.AndroidSavedGameClient+<>c__DisplayClass6_0::<InternalOpen>b__0`` | Unavailable/illegal operand conversion; Unproven EH pads |
| Google.Play.Games: ``GooglePlayGames.Android.AndroidSavedGameClient+<>c__DisplayClass6_0::<InternalOpen>b__1`` | Unavailable/illegal operand conversion |
| Google.Play.Games: ``GooglePlayGames.Android.AndroidSavedGameClient+<>c__DisplayClass9_0::<CommitUpdate>b__1`` | Unavailable/illegal operand conversion |
| Google.Play.Games: ``GooglePlayGames.Android.AndroidTaskUtils+TaskOnCompleteProxy`1::onComplete`` | Unproven EH pads |
| Google.Play.Games: ``GooglePlayGames.Android.AndroidTaskUtils+TaskOnFailedProxy::onFailure`` | Unproven EH pads |
| Google.Play.Games: ``GooglePlayGames.BasicApi.AuthScopeExtensions+<>c::<.cctor>b__4_0`` | Unavailable/illegal operand conversion |
| Google.Play.Games: ``GooglePlayGames.BasicApi.SavedGame.SavedGameMetadataUpdate+Builder::WithUpdatedPlayedTime`` | Unavailable/illegal operand conversion |
| Google.Play.Games: ``GooglePlayGames.Android.AndroidNearbyConnectionClient+OnGameThreadDiscoveryListener+<>c__DisplayClass2_0::<OnEndpointFound>b__0`` | Unavailable/illegal operand conversion |

</details>

<details>
<summary>All 82 newly clean owned methods after development</summary>

- CastleClashers.Game: ``UnityEngine.Sprite CastleBuildElements::GetSpriteElement(System.Collections.Generic.List`1<AttachDirection>, WallType, System.Int32)``
- CastleClashers.Game: ``System.Void CastleDamageTracker::OnTurnStart(PlayingSide)``
- CastleClashers.Game: ``System.Void CastleDamageTracker::FlushDamage()``
- CastleClashers.Game: ``UnityEngine.Transform CastleMaker::CheckIfBelongsToAnyFoundation(System.Int32, System.Int32)``
- CastleClashers.Game: ``System.Boolean CastleMaker::CheckIfHasFoundationAbove(System.Int32, System.Int32)``
- CastleClashers.Game: ``System.Collections.Generic.List`1<UnityEngine.Vector3> CastleMaker::WhereCanUpgrade()``
- CastleClashers.Game: ``System.Int32 CastleMaker::GetBottomPartAverageUpgradeLevel()``
- CastleClashers.Game: ``System.Collections.Generic.List`1<UnityEngine.Transform> CastleMaker::GetImpactedObjects(System.Int32, System.Int32)``
- CastleClashers.Game: ``System.Void CastleMaker::AddFoundation(System.Int32, System.Int32, System.Int32)``
- CastleClashers.Game: ``System.Void CastleMaker::RemoveFoundation(System.Int32, System.Int32)``
- CastleClashers.Game: ``System.Int32[] ChestController::AllocatePieces(System.Int32, System.Int32)``
- CastleClashers.Game: ``System.Int32 LocalNotificationController::GetDelaySecondsUntilNextRewardNotification(System.DateTime, System.Int32)``
- CastleClashers.Game: ``System.Void LocalNotificationController::ScheduleNotificationsForCastleBuildingAndUpgrading()``
- CastleClashers.Game: ``System.Void DragAndDropUIToWorldBase::CompleteDrag()``
- CastleClashers.Game: ``System.Int32 EconomyScaler::RoundToNearest(System.Single, System.Int32)``
- CastleClashers.Game: ``System.Void EnemyTrophySelector::CalculateTrophyChangeInternal(System.Boolean, TrophyConfigSO, ArenaData, ArenaTrophyItem, System.Int32, System.Int32, System.Int32&, System.Int32&, System.Int32&, System.Single&)``
- CastleClashers.Game: ``System.Int32 EnemyTrophySelector::SampleTriangularOffset(System.Int32, System.Int32, System.Single, System.Int32)``
- CastleClashers.Game: ``System.Int32 EnemyTrophySelector::SnapToStep(System.Int32, System.Int32)``
- CastleClashers.Game: ``System.Int32 EngineersController::GetGemsNeededToUpgrade(System.Int32)``
- CastleClashers.Game: ``System.Void GlobalLeaderboardPlayerEntry::UpdateRankDisplay()``
- CastleClashers.Game: ``System.Void ChainOfferController::EndChain(System.Boolean)``
- CastleClashers.Game: ``System.Void ConclusionPanel::DoubleMoneySuccess()``
- CastleClashers.Game: ``System.Void UnitUpgradePanel::OnUpgradeSliderValueChanged(System.Single)``
- CastleClashers.Game: ``System.Void UnitUpgradingPanel::OnReduceTimeRVButtonClicked()``
- CastleClashers.Game: ``UnityEngine.GameObject UnitsPanel::GetMenuUnitItemGameObject(System.String)``
- CastleClashers.Game: ``System.Void PowerUpsController::SpawnRandomPowerUp()``
- CastleClashers.Game: ``System.Boolean CleanProjectile::ProcessUnitHit(UnityEngine.Collider2D, UnityEngine.Vector2, System.Single, System.Single)``
- CastleClashers.Game: ``System.Void CleanPulsarProjectile::InitWithProgress(UnityEngine.Vector3, System.Single, ProjectileData, System.Int32, System.Int32, System.Single, System.Single, UnitData)``
- CastleClashers.Game: ``System.Int32 TrainersController::GetGemsNeededToUpgrade(System.Int32)``
- CastleClashers.Game: ``System.Void WLBFakePlayerItem::SetData(WeeklyLeaderboardPlayerEntry, System.Int32)``
- CastleClashers.Game: ``System.Void WLBMilestoneItem::SetBackgroundColors(UnityEngine.Color)``
- CastleClashers.Game: ``System.Single WeeklyLeaderboardController::GetNormalizedLeaderboardTime(System.DateTime)``
- CastleClashers.Game: ``System.Int32 WeeklyLeaderboardController::GetWeekNumber(System.DateTime)``
- CastleClashers.Game: ``System.Int32 Tournament.TournamentRewardsConfigSO::GetEndCoinsForPosition(System.Int32)``
- CastleClashers.Game: ``System.Int32 Tournament.TournamentRewardsConfigSO::GetEndWoodForPosition(System.Int32)``
- CastleClashers.Game: ``System.Int32 Tournament.TournamentRewardsConfigSO::GetScaledAmount(System.Int32, System.Int32, System.Boolean)``
- CastleClashers.Game: ``System.Int32 RoyalBlessing.RoyalBlessingController::GetCurrentDayIndex()``
- CastleClashers.Game: ``System.DateTime EpiCoro.Internal.IAP.AvatarShopRotationController::GetNextResetTime(System.DateTime)``
- CastleClashers.Game: ``System.DateTime EpiCoro.Internal.IAP.BannerShopRotationController::GetNextResetTime(System.DateTime)``
- CastleClashers.Game: ``System.DateTime EpiCoro.Internal.IAP.EmoteShopRotationController::GetNextResetTime(System.DateTime)``
- CastleClashers.Game: ``System.DateTime EpiCoro.Internal.IAP.DecorationShopRotationController::GetNextResetTime(System.DateTime)``
- CastleClashers.Game: ``System.Int32 CastleClashers.UnitLevelUtility::ClampToMaxInternalLevel(System.Single)``
- CastleClashers.Game: ``System.Int32[] CastleClashers.Rewards.ChestRoller::AllocatePieces(System.Int32, System.Int32)``
- CastleClashers.Game: ``System.Boolean CastleClashers.PvP.PvpProtocol::TryDecodePickupConsumed(Nakama.Protobuf.CCRelayServerEnvelope, System.String&, CastleClashers.PvP.PickupKind&, System.Boolean&, System.Int32&)``
- CastleClashers.Game: ``System.Boolean CastleClashers.HumanLikeBots.CastleConfigSO::IsCategoryValid(CastleClashers.HumanLikeBots.CastleBuildCategory, System.Int32, System.Int32, System.Int32)``
- CastleClashers.Game: ``System.Int32 CastleClashers.HumanLikeBots.WheelSelectionConfigSO::GetWinningBotLevelBonus(System.Single, System.Boolean)``
- CastleClashers.Game: ``System.Void CastleClashers.HumanLikeBots.HumanLikeBotProfile::PreCalculateCastleStats(CastleClashers.HumanLikeBots.HumanLikeBotProfile, CastleClashers.HumanLikeBots.HumanLikeBotConfigSO)``
- CastleClashers.Game: ``System.Boolean MatchEndController+<Fireworks>d__15::MoveNext()``
- CastleClashers.Game: ``System.Boolean InfiniteScrollRect+<FocusRoutine>d__54::MoveNext()``
- CastleClashers.Game: ``System.Boolean RewardMoneyItem+<CountTo>d__6::MoveNext()``
- CastleClashers.Game: ``System.Boolean RewardUnitItem+<CountTo>d__20::MoveNext()``
- CastleClashers.Game: ``System.Boolean RewardWoodItem+<CountTo>d__6::MoveNext()``
- Assembly-CSharp: ``System.Void AnalyticsProviderButton::SetButtonColor(UnityEngine.Color)``
- Assembly-CSharp: ``System.String ConsentManagementProvider.UsnatConsent::ToFullString()``
- Assembly-CSharp: ``System.Void Voodoo.Analytics.Tracker::StartSendEventsTimer()``
- Assembly-CSharp: ``System.Int32 Voodoo.ADN.Internal.AdnAppSignalsCollector::TimeSinceStartup()``
- Assembly-CSharp: ``System.Void Voodoo.Live.PersistencyRetroCompatibility::Apply(System.String, Voodoo.Live.IBlackboard, System.String)``
- Assembly-CSharp: ``System.Int32 Voodoo.Live.TimeEventRecurrence::GetIntervals(System.DateTime, System.DateTime)``
- Assembly-CSharp: ``System.DateTime Voodoo.Live.DateTimeExtensions::GetMonday(System.DateTime)``
- Assembly-CSharp: ``System.Int32 Voodoo.Live.Sample.RotationOperator::GetCurrentRotation(System.TimeSpan)``
- Assembly-CSharp: ``System.Void Voodoo.Live.Sample.WheelPie::Setup(System.Single, Voodoo.Live.IReward, System.Single, UnityEngine.Color)``
- Assembly-CSharp: ``System.Void Voodoo.Sauce.Debugger.DebuggerHeader::UpdateTarget(Voodoo.Sauce.Debugger.Screen)``
- Assembly-CSharp: ``System.Void Voodoo.Sauce.Debugger.DebugButtonWithInputField::SetColor(UnityEngine.Color)``
- Assembly-CSharp: ``System.Void Voodoo.Sauce.Debugger.DebugMenuItemButton::SetIcon(UnityEngine.Sprite, UnityEngine.Color)``
- Assembly-CSharp: ``System.Void Voodoo.Sauce.Debugger.Widgets.DebugTextPair::SetStyle(UnityEngine.Color, TMPro.FontStyles)``
- Assembly-CSharp: ``System.Void Voodoo.Sauce.Privacy.UI.AccessDataScreen::Initialize(Voodoo.Sauce.Privacy.UI.AccessDataScreen+Parameters)``
- Assembly-CSharp: ``System.Void Voodoo.Sauce.Privacy.UI.CmpSettingsScreen::Initialize(Voodoo.Sauce.Privacy.UI.CmpSettingsScreen+Parameters)``
- Assembly-CSharp: ``System.Void Voodoo.Sauce.Privacy.UI.DeleteScreen::Initialize(Voodoo.Sauce.Privacy.UI.DeleteScreen+Parameters)``
- Assembly-CSharp: ``System.Void Voodoo.Sauce.Privacy.UI.LearnMoreScreen::Initialize(Voodoo.Sauce.Privacy.UI.LearnMoreScreen+Parameters)``
- Assembly-CSharp: ``System.Void Voodoo.Sauce.Privacy.UI.ParternsScreen::Initialize(Voodoo.Sauce.Privacy.UI.ParternsScreen+Parameters)``
- Assembly-CSharp: ``System.Void Voodoo.Sauce.Privacy.UI.PopupScreen::Initialize(Voodoo.Sauce.Privacy.UI.PopupScreen+Parameters)``
- Assembly-CSharp: ``System.Void Voodoo.Sauce.Privacy.UI.PrivacyScreen::Initialize(Voodoo.Sauce.Privacy.UI.PrivacyScreen+Parameters)``
- Assembly-CSharp: ``System.Void Voodoo.Sauce.Privacy.UI.SettingsScreen::Initialize(Voodoo.Sauce.Privacy.UI.SettingsScreen+Parameters)``
- Assembly-CSharp: ``System.Int32 Voodoo.Sauce.Ads.AppOpenRewardedInterstitialWrapper::GetReward()``
- Assembly-CSharp: ``UnityEngine.Vector2 Voodoo.Sauce.Ads.MrecAdBehaviour::GetMrecPlaceholderSize()``
- Assembly-CSharp: ``UnityEngine.Vector2 Voodoo.Sauce.Internal.Utils.ScreenSizeUtils::GetResolutionNativeToUnityRatio()``
- Assembly-CSharp: ``System.Int32 Voodoo.Sauce.Internal.Attribution.AttributionTimingService::CalculateHoursSinceFirstLaunch()``
- Assembly-CSharp: ``System.Void Voodoo.Sauce.Internal.Ads.BannerBackground::Show(UnityEngine.Color)``
- Assembly-CSharp: ``System.Void Voodoo.Sauce.Internal.Ads.BannerBackground::SetColor(UnityEngine.Color)``
- Assembly-CSharp: ``System.Void SoftMasking.Samples.Item::Set(System.String, UnityEngine.Sprite, UnityEngine.Color, System.Single, System.Single)``
- Assembly-CSharp: ``System.Void ShapeFX.Demo.ShFX_Atlas::UpdateToNewGroup(System.Int32)``
- Assembly-CSharp: ``System.Boolean Voodoo.Sauce.Core.Request+<doRequest>d__5::MoveNext()``

</details>

<details>
<summary>Normal-dataflow handoff: all 61 methods and their native protected ranges</summary>

Every row has surviving normal ISIL and mapped emitted IL; the latter is
unreachable. Multiple native candidates in one method are combined here.

| Method / entry | Native protected ranges |
|---|---|
| ``AnimatedWeeklyLeaderboardPanel::CreateMilestoneAwareScrollTween`` (`0x3db004c`) | ``3DB09D4-3DB09DC, 3DB0A34-3DB0A3C, 3DB0A80-3DB0A8C, 3DB0EDC-3DB0EE0, 3DB0EE0-3DB0EE4`` |
| ``CastleClashers.HumanLikeBots.HumanLikeAimController::IsBotHealHelperActive`` (`0x3e7a538`) | ``3E7A6B0-3E7A6B8, 3E7A6D0-3E7A6D4, 3E7A6D4-3E7A6E4, 3E7A76C-3E7A770`` |
| ``CastleClashers.HumanLikeBots.HumanLikeAimController::IsPlayerAntiMissileReady`` (`0x3e79e04`) | ``3E79F78-3E79F80, 3E79F98-3E79F9C, 3E79F9C-3E79FAC, 3E7A034-3E7A038`` |
| ``CastleClashers.HumanLikeBots.HumanLikeAimController::IsPlayerDefensiveHelperActive`` (`0x3e790dc`) | ``3E79264-3E7926C, 3E79284-3E79288, 3E79288-3E79298, 3E792C0-3E792C4, 3E792C4-3E792D4, 3E792EC-3E792F4, 3E79318-3E79348, 3E79384-3E79388, 3E79388-3E7938C, 3E7938C-3E79390, 3E79390-3E79394`` |
| ``CastleClashers.HumanLikeBots.HumanLikeAimController::IsPlayerShieldActive`` (`0x3e7a09c`) | ``3E7A210-3E7A218, 3E7A230-3E7A234, 3E7A234-3E7A244, 3E7A2CC-3E7A2D0`` |
| ``ConclusionController+<TrophyProgressionAndArenaRewards_2>d__52::MoveNext`` (`0x3ee4440`) | ``3EE5228-3EE5230, 3EE523C-3EE5240, 3EE524C-3EE5254, 3EE58C0-3EE58C4, 3EE58C4-3EE58C8`` |
| ``GooSplatPointGroup+<InitGooPoints>d__15::MoveNext`` (`0x3ebd828`) | ``3EBDBC8-3EBDBD0, 3EBDBDC-3EBDBF4, 3EBDE0C-3EBDE10, 3EBDE10-3EBDE14`` |
| ``MatchEndController+<ShowEndingReason>d__12::MoveNext`` (`0x3f0acbc`) | ``3F0B484-3F0B48C, 3F0B49C-3F0B4A8, 3F0B4AC-3F0B4B4, 3F0B4B8-3F0B4C4, 3F0B6B8-3F0B6BC, 3F0B6BC-3F0B6C0, 3F0B6C0-3F0B6C4`` |
| ``UnitsPanel+<PlayUnseenUnitUpgrades>d__30::MoveNext`` (`0x3cd31d8`) | ``3CD3398-3CD33A0, 3CD33AC-3CD33B8, 3CD33BC-3CD33C4, 3CD33D4-3CD33E4, 3CD33E4-3CD33F0, 3CD33F4-3CD3400, 3CD3498-3CD34A0, 3CD34AC-3CD34B8, 3CD34BC-3CD34C4, 3CD34D4-3CD34E4, 3CD34E4-3CD34F0, 3CD34F4-3CD3500, 3CD3590-3CD3594, 3CD3594-3CD3598, 3CD3598-3CD359C, 3CD359C-3CD35A0, 3CD35A0-3CD35A4, 3CD35A4-3CD35A8`` |
| ``AnalyticsController::FlattenForVoodoo`` (`0x3ee7b28`) | ``3EE7C90-3EE7C98, 3EE7CFC-3EE7D00, 3EE7D00-3EE7D24, 3EE7D30-3EE7D40, 3EE7D70-3EE7D74, 3EE7D74-3EE7D78`` |
| ``MatchTelemetryTrackerController::BuildDefenderUtilitiesWithDamage`` (`0x3f12720`) | ``3F12938-3F12940, 3F12954-3F12958, 3F12958-3F12968, 3F12980-3F12984, 3F12984-3F12994, 3F12A08-3F12A20, 3F12A38-3F12A40, 3F12A58-3F12A7C, 3F12A8C-3F12AB0, 3F12AC0-3F12AE4, 3F12B00-3F12B18, 3F12B34-3F12B3C, 3F12B54-3F12B78, 3F12B88-3F12BAC, 3F12BBC-3F12BE0, 3F12E70-3F12E74, 3F12E78-3F12E7C, 3F12E80-3F12E84, 3F12E84-3F12E88`` |
| ``MatchTelemetryTrackerController::BuildRuntimeUtilitiesPayload`` (`0x3f121fc`) | ``3F123F8-3F12400, 3F12414-3F12418, 3F12418-3F12428, 3F12440-3F12444, 3F12444-3F12454, 3F12460-3F12470, 3F1248C-3F12494, 3F124AC-3F124D0, 3F124FC-3F12518, 3F12688-3F1268C, 3F12694-3F12698, 3F12698-3F1269C`` |
| ``MatchTelemetryTrackerController::BuildUtilitiesEndStatePayload`` (`0x3f15900`) | ``3F15B5C-3F15B64, 3F15B78-3F15B7C, 3F15B7C-3F15B8C, 3F15BA4-3F15BA8, 3F15BA8-3F15BB8, 3F15BC4-3F15BDC, 3F15C00-3F15C08, 3F15C18-3F15C44, 3F15C48-3F15C60, 3F15C64-3F15C74, 3F15C7C-3F15CB0, 3F15CB4-3F15CC4, 3F15CCC-3F15CFC, 3F15D00-3F15D10, 3F15D18-3F15D44, 3F15D48-3F15D58, 3F15D60-3F15DB0, 3F15DD4-3F15E00, 3F16104-3F16108, 3F16134-3F16138, 3F16138-3F1613C, 3F1613C-3F16140`` |
| ``Voodoo.Sauce.Internal.Analytics.AmplitudeIAPEventsHandler::BuildCommonIAPData`` (`0x39bff00`) | ``39C0AD4-39C0ADC, 39C0AE8-39C0AF0`` |
| ``Voodoo.Sauce.Internal.Analytics.FirebaseAnalyticsEvent::ToParameters`` (`0x39df738`) | ``39DF874-39DF87C, 39DF8AC-39DF8B4, 39DF8BC-39DF918, 39DF920-39DF9A0, 39DF9A8-39DFA28, 39DFA38-39DFA44, 39DFA54-39DFA60, 39DFA70-39DFA7C, 39DFAAC-39DFAB0, 39DFAB0-39DFAB4, 39DFAB4-39DFAB8, 39DFAB8-39DFABC, 39DFABC-39DFAC4, 39DFAC4-39DFACC`` |
| ``MatchTelemetryTrackerController::BuildUtilitiesPayload`` (`0x3f14a38`) | ``3F14CB4-3F14CBC, 3F14CD0-3F14CD4, 3F14CD4-3F14CE4, 3F14CFC-3F14D00, 3F14D00-3F14D10, 3F14D24-3F14D3C, 3F14D60-3F14D68, 3F14D80-3F14DAC, 3F14DB8-3F14DD0, 3F14DD4-3F14DE4, 3F14DF4-3F14E28, 3F14E2C-3F14E3C, 3F14E4C-3F14E7C, 3F14E80-3F14E90, 3F14EA0-3F14ECC, 3F14EE0-3F14F30, 3F150CC-3F150D0, 3F150D4-3F150D8, 3F150D8-3F150DC, 3F150DC-3F150E0`` |
| ``CastleClashers.HumanLikeBots.HumanLikeAimController::SelectFiringUnit`` (`0x3e781c4`) | ``3E78CC0-3E78CC8, 3E78CD8-3E78CF4, 3E78D50-3E78D60, 3E78D70-3E78D74, 3E78EF0-3E78EF8, 3E78F04-3E78F14, 3E78F18-3E78F20, 3E78F30-3E78F50, 3E78FAC-3E78FB0, 3E78FB4-3E78FB8`` |
| ``CastleClashers.HumanLikeBots.HumanLikeCastleBuilder::DetermineSpecialWidth`` (`0x3e972cc`) | ``3E97770-3E97778`` |
| ``CastleClashers.HumanLikeBots.HumanLikeAimController::GetDeepInsideCastleTarget`` (`0x3e71914`) | ``3E72514-3E7251C, 3E72534-3E7253C, 3E727B0-3E727B4`` |
| ``CastleClashers.HumanLikeBots.HumanLikeAimController::TryGetRightSideNonSpecialChunk`` (`0x3e73c44`) | ``3E7441C-3E74424, 3E74434-3E74450, 3E74464-3E74478`` |
| ``CastleClashers.HumanLikeBots.HumanLikeAimController::TryGetUnderLeveledBlock`` (`0x3e6f5dc`) | ``3E6FDEC-3E6FDF4, 3E6FE20-3E6FE28, 3E6FE34-3E6FE3C, 3E6FE4C-3E6FE54, 3E6FE64-3E6FE74, 3E6FE80-3E6FE88, 3E6FE94-3E6FE9C, 3E6FEA4-3E6FEB0, 3E6FEC0-3E6FEC8, 3E6FECC-3E6FED4, 3E6FEEC-3E6FF20, 3E6FF40-3E6FF60, 3E6FF78-3E6FF80, 3E6FF80-3E6FF88, 3E6FFAC-3E6FFE0, 3E70064-3E7006C, 3E70088-3E70094, 3E700A0-3E700D0, 3E700E0-3E700F4, 3E70118-3E7011C, 3E70120-3E70124, 3E70128-3E7012C, 3E70130-3E70134, 3E70134-3E70138`` |
| ``CastleClashers.HumanLikeBots.HumanLikeAimController::GetPlayerCastleCenterY`` (`0x3e7aaa0`) | ``3E7AC04-3E7AC0C, 3E7AC20-3E7AC24, 3E7AC24-3E7AC34, 3E7AC3C-3E7AC48, 3E7AC4C-3E7AC54, 3E7AC58-3E7AC64, 3E7ACBC-3E7ACC0, 3E7ACC0-3E7ACC4`` |
| ``CastleClashers.HumanLikeBots.HumanLikeAimController::GetPlayerCastleDamagePercent`` (`0x3e79410`) | ``3E79570-3E79578, 3E7958C-3E79590, 3E79590-3E795A0, 3E795A8-3E795B4, 3E795B8-3E795C0, 3E79618-3E7961C, 3E7961C-3E79620`` |
| ``MatchTelemetryTrackerController::ComputeDefenderUtilityDamage`` (`0x3f0ffd8`) | ``3F10120-3F10128, 3F1013C-3F10140, 3F10140-3F10150, 3F10168-3F1016C, 3F1016C-3F1017C, 3F1027C-3F10280, 3F10284-3F10288`` |
| ``Voodoo.Sauce.Common.Utils.NewManifestUtilsImpl::GetXmlNodeChildValue`` (`0x3af18f8`) | ``3AF1D08-3AF1D10, 3AF1D18-3AF1D28, 3AF1D34-3AF1D40, 3AF1D44-3AF1D50, 3AF1DAC-3AF1DB0, 3AF1DB0-3AF1DB4`` |
| ``CardRewardsPanel::SetData`` (`0x3c9d31c`) | ``3C9D62C-3C9D634, 3C9D64C-3C9D650, 3C9D654-3C9D660, 3C9D668-3C9D66C, 3C9D67C-3C9D684, 3C9D6CC-3C9D6D0, 3C9D6D0-3C9D6D4, 3C9D6D4-3C9D6D8`` |
| ``CastleClashers.Core.Reactive`1::ClearDestroyedObjects<D>`` (`0x4363878`) | ``4363AD8-4363AE0, 4363AF4-4363AFC`` |
| ``CastleClashers.HumanLikeBots.ArenaLogsDebugger::SetupScreen`` (`0x3e84db0`) | ``3E854F0-3E854F8, 3E8550C-3E85510, 3E8551C-3E85520, 3E8553C-3E85544, 3E85558-3E85598, 3E855C4-3E85604, 3E8560C-3E8564C, 3E85658-3E85698, 3E856A4-3E856E4, 3E856F0-3E856FC, 3E85738-3E8576C, 3E85794-3E8579C, 3E857AC-3E857B4, 3E857D8-3E857E0, 3E85800-3E8580C, 3E8581C-3E85828, 3E8583C-3E85844, 3E8588C-3E85894, 3E858A4-3E858E4, 3E858F0-3E85918, 3E85924-3E8594C, 3E85958-3E85980, 3E8598C-3E859CC, 3E859DC-3E85A04, 3E85A10-3E85A1C, 3E85A68-3E85A94, 3E85AD4-3E85B0C, 3E85B48-3E85B74, 3E85CC0-3E85CC4, 3E85CC4-3E85CCC, 3E85CCC-3E85CD0, 3E85CD0-3E85CD4, 3E85CD4-3E85CD8, 3E85CD8-3E85CDC, 3E85CDC-3E85CE0, 3E85CE0-3E85CE4, 3E85CE4-3E85CF4, 3E85CF4-3E85D00, 3E85D00-3E85D0C, 3E85D0C-3E85D18, 3E85D18-3E85D24, 3E85D24-3E85D30, 3E85D30-3E85D38, 3E85D38-3E85D3C, 3E85D3C-3E85D40, 3E85D40-3E85D44, 3E85D44-3E85D48, 3E85D48-3E85D4C, 3E85D4C-3E85D58, 3E85D58-3E85D64, 3E85D64-3E85D70, 3E85D70-3E85D74, 3E85D74-3E85D80, 3E85D80-3E85D8C, 3E85D8C-3E85D90`` |
| ``CastleMaker::Build`` (`0x3e597dc`) | ``3E5C028-3E5C030, 3E5C0AC-3E5C0B0, 3E5C0BC-3E5C0C4, 3E5C0CC-3E5C0D8, 3E5C0E8-3E5C0F4, 3E5C11C-3E5C128, 3E5C128-3E5C134, 3E5C13C-3E5C144, 3E5C144-3E5C150, 3E5C174-3E5C180, 3E5C18C-3E5C194, 3E5C19C-3E5C1A4, 3E5C1B0-3E5C1B8, 3E5C1E0-3E5C1E8, 3E5C1F0-3E5C1F8, 3E5C204-3E5C20C, 3E5C21C-3E5C22C, 3E5C22C-3E5C240, 3E5C248-3E5C254, 3E5C254-3E5C260, 3E5C268-3E5C274, 3E5C284-3E5C290, 3E5C29C-3E5C2B4, 3E5C2C0-3E5C2C8, 3E5C2D8-3E5C2E0, 3E5E0FC-3E5E100, 3E5E104-3E5E108, 3E5E10C-3E5E110, 3E5E114-3E5E118, 3E5E11C-3E5E120, 3E5E124-3E5E128, 3E5E12C-3E5E130, 3E5E134-3E5E138, 3E5E13C-3E5E140, 3E5E144-3E5E148, 3E5E14C-3E5E150, 3E5E5D0-3E5E5D8, 3E5E5F8-3E5E5FC, 3E5F064-3E5F068, 3E5F068-3E5F06C`` |
| ``CastleMaker::SpawnShields`` (`0x3e6295c`) | ``3E6336C-3E63374, 3E63394-3E633A0, 3E633AC-3E633B4, 3E633C4-3E633D8, 3E633DC-3E633E8, 3E633F0-3E633FC, 3E633FC-3E63408, 3E63414-3E6341C, 3E63428-3E63430, 3E6344C-3E63464, 3E63464-3E6347C, 3E6348C-3E63490, 3E634A8-3E634AC, 3E634D4-3E634DC, 3E6356C-3E63570, 3E6358C-3E635A4, 3E635B0-3E635CC, 3E635E8-3E635F0, 3E63C60-3E63C64, 3E63C84-3E63C8C, 3E63C9C-3E63CA0, 3E63CA0-3E63CB0, 3E63CCC-3E63CD0, 3E63CD0-3E63CE0, 3E63CF8-3E63CFC, 3E63D0C-3E63D10, 3E63D10-3E63D20, 3E63D28-3E63D34, 3E63D50-3E63D58, 3E63D6C-3E63D74, 3E63D8C-3E63D94, 3E63E30-3E63E34, 3E63E68-3E63E70, 3E63E80-3E63E88, 3E63F0C-3E63F10, 3E63F2C-3E63F38, 3E63FAC-3E63FB0, 3E63FCC-3E63FD4, 3E63FF0-3E63FF8, 3E6402C-3E64034, 3E64068-3E64070, 3E640A4-3E640AC, 3E640E4-3E640F0, 3E64220-3E64224, 3E64240-3E64248, 3E6425C-3E64260, 3E64260-3E64274, 3E64290-3E64294, 3E64294-3E642A4, 3E642AC-3E642CC, 3E642D8-3E642E4, 3E642F0-3E642FC, 3E64308-3E64310, 3E64314-3E64320, 3E64A68-3E64A6C, 3E64A6C-3E64A70, 3E64A70-3E64A74, 3E64A74-3E64A78, 3E64A78-3E64A7C, 3E64A80-3E64A84, 3E64A84-3E64A88, 3E64A88-3E64A8C, 3E64A8C-3E64A90, 3E64AA0-3E64AA4, 3E64AA4-3E64AA8, 3E64AA8-3E64AAC, 3E64AAC-3E64AB0, 3E64AB0-3E64AB4, 3E64AB4-3E64AB8, 3E64AD0-3E64AD4, 3E64ADC-3E64AE0, 3E64AE0-3E64AE4, 3E64AE4-3E64AE8, 3E64AF0-3E64AF4, 3E64AF4-3E64AF8, 3E64AF8-3E64AFC, 3E64AFC-3E64B00, 3E64B00-3E64B04, 3E64B04-3E64B08, 3E634FC-3E63504, 3E63518-3E6351C, 3E6351C-3E6352C, 3E6354C-3E63554, 3E643B0-3E643B4, 3E63618-3E63620, 3E6362C-3E6364C, 3E63658-3E63664, 3E6366C-3E63678, 3E63688-3E63690, 3E6369C-3E636A4, 3E636A4-3E636B4, 3E636D0-3E636D8, 3E636F0-3E636F4, 3E636F4-3E63704, 3E63710-3E63718, 3E638A0-3E63914, 3E63934-3E63938, 3E63938-3E6394C, 3E63978-3E63980, 3E63988-3E63990, 3E639A8-3E639AC, 3E639B0-3E639C8, 3E639E4-3E639F0, 3E63A08-3E63A20, 3E63A20-3E63A30, 3E63A48-3E63A4C, 3E63A58-3E63A64, 3E63A6C-3E63A78, 3E63A88-3E63A94, 3E63ABC-3E63AC8, 3E63AC8-3E63AD4, 3E63AD8-3E63AEC, 3E63AF8-3E63B00, 3E63B00-3E63B10, 3E63B20-3E63B24, 3E63B34-3E63B38, 3E63B38-3E63B48, 3E63B58-3E63B60, 3E63B60-3E63B6C, 3E63B74-3E63B80, 3E63B90-3E63BA0, 3E63BB4-3E63BBC, 3E6434C-3E64350, 3E64354-3E64358, 3E6435C-3E64360, 3E6436C-3E64370, 3E6437C-3E64380, 3E64390-3E64394, 3E64398-3E6439C, 3E643A0-3E643A4, 3E643A8-3E643AC, 3E643B8-3E643BC, 3E643C0-3E643C4, 3E643C8-3E643CC, 3E643D0-3E643D4, 3E643D8-3E643DC, 3E643E0-3E643E4, 3E643E8-3E643EC, 3E643F0-3E643F4, 3E643F8-3E643FC, 3E63DBC-3E63DC4, 3E63DD8-3E63DDC, 3E63DDC-3E63DEC, 3E63DF4-3E63E00, 3E63E08-3E63E14, 3E63EA8-3E63EB0, 3E63EC4-3E63EC8, 3E63EC8-3E63ED8, 3E63EE0-3E63EF0, 3E64364-3E64368, 3E64374-3E64378, 3E63F74-3E63F7C, 3E63F88-3E63F90, 3E64118-3E64120, 3E6413C-3E6414C, 3E64184-3E64194, 3E641A0-3E641A8, 3E641B4-3E641BC, 3E641D4-3E641DC, 3E641E8-3E641F4, 3E64324-3E64328, 3E6432C-3E64330, 3E64334-3E64338, 3E6433C-3E64340, 3E64344-3E64348`` |
| ``CastleMaker::SpawnShieldsFromPlacements`` (`0x3e65ec4`) | ``3E66728-3E66730, 3E66744-3E66748, 3E66748-3E66758, 3E66760-3E6676C, 3E66770-3E6677C, 3E6677C-3E6678C, 3E66798-3E667A4, 3E67F28-3E67F2C, 3E67F2C-3E67F30, 3E67F38-3E67F3C, 3E6684C-3E66854, 3E6686C-3E66874, 3E66880-3E668AC, 3E668B4-3E668C0, 3E66910-3E66914, 3E67EA4-3E67EA8, 3E67EB0-3E67EB4, 3E67EB4-3E67EB8, 3E66B4C-3E66B54, 3E66BB8-3E66BC0, 3E66BE4-3E66BF0, 3E66C00-3E66C20, 3E66C2C-3E66C38, 3E66C40-3E66C4C, 3E66C50-3E66C64, 3E66C64-3E66C70, 3E66C80-3E66C8C, 3E66CB4-3E66CC0, 3E66CCC-3E66CD4, 3E66CD4-3E66CE4, 3E66CFC-3E66D00, 3E66D14-3E66D18, 3E66D18-3E66D28, 3E66D34-3E66D4C, 3E66EC8-3E66ED0, 3E66EE8-3E66EF0, 3E66F00-3E66F08, 3E66F18-3E66F48, 3E66F5C-3E66F64, 3E66FAC-3E66FB4, 3E66FC4-3E66FF0, 3E67010-3E67084, 3E670AC-3E670B0, 3E670B0-3E670C0, 3E670D8-3E670E4, 3E670FC-3E67114, 3E67114-3E67124, 3E6713C-3E67140, 3E6714C-3E67158, 3E67160-3E6716C, 3E6717C-3E67188, 3E671B0-3E671BC, 3E671BC-3E671C8, 3E671CC-3E671E0, 3E671EC-3E671F4, 3E671F4-3E67204, 3E6721C-3E67220, 3E67230-3E67234, 3E67234-3E67244, 3E67254-3E6725C, 3E6725C-3E67268, 3E67270-3E6727C, 3E6728C-3E6729C, 3E672B0-3E672B8, 3E67A98-3E67A9C, 3E67AA8-3E67AAC, 3E67AB0-3E67AB4, 3E67AC0-3E67AC4, 3E67AC8-3E67ACC, 3E67AD0-3E67AD4, 3E67AD8-3E67ADC, 3E67AE0-3E67AE4, 3E67AE8-3E67AEC, 3E67AFC-3E67B00, 3E67B04-3E67B08, 3E67B0C-3E67B10, 3E67B14-3E67B18, 3E67B1C-3E67B20, 3E67B24-3E67B28, 3E67B2C-3E67B30, 3E67B34-3E67B38, 3E67B3C-3E67B40, 3E67B44-3E67B48, 3E67B4C-3E67B50, 3E674A0-3E674A8, 3E674BC-3E674C0, 3E674C0-3E674D0, 3E674D8-3E674E4, 3E674EC-3E674F8, 3E67578-3E67580, 3E67594-3E67598, 3E67598-3E675A8, 3E675B0-3E675C0, 3E67AA0-3E67AA4, 3E67AB8-3E67ABC, 3E67634-3E6763C, 3E67648-3E67650, 3E677FC-3E67804, 3E67810-3E67820, 3E67858-3E67868, 3E67874-3E6787C, 3E67888-3E67890, 3E678A8-3E678B0, 3E678BC-3E678C8, 3E67A70-3E67A74, 3E67A78-3E67A7C, 3E67A80-3E67A84, 3E67A88-3E67A8C, 3E67A90-3E67A94`` |
| ``CastleMovement::Update`` (`0x3ec9da4`) | ``3ECA59C-3ECA5A4, 3ECA5B8-3ECA5BC, 3ECA5BC-3ECA5CC, 3ECA5D8-3ECA5E0, 3ECA5F0-3ECA5F4, 3ECA5F4-3ECA604, 3ECA614-3ECA61C, 3ECA670-3ECA678, 3ECA68C-3ECA690, 3ECA690-3ECA6A0, 3ECA6AC-3ECA6B4, 3ECA6C4-3ECA6C8, 3ECA6C8-3ECA6D8, 3ECA6E8-3ECA6F4, 3ECA6F8-3ECA6FC, 3ECA6FC-3ECA700, 3ECA700-3ECA704, 3ECA704-3ECA708, 3ECA7E0-3ECA7E8, 3ECA7FC-3ECA800, 3ECA800-3ECA810, 3ECA81C-3ECA824, 3ECA834-3ECA838, 3ECA838-3ECA848, 3ECA858-3ECA864, 3ECA920-3ECA924, 3ECA924-3ECA928`` |
| ``CastleShieldsPlacingController::OnShieldDroppedInWorld`` (`0x3ed284c`) | ``3ED2A50-3ED2A58, 3ED2A6C-3ED2A88`` |
| ``CastleShieldsPlacingController::RemoveGroup`` (`0x3ed206c`) | ``3ED23D0-3ED23D8, 3ED23EC-3ED23F0, 3ED23F0-3ED2400, 3ED2408-3ED2414, 3ED2414-3ED2420, 3ED2420-3ED2430, 3ED2444-3ED244C, 3ED245C-3ED2460, 3ED2460-3ED2470, 3ED2478-3ED24A4, 3ED24D0-3ED24D4, 3ED24D8-3ED24DC`` |
| ``CastleShieldsPlacingController::SpawnShield`` (`0x3ed2bbc`) | ``3ED3160-3ED3168, 3ED317C-3ED3180, 3ED3180-3ED3190, 3ED3198-3ED31A4, 3ED31A8-3ED31B4, 3ED31B4-3ED31C8, 3ED31D4-3ED31E0, 3ED31E4-3ED31E8, 3ED31E8-3ED31EC, 3ED31EC-3ED31F0, 3ED38A4-3ED38AC, 3ED38BC-3ED38C8, 3ED38CC-3ED38D8, 3ED38D8-3ED38F0, 3ED392C-3ED3934, 3ED3948-3ED3950, 3ED3C70-3ED3C74, 3ED3C78-3ED3C7C, 3ED3C80-3ED3C84, 3ED3C88-3ED3C8C, 3ED3C90-3ED3C94, 3ED3C98-3ED3C9C`` |
| ``CastleShieldsView::PopulateShields`` (`0x3ed6384`) | ``3ED6678-3ED6680, 3ED6698-3ED669C, 3ED66A0-3ED66A8, 3ED66B4-3ED66BC, 3ED66C4-3ED66CC, 3ED66CC-3ED66D8, 3ED66E0-3ED66EC, 3ED672C-3ED6730, 3ED6730-3ED6734, 3ED6734-3ED6738`` |
| ``CombineChildSpriteRenderers::Combine`` (`0x3edbab8`) | ``3EDC01C-3EDC024, 3EDC030-3EDC044, 3EDC048-3EDC054, 3EDC054-3EDC078, 3EDC078-3EDC084, 3EDC088-3EDC098, 3EDC09C-3EDC0A4, 3EDC0A8-3EDC0B4, 3EDC0B4-3EDC0C0, 3EDC0C0-3EDC0D0, 3EDC0D4-3EDC0DC, 3EDC0F4-3EDC100, 3EDC140-3EDC164, 3EDC168-3EDC174, 3EDC178-3EDC180, 3EDC188-3EDC194, 3EDC194-3EDC1A0, 3EDC1A4-3EDC1AC, 3EDC1AC-3EDC1C0, 3EDC1C8-3EDC1D4, 3EDC1D4-3EDC1E8, 3EDC1E8-3EDC1F8, 3EDC1F8-3EDC208, 3EDC208-3EDC218, 3EDC218-3EDC228, 3EDC440-3EDC448, 3EDC454-3EDC460, 3EDCDF4-3EDCDFC, 3EDCE08-3EDCE20, 3EDCF0C-3EDCF14, 3EDCF2C-3EDCF34, 3EDCF40-3EDCF44, 3EDCF44-3EDCF54, 3EDCF60-3EDCF68, 3EDCF70-3EDCF78, 3EDCF7C-3EDCF94, 3EDD424-3EDD498, 3EDD4C0-3EDD4C4, 3EDD4C4-3EDD4D4, 3EDD4F0-3EDD4F4, 3EDD4F4-3EDD504, 3EDD508-3EDD514, 3EDD51C-3EDD528, 3EDD534-3EDD53C, 3EDD54C-3EDD550, 3EDD550-3EDD560, 3EDD568-3EDD578, 3EDD57C-3EDD588, 3EDD58C-3EDD59C, 3EDD94C-3EDD950, 3EDD950-3EDD954, 3EDD954-3EDD958, 3EDD958-3EDD95C, 3EDD95C-3EDD960, 3EDD960-3EDD964, 3EDD964-3EDD968, 3EDD968-3EDD96C, 3EDD96C-3EDD970, 3EDD970-3EDD974, 3EDD974-3EDD978, 3EDD978-3EDD97C, 3EDD97C-3EDD980, 3EDD980-3EDD984, 3EDD984-3EDD988, 3EDD994-3EDD998, 3EDD998-3EDD99C, 3EDD99C-3EDD9A0, 3EDD9A0-3EDD9A4, 3EDD9A8-3EDD9AC, 3EDD9AC-3EDD9B0, 3EDD9B0-3EDD9B4, 3EDD9B4-3EDD9B8`` |
| ``EpiCoro.Background::CleanupAllMaterials`` (`0x3f3c1c0`) | ``3F3C4DC-3F3C4E4, 3F3C4F8-3F3C4FC, 3F3C4FC-3F3C50C, 3F3C51C-3F3C520, 3F3C520-3F3C528, 3F3C538-3F3C53C, 3F3C53C-3F3C544, 3F3C558-3F3C568, 3F3C570-3F3C580`` |
| ``EpiCoro.Internal.IAP.CurrencyPurchaseUIItem::UpdateUIData`` (`0x3e1a688`) | ``3E1A784-3E1A78C, 3E1A7E4-3E1A804, 3E1A834-3E1A838, 3E1A838-3E1A83C, 3E1A83C-3E1A840`` |
| ``EpiCoro.Internal.IAP.StoreController::OnPurchaseSuccess`` (`0x3e0c370`) | ``3E0C754-3E0C75C, 3E0C780-3E0C788, 3E0C79C-3E0C7A4, 3E0C888-3E0C88C, 3E0C8B4-3E0C8B8`` |
| ``MatchTelemetryTrackerController::OnTurnEnded`` (`0x3f0e638`) | ``3F0F000-3F0F008, 3F0F01C-3F0F020, 3F0F020-3F0F030, 3F0F04C-3F0F050, 3F0F050-3F0F060, 3F0FACC-3F0FAD0, 3F0FAD4-3F0FAD8`` |
| ``MatchTelemetryTrackerController::SnapshotAttackerHelperState`` (`0x3f0de74`) | ``3F0DFA4-3F0DFAC, 3F0DFC0-3F0DFC4, 3F0DFC4-3F0DFD4, 3F0DFEC-3F0DFF0, 3F0DFF0-3F0E000, 3F0E064-3F0E068, 3F0E070-3F0E074`` |
| ``MatchTelemetryTrackerController::SnapshotDefenderHealth`` (`0x3f0e0e4`) | ``3F0E44C-3F0E454, 3F0E468-3F0E46C, 3F0E46C-3F0E47C, 3F0E494-3F0E498, 3F0E498-3F0E4A8, 3F0E524-3F0E528, 3F0E53C-3F0E540`` |
| ``MonetizationEvents.MonetizationEventController::<ApplyNonAdultRewardSubstitution>g__SubstituteConfig\|29_0`` (`0x3de8de4`) | ``3DE8FCC-3DE8FD4, 3DE8FE0-3DE8FEC, 3DE9004-3DE900C, 3DE9064-3DE9068, 3DE90B8-3DE90C0, 3DE9100-3DE9108, 3DE9148-3DE9150, 3DE9160-3DE916C, 3DE917C-3DE9188, 3DE9198-3DE91A4, 3DE91F0-3DE9200, 3DE9218-3DE921C, 3DE9234-3DE9260, 3DE9278-3DE9280, 3DE9478-3DE947C, 3DE94D0-3DE94F0, 3DE95C0-3DE95C8, 3DE95C8-3DE95D0, 3DE95D0-3DE95D8, 3DE95D8-3DE95E4, 3DE95F0-3DE95F8, 3DE95F8-3DE9608, 3DE9028-3DE9030, 3DE929C-3DE92A4, 3DE92C0-3DE92CC, 3DE92E0-3DE92F0, 3DE9308-3DE935C, 3DE93A8-3DE93B4, 3DE9400-3DE940C, 3DE941C-3DE9424, 3DE9434-3DE943C, 3DE944C-3DE9458, 3DE94F4-3DE94FC, 3DE9500-3DE9504, 3DE9508-3DE9510, 3DE9514-3DE9518`` |
| ``ProfileInfoPanel::UpdatePlayerStats`` (`0x3cbe000`) | ``3CBE6C8-3CBE6D0, 3CBE6E4-3CBE6EC, 3CBE6F4-3CBE6FC, 3CBE708-3CBE710, 3CBE718-3CBE720, 3CBE72C-3CBE734, 3CBE73C-3CBE744, 3CBE958-3CBE95C`` |
| ``RadialCarveDebugger::RenderInGame`` (`0x3d1d274`) | ``3D1D9C0-3D1D9C8, 3D1D9D4-3D1D9E0, 3D1D9E8-3D1D9F4, 3D1D9FC-3D1DA04, 3D1DA04-3D1DA10, 3D1DA14-3D1DA28, 3D1DA28-3D1DA34, 3D1DA40-3D1DA48, 3D1DA70-3D1DA7C, 3D1DA88-3D1DA90, 3D1DAB4-3D1DAC0, 3D1DAC8-3D1DAD4, 3D1DAD8-3D1DB08, 3D1DB14-3D1DB20, 3D1DB48-3D1DB4C, 3D1DB50-3D1DB54, 3D1DB58-3D1DB5C, 3D1DB60-3D1DB64, 3D1DB68-3D1DB6C, 3D1DB70-3D1DB74, 3D1DB78-3D1DB7C`` |
| ``SDFSpriteGenerator_SR::RefreshPointsFromChildren`` (`0x3b8cfc0`) | ``3B8D670-3B8D678, 3B8D684-3B8D690, 3B8D694-3B8D6A8, 3B8D6F4-3B8D6FC, 3B8D880-3B8D884, 3B8D8B0-3B8D8B4, 3B8D7B0-3B8D7B8`` |
| ``UnitsPanel::UpdateCards`` (`0x3cca930`) | ``3CCB570-3CCB578, 3CCB584-3CCB590, 3CCB5D0-3CCB5D8, 3CCB5E4-3CCB5F0, 3CCB634-3CCB63C, 3CCB648-3CCB654, 3CCB738-3CCB73C, 3CCB73C-3CCB740, 3CCB740-3CCB744`` |
| ``Voodoo.Live.Analytics.FeatureTrackingRegistry::.ctor`` (`0x3aa31b8`) | ``3AA3CA0-3AA3CA8, 3AA3CB8-3AA3D40, 3AA3D70-3AA3D74`` |
| ``Voodoo.Live.Debugger.FeatureGroupDebugUI::DisplayMultipleOfferInfo`` (`0x3aacf50`) | ``3AAD250-3AAD258, 3AAD26C-3AAD278, 3AAD2C0-3AAD2F4, 3AAD30C-3AAD314, 3AAD348-3AAD34C, 3AAD34C-3AAD350`` |
| ``Voodoo.Live.Debugger.WheelOfferDebugUI::PopulateWheelValues`` (`0x3ab33b0`) | ``3AB3558-3AB3560, 3AB3578-3AB357C, 3AB3588-3AB3594, 3AB3598-3AB35B0, 3AB35E0-3AB35E4`` |
| ``Voodoo.Live.Offers.FeatureClient::ProcessPayload`` (`0x3a90cdc`) | ``3A9129C-3A912A4, 3A912B4-3A912B8, 3A912F0-3A91318, 3A9131C-3A91324, 3A91358-3A91364, 3A91368-3A91374, 3A9138C-3A91394, 3A91394-3A9139C, 3A913E0-3A913EC, 3A91424-3A91430, 3A91440-3A91448, 3A91448-3A91454, 3A9146C-3A91478, 3A91480-3A91488, 3A914C0-3A914CC, 3A91500-3A9150C, 3A91524-3A91530, 3A91538-3A91540, 3A91544-3A9154C, 3A91584-3A91590, 3A91594-3A915A0, 3A915B8-3A915C0, 3A915F4-3A91620, 3A9163C-3A91668, 3A91668-3A91674, 3A9168C-3A91698, 3A916A0-3A916A8, 3A916E0-3A91710, 3A91750-3A91774, 3A91774-3A91780, 3A917DC-3A917E0, 3A917E0-3A917E4, 3A917E4-3A917E8, 3A917EC-3A917F0, 3A917F0-3A917F4, 3A917F4-3A917F8, 3A917F8-3A917FC, 3A917FC-3A91800, 3A91800-3A91804, 3A91804-3A91808`` |
| ``Voodoo.Live.Offers.FeatureGroup::Dispose`` (`0x3a8e268`) | ``3A8E348-3A8E350, 3A8E368-3A8E36C`` |
| ``Voodoo.Sauce.Debugger.EventConsoleInformationScreen::UpdateEventInformationBody`` (`0x3acb254`) | ``3ACB3C8-3ACB3D0, 3ACB410-3ACB420, 3ACB420-3ACB43C, 3ACB43C-3ACB454, 3ACB464-3ACB46C, 3ACB484-3ACB48C, 3ACB490-3ACB49C, 3ACB4A4-3ACB4B0, 3ACB500-3ACB504, 3ACB518-3ACB534, 3ACB5A4-3ACB5A8, 3ACB5A8-3ACB5AC, 3ACB5AC-3ACB5B0, 3ACB5B8-3ACB5BC, 3ACB5BC-3ACB5C0, 3ACB5C0-3ACB5C4, 3ACB5C4-3ACB5C8, 3ACB5CC-3ACB5D0, 3ACB4CC-3ACB4D4, 3ACB4E4-3ACB4EC, 3ACB53C-3ACB540`` |
| ``Voodoo.Sauce.Debugger.LogConsoleDebugScreen::ClearExceptionsList`` (`0x3ad0838`) | ``3AD0B48-3AD0B50, 3AD0B58-3AD0B64`` |
| ``Voodoo.Sauce.Debugger.PrivacyDebugScreen::OnEnable`` (`0x3ad31f4`) | ``3AD3854-3AD385C, 3AD3868-3AD3888, 3AD3888-3AD389C, 3AD3924-3AD3928`` |
| ``Voodoo.Sauce.Internal.Analytics.AmplitudeAdEventsHandler::OnImpressionTracked`` (`0x39b9e80`) | ``39BA590-39BA598, 39BA5A4-39BA5AC`` |
| ``Voodoo.Sauce.Internal.Analytics.AmplitudeGameEventsHandler::OnGameFinished`` (`0x39bdf18`) | ``39BE5F4-39BE5FC, 39BE608-39BE610`` |
| ``Voodoo.Sauce.Internal.LoggerSettingsManager::ToggleCategoryForModuleCode`` (`0x3b19968`) | ``3B19A6C-3B19A74, 3B19B04-3B19B08`` |
| ``Voodoo.Sauce.Internal.Utils.UnityThreadExecutor::Update`` (`0x39ac004`) | ``39AC210-39AC218, 39AC230-39AC234, 39AC25C-39AC260`` |
| ``WorldSpaceUI::UpdateProjectileIndicators`` (`0x3dbd9b0`) | ``3DBDD04-3DBDD0C, 3DBDD20-3DBDD24, 3DBDD24-3DBDD34, 3DBDD40-3DBDD4C, 3DBDD50-3DBDD5C, 3DBDD60-3DBDD68, 3DBDD6C-3DBDD78, 3DBDDBC-3DBDDC8, 3DBDDD0-3DBDDD8, 3DBDDE4-3DBDDEC, 3DBDDF0-3DBDDFC, 3DBDE0C-3DBDE10, 3DBDE10-3DBDE20, 3DBDE28-3DBDE34, 3DBDE4C-3DBDE54, 3DBDE54-3DBDE60, 3DBDE70-3DBDE7C, 3DBDEA4-3DBDEB0, 3DBDEB0-3DBDEC0, 3DBDEC0-3DBDECC, 3DBDEDC-3DBDEE8, 3DBDF0C-3DBDF20, 3DBDF2C-3DBDF34, 3DBDF40-3DBDFB0, 3DBE018-3DBE024, 3DBE040-3DBE054, 3DBE064-3DBE070, 3DBE074-3DBE07C, 3DBE084-3DBE090, 3DBE094-3DBE0A0, 3DBE0A4-3DBE0B0, 3DBE0D4-3DBE0E4, 3DBE0E8-3DBE0F4, 3DBE0F4-3DBE10C, 3DBE10C-3DBE124, 3DBE128-3DBE130, 3DBE148-3DBE16C, 3DBE178-3DBE180, 3DBE190-3DBE194, 3DBE194-3DBE1A4, 3DBE1B4-3DBE1D8, 3DBE284-3DBE290, 3DBE29C-3DBE2C0, 3DBE45C-3DBE464, 3DBE478-3DBE47C, 3DBE4D0-3DBE4D4, 3DBE4D4-3DBE4D8, 3DBE4D8-3DBE4DC, 3DBE4DC-3DBE4E0, 3DBE4E0-3DBE4E4, 3DBE4EC-3DBE4F0, 3DBE4F0-3DBE4F4, 3DBE4F4-3DBE4F8, 3DBE4F8-3DBE4FC, 3DBE4FC-3DBE500, 3DBE500-3DBE504, 3DBE504-3DBE508, 3DBE508-3DBE50C, 3DBE50C-3DBE510, 3DBE510-3DBE514, 3DBE514-3DBE518, 3DBE358-3DBE360, 3DBE374-3DBE378, 3DBE378-3DBE384, 3DBE390-3DBE39C, 3DBE3A0-3DBE3AC, 3DBE3E8-3DBE40C, 3DBE4C4-3DBE4C8, 3DBE4CC-3DBE4D0`` |

</details>

### Verification commands and results

- `NUGET_PACKAGES=/private/tmp/astra204-nuget dotnet build Cpp2IL/Cpp2IL.csproj -c Release --no-restore -f net10.0`: **0 errors**.
- `NUGET_PACKAGES=/private/tmp/astra204-nuget dotnet test --no-restore --project Cpp2IL.Core.Tests`: **1310/1310**; pre-increment merge run **1307/1307**.
- `dotnet test --no-restore --project Cpp2IL.Core.Tests -- --filter 'FullyQualifiedName~ExceptionRegionRecoveryTests'`: **66/66**.
- `dotnet test --no-restore --project LibCpp2ILTests`: **12/12**.
- `dotnet test --no-restore --project Cpp2IL.JitOracle.Tests`: **9/9**.
- `/Users/dankondr/castle-evidence/r241/run-cpp2il.sh ROOT OUT`: both final control/branch runs **69982/69982**.
- `diag_families.py OUT --dispositions ... --count 'Exception landing pad at'`, and the same command with `--assemblies CastleClashers.Game`: **8996 / 5831 pads**.
- `recovery-audit.dll scan audit-astra206-r13-{control,final}.json audit_astra206-r13-{control,final}`: **0 ILVerify transitions**; exit 1 is the unchanged Bootstrap reachability gate.
- `git diff --check`: passed.

All evidence logs and corpora remain outside the repository. Earlier sections
retain their historical controls and measurements.

## Round 6: original reference parameters and call storage (2026-10-01)

**Draft: 9,465 owned pad warnings remain; target ≤7,768.** This increment
removes nine pads on the control merge described below.
The total reduction from 15,537 is 6,072 (39.1%); another 1,697 are required.

### Proof and control

`CatchArgument` may use an existing reference parameter only when the reaching
native value is that exact parameter's entry-register root. Register copies and
saved frame cells retain the identity; joins retain it only when all inputs agree.
Pointer, byref, generic and hidden MethodInfo parameters remain excluded. No
parameter is selected by its type alone.

An arbitrary call can mutate heap memory through aliases or static state.
The shared call-storage invalidation now discards stored heap values on normal
and exceptional edges and between handler calls. Previously, a handler could
reload a heap cell after a call and return its old stored constant. Class
initializers use the same invalidation, including the memory intersection at
conditional initializer joins. Tracked frame cells still use the existing
address and width checks.

Control: local merge `24ca861d00b944af9b5c74023eefda78871f1c2e`, formed from
prior EH commit `f30aa8fef8ff82abdb24e177aa10a0bf28711391` and development
`40fd405c8a5661af3b158dbe5bf651829ea621c1` (#190, #192, #183).
Branch merge: `a1b8da64f5a5cfcd1dc98510f4d608b569307d12`.
Control sweep: `astra206-r11-fresh-control`; branch sweep:
`astra206-r11-fresh-branch`, frozen executable `astra206-r11-fresh-branch-bin`.
Each completed 69,982/69,982 native methods, 183 assemblies, 178,274 reported
methods. The same development is included on both sides. The earlier paired sweep on
the #189 base (`astra206-r10-branch` / `astra206-r11-final2`) also removes nine
owned pads with no added diagnostic or ILVerify transition. #181 remains open.

### Measurements

| Scope | Diagnosed control → branch | Newly clean | Regressions | Pads control → branch |
|---|---:|---:|---:|---:|
| All | 15,958 → 15,958 | 0 | 0 | 41,689 → 41,608 |
| Game-owned | 3,818 → 3,818 | 0 | 0 | 9,474 → 9,465 |
| CastleClashers.Game | 2,315 → 2,315 | 0 | 0 | 6,113 → 6,113 |
| Castle-building owners + nested types | 80 → 80 | 0 | 0 | 684 → 684 |

No newly clean method, added diagnostic, or clean regression. ILVerify:
**0 status transitions, 0 valid→invalid**; both runs have 170,144 valid,
416 invalid, and 7,714 partial methods. The Bootstrap reachability gate remains
blocked at 29/29. Both required `diag_families.py` scopes were run.

| Changed owned method | Pads control → branch |
|---|---:|
| ``System.Void NativeWebView::OpenAndroid(System.String)`` | 15 → 13 |
| ``System.Void Audiomob.Unmanaged.AudiomobPluginInitialization::DoInitialization(System.Action`1<System.Boolean>)`` | 16 → 9 |

### Native and IL review

`NativeWebView.OpenAndroid`: entry `3955A98` saves original X0 (`url`) in X19.
The catch calls the actual exception message getter, concatenates the error text,
runs Debug/Application class initialization, and logs the error. At `3955F90`
X0 is restored from X19; `3955F98` calls OpenURL. The emitted handler uses
`ldarg url; call Application.OpenURL`, then leaves to the native merge.
Thirteen auxiliary pad warnings remain.

`AudiomobPluginInitialization.DoInitialization`: `3973450` saves the callback
in X19 at entry. The catch restores it to X0 at `39737FC`, restores the native frame,
sets X1 to zero at `3973808`, and calls `InvokeInitCallback` at `3973814`.
Its IL uses `ldarg callback; ldc.i4.0; call InvokeInitCallback`, then leaves
to the normal return. Nine auxiliary pad warnings remain.

The newly emitted methods were reviewed against native disassembly. Neither
method becomes clean because its other unresolved code remains diagnosed.

### Development merge impact

Compared with the prior #189 control, the new development makes 54 methods clean
(11 owned; three in the castle-building owners). These changes are present in
both fresh sweeps; their pad counts remain unchanged. The three newly clean
castle methods are MirrorGridHorizontally, ToObscured, and ToPlain.
No previously clean method regresses. Eleven already diagnosed methods gain
at least one diagnostic, including these three owned methods:

| Method | Added diagnostic from development |
|---|---|
| ChestController.OpenChests | ChestType cannot convert to the ValueTuple slot |
| MatchMakingController.StartMatchmaking | Packed ValueTuple operands remain unresolved in Subtract/Add |
| ChestController.<>c.<OpenChests>b__33_0 | Int32 receiver is unavailable for a projected field |

The added diagnostics reproduce in the fresh control. They are in the reserved
normal array/packed-value recovery lane; this EH increment adds none.

### Tests

The CLR return fixture now has two reference parameters of the same type and
checks that the catch returns the second original value, while the normal path
returns its own string. Its unknown-register variant remains refused. Against
unchanged control code, the positive parameter case fails and the negative
case passes.

A heap-store/reload negative case fails before invalidation: a protected call
may change the stored value, but the old proof emits `Return 7`. With the fix,
the proof refuses that stale value and retains the pad warning.
The focused EH run passed 63/63 cases. Full Core passed before the development
merge; after it, EH + packed fields + multidimensional arrays passed 85/85.
The full-suite counts below precede that merge.
**Core: 1265/1265.**
**LibCpp2IL: 12/12.**
**JitOracle: 9/9.**

### Gaps

Fresh native proof coverage is **7,084 finally + 1,306 catch = 8,390 pads**.
No existing native proof disappears; exactly nine new pads are proven and
materialized. **2,318 proven pads in 118 methods remain unmaterialized**,
with the same pad set as Round 5. Its emission refusal counts still apply:
1,051 unusable/different cleanup IL; 812 no reachable emitted protected unit;
274 unsafe region crossings; 169 unassigned cleanup locals; eight incomplete
shared-pad coverage; four unavailable catch merges/seeds/handlers.

The state-machine cohort remains **133 methods / 3,162 pads**. The earlier
per-pad first-failure classification remains the investigation map; no new
state-machine proof was accepted in this increment.

`Bootstrap.<InitializeVoodooLive>.MoveNext` still reaches native builder target
`398913C` with null MethodInfo. That target is absent from the managed address
map and is a complex body, not a forwarding thunk. The metadata-backed
AsyncUniTaskVoidMethodBuilder.SetException body at `6F03E38` has different
instructions and layout. Similar behavior does not establish managed identity;
a SetException signature was not assigned to the unknown target.

A separate helper-contract experiment found eight additional native finally
pads in CrashReportManager.SelectCrashReporter. It remains outside production
pending contract-specific negative tests and a full emission measurement.
Fresh reference-field loads alone produced no additional native proofs in the
same 1,019-method cohort. Reserved normal receiver/frame passes remain untouched.

### Castle-building scope

| Method | Pads control → branch |
|---|---:|
| ``System.Void CastleBuildingController::ShowUpgradeAdditions()`` | 35 → 35 |
| ``System.Void CastleBuildingController::TriggerInterior()`` | 35 → 35 |
| ``System.Void CastleBuildingController::RelocateUnitsToValidPositions()`` | 41 → 41 |
| ``System.Nullable`1<UnityEngine.Vector2Int> CastleMaker::PickBestAvailablePosition(System.Collections.Generic.List`1<UnityEngine.Vector2Int>, System.Collections.Generic.HashSet`1<UnityEngine.Vector2Int>, CastleClashers.HumanLikeBots.BotTier, System.Boolean)`` | 12 → 12 |
| ``System.Void CastleMaker::Build(System.Boolean, System.Boolean, System.Boolean)`` | 43 → 43 |
| ``System.Void CastleMaker::SpawnShields(System.Boolean)`` | 224 → 224 |
| ``System.Void CastleMaker::SpawnShieldsFromPlacements(System.Collections.Generic.List`1<EnemyShieldPlacement>)`` | 217 → 217 |
| ``System.Void CastleMaker::SaveShieldsData()`` | 47 → 47 |
| ``System.Void CastleMaker::SetShieldTypeForGridPos(UnityEngine.Vector2Int, System.Int32)`` | 14 → 14 |
| ``System.Void CastleMaker::MarkCastleShieldPositionsInUpgradeData()`` | 7 → 7 |
| ``UnityEngine.GameObject[0..., 0...] CastleMaker::BuildGridAuto(System.Collections.Generic.List`1<UnityEngine.Transform>, System.Boolean, System.Single)`` | 9 → 9 |

Earlier sections retain their historical controls and measurements.

## Round 5: catch value returns (2026-10-01)

**Draft: 9,474 owned pad warnings remain; the target is at most 7,768.**
This increment removes 90 owned pads. Against the original 15,537, the total
reduction is 6,063 (39.0%); 1,706 more must be removed.
Earlier sections retain their historical controls and counts.

### Control and proof

Control: `a87c8ff03fa5db47d94d9ec33b4c1054fbd8977a`, the existing PR after
merging development through #187, #188, and #189
(`8bc9beb81d0a4c79e68a20353695fe87a827006b`). #181 remains open.
Full sweeps: `astra206-r10-control` and `astra206-r10-branch`;
69,982/69,982 native methods, 183 assemblies, 178,274 reported methods each.

A non-void catch may now reach a separately proven value return. The proof walks
only register moves, stack restoration, and single-successor jumps to the native
return. It resolves the operand from an actual handler result, the caught object,
a metadata string literal, or an immediate. Primitive returns are restricted to
Int32 and canonical Boolean constants. References must have an assignable base
type, or be null. Pointer, byref, generic, unknown-value, and effectful epilogues
remain refused. Every original wrapper/type/mismatch proof remains required.

The catch leaves to its own return continuation outside EH. Normal paths retain
their own SSA return value. Return operands participate in proof grouping, so
handlers with different values do not share a continuation.

Generated EH locals are now marked as such. The parameter fallback previously
mistook an out-of-CFG catch result for the method's sole parameter of the same
type. The marker prevents that substitution for both the caught object and
handler results. It leaves ordinary local/parameter recovery unchanged.

### Measurements

| Scope | Diagnosed control → branch | Newly clean | Regressions | Pads control → branch |
|---|---:|---:|---:|---:|
| All | 16,012 → 16,012 | 0 | 0 | 41,921 → 41,689 |
| Game-owned | 3,829 → 3,829 | 0 | 0 | 9,564 → 9,474 |
| CastleClashers.Game | 2,326 → 2,326 | 0 | 0 | 6,154 → 6,113 |
| Castle-building owners + nested types | 83 → 83 | 0 | 0 | 684 → 684 |

No method gains a diagnostic. Newly clean methods: none.

ILVerify: **0 status transitions; 0 valid→invalid**. Both runs have 170,144 valid / 416 invalid / 7,714 partial methods. The Bootstrap reachability gate remains blocked at 29/29.

| Method | Pads control → branch |
|---|---:|
| ``System.Collections.Generic.Dictionary`2<System.String, System.Object> MatchTelemetryTrackerController::BuildBotWheelPayload()`` | 19 → 2 |
| ``System.String SaveController::GetFileAsJson(System.String)`` | 6 → 2 |
| ``System.String SaveController::GetFileAsJsonFromPath(System.String)`` | 6 → 2 |
| ``System.Int32 HapticNative::GetMotorType()`` | 15 → 13 |
| ``System.Int32[0..., 0...] CastleClashers.HumanLikeBots.PlayerProfileFetcher::ParseCastleGrid(System.Object)`` | 16 → 2 |
| ``System.Boolean PaperPlaneTools.RateBox::SaveStatistics()`` | 11 → 2 |
| ``System.Int32 Voodoo.ADN.Internal.AdnSignalsHelper::GetAdsCount(System.String)`` | 3 → 2 |
| ``System.String Voodoo.ADN.Internal.AdnSignalsHelper::GetAndUpdateSessionDate(System.String, System.String)`` | 4 → 2 |
| ``UnityEngine.AndroidJavaClass Voodoo.ADN.Internal.AdnSdkAndroid::PluginClassInstance()`` | 3 → 2 |
| ``Voodoo.ADN.Internal.AdnSdkAndroid+BackgroundEventCallbackProxy Voodoo.ADN.Internal.AdnSdkAndroid::EventCallbackInstance()`` | 3 → 2 |
| ``System.String Voodoo.Live.ConfigLoader::GetRequestError(UnityEngine.Networking.UnityWebRequest, System.Double)`` | 21 → 2 |
| ``System.Boolean Voodoo.Live.Sample.RotationOperator::CastFields(System.Object[], Voodoo.Live.IBlackboard)`` | 5 → 2 |
| ``System.Boolean Voodoo.Live.Sample.Offers.VoodooLiveBridge::ApplyItemDelta(System.String, System.Int32)`` | 5 → 2 |
| ``Voodoo.Live.IPrice Voodoo.Live.Offers.ServerSpin::GetRerollPrice()`` | 3 → 2 |
| ``System.Boolean TrustedTimeService::TryParseJsonEpoch(System.String, System.Int64&)`` | 11 → 2 |

### Native and IL review

`TrustedTimeService.TryParseJsonEpoch`: after ending the native catch at
`3F32CD8`, the pad sets X0 to zero, restores the private exception-stack index,
and jumps through register restoration to `3F32C60: Return X0`. The generated
Object catch stores the supplied exception and leaves to `ldc.i4.0; ret`.
The normal success/failure return still loads its original Boolean SSA local.
Nine primary pad warnings disappear; the two auxiliary pads remain.

`SaveController.GetFileAsJson`: the handler calls the caught exception's virtual
`get_Message`, concatenates a metadata literal, initializes Debug, and calls
`LogError`. Its native exit reaches `3F277A8: X0 = 0`, then returns at `3F277B4`.
The IL loads the actual message and concatenation locals, then leaves to a separate
`ldnull; ret`. The normal decoded string has a separate exit. The original emitted
handler incorrectly loaded `fileName` for both message and concatenation results;
the EH-local marker corrects those reads.

### Tests and remaining work

The regression fixture executes Int32, Boolean, string, and original-object
returns through real CLR catches and checks the normal path separately. It also
refuses an unknown return register, an effectful epilogue, pointer and byref
returns. The string case has a parameter of the same type as the handler result;
it fails before the EH-local marker and returns the actual handler result after it.
Six portable cases against unchanged control code: four positive failures and
two negative passes. The return-local collision separately fails before its fix.
Tests: **Core 1,260/1,260**, then **74/74** for EH, aggregate lanes and
parameter-local recovery after merging #189. The full Core build preceded that
merge; the final focused run includes its new whole-result store case.
**LibCpp2IL 12/12; JitOracle 9/9**. The final focused run includes all 60 EH cases.

The state-machine cohort remains 133 methods / 3,162 pads. Its earlier first-failure
counts remain applicable: this change proves no new state-machine handler.
Catch returns do not make an unknown builder signature, captured heap value,
state-guarded cleanup, or uncovered normal call safe.

Two separate experiments remain outside production: filtering unused ABI argument
registers produces zero extra proofs across 1,019 methods; preserving original
reference parameters produces nine native proofs in `NativeWebView.OpenAndroid`
and `AudiomobPluginInitialization.DoInitialization`. The latter still needs
synthetic tests, CLR emission review, and a full measurement before adoption.

The reserved normal cleanup-receiver failures remain listed below, including
`StoreController.OpenSection` and the shield-building methods. No repair of their
normal emission was added here.

Native proofs cover 8,381 pads in the original owned cohort.
**2,318 proven pads remain unmaterialized in 118 methods.**
The fixed 132-method class-test cohort is now 835 pads (925 on control).
The refusal categories from Round 4 still apply; this return extension changes
neither the remaining native state shapes nor the normal cleanup emitters.

### Castle-building scope

| Method | Pads control → branch |
|---|---:|
| ``System.Void CastleBuildingController::ShowUpgradeAdditions()`` | 35 → 35 |
| ``System.Void CastleBuildingController::TriggerInterior()`` | 35 → 35 |
| ``System.Void CastleBuildingController::RelocateUnitsToValidPositions()`` | 41 → 41 |
| ``System.Nullable`1<UnityEngine.Vector2Int> CastleMaker::PickBestAvailablePosition(System.Collections.Generic.List`1<UnityEngine.Vector2Int>, System.Collections.Generic.HashSet`1<UnityEngine.Vector2Int>, CastleClashers.HumanLikeBots.BotTier, System.Boolean)`` | 12 → 12 |
| ``System.Void CastleMaker::Build(System.Boolean, System.Boolean, System.Boolean)`` | 43 → 43 |
| ``System.Void CastleMaker::SpawnShields(System.Boolean)`` | 224 → 224 |
| ``System.Void CastleMaker::SpawnShieldsFromPlacements(System.Collections.Generic.List`1<EnemyShieldPlacement>)`` | 217 → 217 |
| ``System.Void CastleMaker::SaveShieldsData()`` | 47 → 47 |
| ``System.Void CastleMaker::SetShieldTypeForGridPos(UnityEngine.Vector2Int, System.Int32)`` | 14 → 14 |
| ``System.Void CastleMaker::MarkCastleShieldPositionsInUpgradeData()`` | 7 → 7 |
| ``UnityEngine.GameObject[0..., 0...] CastleMaker::BuildGridAuto(System.Collections.Generic.List`1<UnityEngine.Transform>, System.Boolean, System.Single)`` | 9 → 9 |

Reproduction uses the original brief commands with the two frozen output roots above.

Task: dankondr/castle-recovery#206. Continues slice 1 and addresses dankondr/Cpp2IL#80.

## Round 4: catch-all through the defaults class (2026-10-01)

**Draft: 9,564 owned pad warnings remain; the target is at most 7,768.**
This round removes 61 owned pads, with no new diagnostics or ILVerify transitions.
The reduction against the original 15,537-pad denominator is **5,973 (38.4%)**;
another **1,796** pads must be removed. No further safe change was identified in
this EH lane after examining the remaining native and emission failures below.
Earlier sections are historical measurements on their stated controls.

### Control and implementation

Control: `e36d1cdb677f08499b85288fec6b70f0cd2f603c`, the existing slice-2b
implementation after merging development through #184 and #186
(`b12ad62fbd39226378789715068b5d569dc3af53`). This control isolates round 4;
it already includes the earlier changes in this PR. #181 was still open at the
final dependency check and is not included. The branch was merged, not rebased.

`NativeExceptionRegionProof` now resolves the pad's symbolic defaults-table load
through the existing `Unity6PrimitiveDefaultsClass` map. It uses the same Unity 6
and absolute-pointer-load prerequisite as `SeedIl2CppDefaultsClassTypes`; register
copies retain the expression and joins retain it only when all incoming states
agree. Only a defaults-proven Object class enables `catch System.Object`.
The mismatch must still unwind the original exception; the accepted handler must
end its native catch and reach a proven void epilogue. There is no new offset map,
seeding rule, game-specific address, or change to warning text.

Full control and branch sweeps: `astra206-r8-control` and `astra206-r8-object`,
69,982 native methods, 183 assemblies, 178,274 reported methods each.
The fresh control has 9,625 owned pads, versus the historical round-3 count of
9,623; the comparison below includes the intervening development changes on both
sides instead of attributing their effects to this round.

### Results

| Scope | Methods | Diagnosed control → branch | Newly clean | Clean regressions | Pads control → branch |
|---|---:|---:|---:|---:|---:|
| All | 178,274 | 16,265 → 16,265 | 0 | 0 | 42,024 → 41,921 |
| Game-owned | 25,348 | 3,991 → 3,991 | 0 | 0 | 9,625 → 9,564 |
| CastleClashers.Game | 14,423 | 2,482 → 2,482 | 0 | 0 | 6,215 → 6,154 |
| Castle-building owners + nested types | 280 | 93 → 93 | 0 | 0 | 684 → 684 |

The newly clean list is empty in every scope. No method gains any diagnostic.
There are 548 owned methods with pads in both runs. The two improved owned methods
retain two auxiliary pad warnings each; the other 42 removed pads are outside the
owned scope.

ILVerify is identical in both runs: **170,144 valid / 416 invalid / 7,714 partial**.
There are **0 status transitions**, including **0 valid→invalid**. The separate
Bootstrap reachability gate is still 29/29 blocked; its nonzero audit exit is not
a passed gate.

Tests: **Core 1,244/1,244; LibCpp2IL 12/12; JitOracle 9/9**. The seven new synthetic
cases pass on the branch. Against the unchanged control production code, including
#186, three positive cases fail and four negative cases pass. Positive cases cover
a direct load, a register copy, and an equal-value branch join. Negative cases cover
a divergent join, an unknown base, another defaults class, and a mismatch that
returns instead of unwinding. The positive cases execute emitted CLR IL and catch
a thrown non-Exception Object.

### Class-test cohort and native/IL review

The defaults Object comparison is proven in **23 owned methods**. Of these,
**19 belong to the fixed 132-method class-test cohort**; the other four had been
classified under compound/state-machine shapes: `BuildDefenderUnitsWithDamage`,
`TrackKilledUnits`, `PvpRelayTransport.<CloseAsync>.MoveNext`, and
`Voodoo.Live.FileIO.<Save>.MoveNext`. Thus the historical phrase “23 of 132” mixes
shape cohorts. The same expressions flow through copies and equal-value joins;
there is no additional completed handler from those paths in this binary.

Full handlers are newly proven and materialized in **2/132 methods**, covering
61 pads. The fixed class-test cohort changes **986 → 925 pads** on this control;
its 19 Object-test methods change **243 → 182**. Proving the class alone does not
prove the rest of a handler.

| Method | Pads control → branch | Native proof and emitted IL |
|---|---:|---|
| `AnalyticsController.AddSessionContextToDict` | 29 → 2 | At `3EEC804..3EEC814`, load the defaults pointer, load `object_class` at +0x10, and compare it with the unwrapped exception's class. The match only updates the private exception stack, calls `__cxa_end_catch`, and jumps to the void epilogue. The mismatch rethrows the original exception. One Object catch is emitted at `IL_0476`, storing the exception then leaving to `IL_0480: ret`. |
| `MatchTelemetryTrackerController.AddUnitGridPosition` | 36 → 2 | The same sequence is at `3F116B8..3F116C8`; the match ends the catch at `3F116E8` and joins the existing return, and the mismatch rethrows the original exception. Seventeen disjoint Object clauses preserve the uncovered normal calls; each stores the caught object and leaves to the same return. |

The native selector, LSDA ranges, class-test arguments, mismatch path, stack-only
bookkeeping and return were checked for both methods against the retained native
ISIL, and their serialized IL clauses were read. These checks cover the EH change;
normal-body diagnostics and the two remaining auxiliary pads are still visible.

### Gaps: state machines

The fixed cohort remains **133 methods / 3,162 pads**. Its existing typed-catch
proofs still cover 811 native pads in 50 methods. Per-pad classification below uses
the first failed native catch proof at that pad, with the remaining pads checked
against normal-path seeds and the finally walker. Pads occur once in this table;
methods can occur in several rows.

| Failing proof step | Remaining pads | Affected methods |
|---|---:|---:|
| Unknown frame-index store or unsupported scaffolding after the type test | 973 | 48 |
| No normal-path seed for an auxiliary handler | 680 | 133 |
| Iterator cleanup/state-effect proof | 336 | 8 |
| Captured call argument has no managed SSA value | 311 | 27 |
| Managed handler callee is unresolved | 287 | 44 |
| Call reached before an accepted catch-type test | 199 | 13 |
| No accepted selector/site for a standalone region | 134 | 133 |
| Mismatch does not prove unwinding | 92 | 3 |
| Handler does not prove a void epilogue | 71 | 6 |
| Branch inside the handler | 38 | 4 |
| Branch before the catch-type proof | 37 | 1 |
| Native catch proven; emitted merge/seed unavailable | 4 | 2 |

The 336-pad iterator group contains `GrantQueuedTokenRewardsAfterProgress`,
`ScrollToCoroutine`, `ShowRewardsOneByOne` in NewUtilityPanel and
NewProfileCosmeticPanel, `ShowDecorations`, `GetActivePreviewAgents`,
`GrantRewardWithDelay`, and `Co_FetchFromUrl`. Native closure walks reach writes to
iterator state (`[this+0x10]`); some first reach an unsupported negated state-guard
constant. There is no proved matching sequence of normal cleanup effects across
those guards. Treating these fault-like paths as unconditional finally bodies
would change when they run.

The largest async failures remain the unknown exception-stack index after an
addressed call, cached owner fields without an existing managed local, and
specialized builder targets with no unique managed method/MethodInfo. For example,
`Bootstrap.<InitializeVoodooLive>.MoveNext` reaches builder target `398913C` with
null MethodInfo, and `Bootstrap.<StartNakamaLoginFlow>.MoveNext` loses the saved
exception-stack index. A fresh field load or a guessed SetException signature
would not prove the native value. The prior write-barrier/alias experiment did
not remove owned pads and was not added to this round.

### Gaps: proven but not materialized

Native proofs cover **7,084 finally + 1,207 catch = 8,291 distinct pads**.
**2,318** of these still have warnings after emission, across **118 methods**.
This is the fresh measurement after the base merge; the earlier 2,316 count was
on the round-3 base. The Object change materializes all 61 of its new owned proofs.
The table assigns each remaining proven pad to its first applicable candidate
refusal; method counts overlap.

| Emission refusal | Remaining proven pads | Affected methods |
|---|---:|---:|
| Cleanup IL is unusable or differs between normal copies | 1,051 | 25 |
| No reachable emitted protected instruction | 812 | 62 |
| Region crosses a return, live entry, or uncovered call | 274 | 18 |
| Cleanup local is not assigned at try entry | 169 | 15 |
| Final shared-pad coverage remains incomplete | 8 | 5 |
| Catch merge/seed/handler is unavailable | 4 | 2 |

The top two refusals were inspected in the emitted IL, but cannot be lifted by
relaxing the EH checks:

- `CastleMaker.SpawnShields`, `SpawnShieldsFromPlacements`, and
  `StoreController.OpenSection` have `Dispose` receivers reconstructed as an
  enumerator's `_list` or `_index` field. Emission diagnoses the missing enumerator
  and substitutes a zero-initialized receiver. Moving this code into a finally
  would preserve a known wrong cleanup. Receiver/frame recovery belongs to the
  reserved normal-dataflow lane.
- `CastleMaker.Build` has 43 pads whose native cleanup is proven, but no reachable
  emitted protected seed. A clause needs an actual emitted body; fabricating one
  would not recover the missing normal code.
- `BotEmoteController.SetBotEmotes` illustrates the local-assignment refusal:
  protected `MoveNext` uses assigned locals V_77 or V_67, while the normal Dispose
  copy uses V_27, which is not assigned at those entries. Those SSA values need
  reconciliation before a cleanup can be reused.
- `CastleBuildingController.RelocateUnitsToValidPositions` and
  `ShowUpgradeAdditions` cross normal enumerator calls that are outside the
  candidate's proven native ranges. Expanding the try would protect uncovered
  calls. The existing disjoint catch fallback is not a finally solution: executing
  a finally at each successful unit would run cleanup too early.
- Eight pads in four PlayerProfileFetcher parsers and
  `ConsentWrapperAndroid.Initialize` still fail final shared-pad coverage. Their
  native proofs are present at emission; partial region coverage does not justify
  removing their warnings.

No additional defaults-table offset is requested by this round's failures.
Filters and undecoded action chains remain zero in the inspected 1,019-method
owned cohort; state-dependent fault-like handlers remain outside this proof.
No reserved pass or block-operation emission was modified.

### Castle-building scope

All 11 methods that carried pads in the control still carry the same pads.
`TimedCastleBuildingController` and `EngineersController` add no pad-bearing method.

| Method | Pads control → branch |
|---|---:|
| `CastleBuildingController.ShowUpgradeAdditions` | 35 → 35 |
| `CastleBuildingController.TriggerInterior` | 35 → 35 |
| `CastleBuildingController.RelocateUnitsToValidPositions` | 41 → 41 |
| `CastleMaker.PickBestAvailablePosition` | 12 → 12 |
| `CastleMaker.Build` | 43 → 43 |
| `CastleMaker.SpawnShields` | 224 → 224 |
| `CastleMaker.SpawnShieldsFromPlacements` | 217 → 217 |
| `CastleMaker.SaveShieldsData` | 47 → 47 |
| `CastleMaker.SetShieldTypeForGridPos` | 14 → 14 |
| `CastleMaker.MarkCastleShieldPositionsInUpgradeData` | 7 → 7 |
| `CastleMaker.BuildGridAuto` | 9 → 9 |

### Reproduction

With `NUGET_PACKAGES=/private/tmp/astra204-nuget`, build the control commit and the
branch separately, including the pinned Disarm submodule, then run:

```sh
dotnet build Cpp2IL/Cpp2IL.csproj -c Release -f net10.0
dotnet test --project Cpp2IL.Core.Tests
dotnet test --project LibCpp2ILTests
dotnet test --project Cpp2IL.JitOracle.Tests
~/castle-evidence/r241/run-cpp2il.sh CONTROL_ROOT /private/tmp/astra206-r8-control
~/castle-evidence/r241/run-cpp2il.sh BRANCH_ROOT /private/tmp/astra206-r8-object
```

Both outputs were scanned with the r241 recovery-audit template, substituting the
respective output path. Temporary native/IL refusal instrumentation was used only
in a separate source copy; it is not part of this PR.

### Diagnostic-family output

#### Control: all game-owned

```text
scope: Assembly-CSharp, CastleClashers.Core, CastleClashers.Game, CastleClashers.Internal.Services, CastleClashers.Internal.UI, CastleClashers.Rules, CastleClashers.Rules.Client, CastleClashers.SDKGlue, CastleClashers.VoodooTune, Ranked
game-owned methods with diagnostics: 3991
methods naming a canonical shared-generic type: 173

| family | methods | sole | occurrences |
|---|---:|---:|---:|
| type: no legal conversion | 1614 | 607 | 6409 |
| memory: unmanaged load | 1229 | 320 | 6243 |
| other | 987 | 257 | 10673 |
| dataflow: undefined local | 976 | 176 | 2459 |
| type: synthetic default in operand slot | 709 | 168 | 1763 |
| lift: unimplemented or unrecoverable op | 641 | 104 | 2250 |
| call: unresolved target | 619 | 40 | 1122 |
| memory: unmanaged store dropped | 535 | 119 | 2610 |
| meta: native metadata pointer as value | 278 | 16 | 1099 |
| access: inaccessible member | 205 | 30 | 560 |
| call: indirect call | 179 | 8 | 293 |
| call: hidden generic argument | 127 | 58 | 187 |
| dataflow: zero on phi edge | 103 | 1 | 278 |
| dataflow: non-empty stack at end | 70 | 1 | 70 |
| dataflow: receiver not recovered | 55 | 12 | 106 |
| dataflow: undefined local, float lane V1-V7 | 31 | 2 | 48 |
| /Exception landing pad at/ | 548 | 111 | 9625 |

greedy fix order (methods cleared at each step):
  +  607 ->   607  type: no legal conversion
  +  348 ->   955  memory: unmanaged load
  +  446 ->  1401  other
  +  297 ->  1698  dataflow: undefined local
  +  345 ->  2043  lift: unimplemented or unrecoverable op
  +  401 ->  2444  type: synthetic default in operand slot
  +  384 ->  2828  memory: unmanaged store dropped
  +  326 ->  3154  call: unresolved target
  +  180 ->  3334  meta: native metadata pointer as value
  +  151 ->  3485  access: inaccessible member

top unresolved call targets (of 157):
    259  0x37C2D44
    171  0x37FC3B0
     69  0x32D69D0
     55  0x3C29C4C
     48  0x37C2A9C
     37  0x32D7C3C
     35  0x3988F84
     29  0x50921DC
     21  0x38E44AC
     15  0x37C2AA0
     15  0x52BD3BC
     14  0x3C29C08
     13  0x32D50FC
     13  0x37C2B6C
     12  0x39295B4
```

#### Control: CastleClashers.Game

```text
scope: CastleClashers.Game
game-owned methods with diagnostics: 2482
methods naming a canonical shared-generic type: 108

| family | methods | sole | occurrences |
|---|---:|---:|---:|
| type: no legal conversion | 1208 | 414 | 5360 |
| memory: unmanaged load | 706 | 202 | 3706 |
| dataflow: undefined local | 638 | 83 | 1677 |
| lift: unimplemented or unrecoverable op | 481 | 66 | 1755 |
| type: synthetic default in operand slot | 480 | 86 | 1356 |
| other | 476 | 91 | 6855 |
| memory: unmanaged store dropped | 446 | 106 | 2214 |
| call: unresolved target | 375 | 18 | 672 |
| access: inaccessible member | 140 | 22 | 457 |
| meta: native metadata pointer as value | 135 | 5 | 582 |
| call: indirect call | 82 | 1 | 123 |
| dataflow: zero on phi edge | 79 | 0 | 242 |
| call: hidden generic argument | 70 | 21 | 97 |
| dataflow: receiver not recovered | 44 | 9 | 73 |
| dataflow: non-empty stack at end | 28 | 0 | 28 |
| dataflow: undefined local, float lane V1-V7 | 21 | 2 | 29 |
| /Exception landing pad at/ | 242 | 29 | 6215 |

greedy fix order (methods cleared at each step):
  +  414 ->   414  type: no legal conversion
  +  218 ->   632  memory: unmanaged load
  +  184 ->   816  lift: unimplemented or unrecoverable op
  +  213 ->  1029  type: synthetic default in operand slot
  +  224 ->  1253  other
  +  220 ->  1473  dataflow: undefined local
  +  325 ->  1798  memory: unmanaged store dropped
  +  209 ->  2007  call: unresolved target
  +   90 ->  2097  access: inaccessible member
  +   86 ->  2183  meta: native metadata pointer as value

top unresolved call targets (of 112):
    177  0x37C2D44
     72  0x37FC3B0
     53  0x32D69D0
     33  0x3988F84
     29  0x50921DC
     21  0x32D7C3C
     15  0x52BD3BC
     14  0x3C29C08
     13  0x38E44AC
     13  0x37C2B6C
     10  0x446DFD4
     10  0x398925C
      9  0x446E560
      9  0x3BAD7C4
      7  0x3C01928
```

#### Branch: all game-owned

```text
scope: Assembly-CSharp, CastleClashers.Core, CastleClashers.Game, CastleClashers.Internal.Services, CastleClashers.Internal.UI, CastleClashers.Rules, CastleClashers.Rules.Client, CastleClashers.SDKGlue, CastleClashers.VoodooTune, Ranked
game-owned methods with diagnostics: 3991
methods naming a canonical shared-generic type: 173

| family | methods | sole | occurrences |
|---|---:|---:|---:|
| type: no legal conversion | 1614 | 607 | 6409 |
| memory: unmanaged load | 1229 | 320 | 6243 |
| other | 987 | 257 | 10612 |
| dataflow: undefined local | 976 | 176 | 2459 |
| type: synthetic default in operand slot | 709 | 168 | 1763 |
| lift: unimplemented or unrecoverable op | 641 | 104 | 2250 |
| call: unresolved target | 619 | 40 | 1122 |
| memory: unmanaged store dropped | 535 | 119 | 2610 |
| meta: native metadata pointer as value | 278 | 16 | 1099 |
| access: inaccessible member | 205 | 30 | 560 |
| call: indirect call | 179 | 8 | 293 |
| call: hidden generic argument | 127 | 58 | 187 |
| dataflow: zero on phi edge | 103 | 1 | 278 |
| dataflow: non-empty stack at end | 70 | 1 | 70 |
| dataflow: receiver not recovered | 55 | 12 | 106 |
| dataflow: undefined local, float lane V1-V7 | 31 | 2 | 48 |
| /Exception landing pad at/ | 548 | 111 | 9564 |

greedy fix order (methods cleared at each step):
  +  607 ->   607  type: no legal conversion
  +  348 ->   955  memory: unmanaged load
  +  446 ->  1401  other
  +  297 ->  1698  dataflow: undefined local
  +  345 ->  2043  lift: unimplemented or unrecoverable op
  +  401 ->  2444  type: synthetic default in operand slot
  +  384 ->  2828  memory: unmanaged store dropped
  +  326 ->  3154  call: unresolved target
  +  180 ->  3334  meta: native metadata pointer as value
  +  151 ->  3485  access: inaccessible member

top unresolved call targets (of 157):
    259  0x37C2D44
    171  0x37FC3B0
     69  0x32D69D0
     55  0x3C29C4C
     48  0x37C2A9C
     37  0x32D7C3C
     35  0x3988F84
     29  0x50921DC
     21  0x38E44AC
     15  0x37C2AA0
     15  0x52BD3BC
     14  0x3C29C08
     13  0x32D50FC
     13  0x37C2B6C
     12  0x39295B4
```

#### Branch: CastleClashers.Game

```text
scope: CastleClashers.Game
game-owned methods with diagnostics: 2482
methods naming a canonical shared-generic type: 108

| family | methods | sole | occurrences |
|---|---:|---:|---:|
| type: no legal conversion | 1208 | 414 | 5360 |
| memory: unmanaged load | 706 | 202 | 3706 |
| dataflow: undefined local | 638 | 83 | 1677 |
| lift: unimplemented or unrecoverable op | 481 | 66 | 1755 |
| type: synthetic default in operand slot | 480 | 86 | 1356 |
| other | 476 | 91 | 6794 |
| memory: unmanaged store dropped | 446 | 106 | 2214 |
| call: unresolved target | 375 | 18 | 672 |
| access: inaccessible member | 140 | 22 | 457 |
| meta: native metadata pointer as value | 135 | 5 | 582 |
| call: indirect call | 82 | 1 | 123 |
| dataflow: zero on phi edge | 79 | 0 | 242 |
| call: hidden generic argument | 70 | 21 | 97 |
| dataflow: receiver not recovered | 44 | 9 | 73 |
| dataflow: non-empty stack at end | 28 | 0 | 28 |
| dataflow: undefined local, float lane V1-V7 | 21 | 2 | 29 |
| /Exception landing pad at/ | 242 | 29 | 6154 |

greedy fix order (methods cleared at each step):
  +  414 ->   414  type: no legal conversion
  +  218 ->   632  memory: unmanaged load
  +  184 ->   816  lift: unimplemented or unrecoverable op
  +  213 ->  1029  type: synthetic default in operand slot
  +  224 ->  1253  other
  +  220 ->  1473  dataflow: undefined local
  +  325 ->  1798  memory: unmanaged store dropped
  +  209 ->  2007  call: unresolved target
  +   90 ->  2097  access: inaccessible member
  +   86 ->  2183  meta: native metadata pointer as value

top unresolved call targets (of 112):
    177  0x37C2D44
     72  0x37FC3B0
     53  0x32D69D0
     33  0x3988F84
     29  0x50921DC
     21  0x32D7C3C
     15  0x52BD3BC
     14  0x3C29C08
     13  0x38E44AC
     13  0x37C2B6C
     10  0x446DFD4
     10  0x398925C
      9  0x446E560
      9  0x3BAD7C4
      7  0x3C01928
```

## Slice 2b: handler calls and disjoint regions (2026-10-01)

Task: dankondr/castle-recovery#206. Follow-up to merged Cpp2IL#175; continues
Cpp2IL#80. **Draft: the >50% reduction target remains unmet.**

Control is `9a7cd59582e69f927b68e5ed62dd59553ec38602`, the #175 merge.
Its tree is identical to #175's measured `ad80dde37966f903be4712221e8c59d8b73483f4`
(`git diff` is empty), so the complete `astra206-r6-branch` sweep and audit are
reused as the control. The new full sweep is `astra206-r7-stage4`: 69,982 native
methods, 183 assemblies, 178,274 reported methods. The denominator for the task's
cumulative target remains the original **15,537 owned pads**.

### Changes

- A catch can call a parameterless virtual member on the caught exception when
  its function pointer and hidden MethodInfo are the two halves of the same
  proven vtable entry. Emission uses `callvirt` and preserves overrides.
- Reference-valued handler calls define real locals used by later calls. Metadata
  string literals are retained. Scalar/aggregate returns remain unsupported.
- A proven `cctor_finished` guard with exactly one recognized class-init call
  becomes `RuntimeHelpers.RunClassConstructor`. Initialization effects and
  exceptions are preserved; extra effects or a different class reject the proof.
- Unreachable predecessors no longer veto region entry or cleanup sharing.
  Their branches are redirected to legal entry anchors. Live entries still
  require a valid boundary.
- When one enclosing catch would cross an uncovered call, disjoint protected
  units get separate clauses with the same returning handler. Uncovered calls
  remain outside the try. Overlap/nesting and handler exit checks still apply.

### Verification

| Scope | Methods | Diagnosed control → branch | Newly clean | Clean regressions | Pads control → branch |
|---|---:|---:|---:|---:|---:|
| All | 178,274 | 16,228 → 16,228 | 0 | 0 | 47,263 → 42,027 |
| Game-owned | 25,348 | 3,944 → 3,944 | 0 | 0 | 10,816 → 9,623 |
| CastleClashers.Game | 14,423 | 2,442 → 2,442 | 0 | 0 | 6,659 → 6,207 |
| Castle-building owners + nested types | 280 | 87 → 87 | 0 | 0 | 684 → 684 |

This slice removes **1,193 owned pad messages across 80 methods**. Eight methods
lose all pads but retain other diagnostics. No method becomes entirely diagnostic-free,
and no method gains any diagnostic. The castle-building scope is unchanged; its
newly clean list is empty. Including merged #175, the cumulative reduction is
**5,914 / 15,537 = 38.1%**. **9,623 remain**, versus the target of at most **7,768**
(another 1,855 must be removed).

Measured steps against the same control:

| Step | Owned pads remaining |
|---|---:|
| Merged #175 | 10,816 |
| Handler calls/results, literals and class initialization | 10,481 |
| Reachable-entry checks | 9,804 |
| Disjoint catch clauses | 9,623 |

The fixed 133-method state-machine cohort improves **3,878 → 3,162 pads**.
Native typed-catch proofs increase from 19 to 50 cohort methods, covering
**392 → 811 native pads**. This slice clears no whole state-machine method.

ILVerify: **170,144 valid / 416 invalid / 7,714 partial** in both control and branch;
**zero status transitions**, including zero valid→invalid. The separate Bootstrap
reachability gate remains 29/29 blocked in both; its nonzero audit exit is not
reported as a passed gate.

Tests: Core **1,214/1,214**, LibCpp2IL **12/12**, JitOracle **9/9**.
Focused EH tests: **45/45**. Running those same tests against the pre-change
production source gives **41 pass / 4 fail**: both positive virtual-result cases,
the unreachable-entry case, and the disjoint-range case. The new negative cases
continue to reject mismatched receiver/MethodInfo, a wrong cctor flag/class, and
an extra store. CLR execution checks virtual override dispatch, the string result,
once-only class initialization, and exceptions at both protected calls and at
an uncovered intervening call.

Commands used (with `NUGET_PACKAGES=/private/tmp/astra204-nuget`):

```sh
dotnet build Cpp2IL/Cpp2IL.csproj -c Release -f net10.0
dotnet test --project Cpp2IL.Core.Tests
dotnet test --project LibCpp2ILTests
dotnet test --project Cpp2IL.JitOracle.Tests
~/castle-evidence/r241/run-cpp2il.sh /private/tmp/astra206-r7-stage4-bin /private/tmp/astra206-r7-stage4
```

### Native/IL review of this slice

No newly diagnostic-free methods exist in this slice. Instead, these ten methods
with newly materialized clauses were checked against the retained native ISIL and
LSDA ranges. This is a review of the EH changes, not a claim that their remaining
normal-body diagnostics are harmless.

| Method | Pads before → after | Checked handler |
|---|---:|---|
| `CastleClashers.HumanLikeBots.PlayerProfileFetcher::ParsePlayerProfileData` | 55 → 2 | get_Message via callvirt → literal + String.Concat → explicit EpiLog class init → LogError(this) |
| `QuestController::AddQuestsByDifficulty` | 45 → 0 | Dispose of the same List<QuestDefinition> enumerator |
| `Voodoo.Sauce.Privacy.PrivacyManager+<RequestAccessToData>d__48::MoveNext` | 43 → 2 | state = -2; address of the same AsyncVoidMethodBuilder; SetException; return |
| `CastleClashers.HumanLikeBots.PlayerProfileFetcher::ParseUnitsData` | 49 → 10 | separate catch clauses, preserved inner Dispose and log-error handler |
| `Voodoo.Sauce.Privacy.PrivacyManager+<SynchronizeWithServer>d__51::MoveNext` | 41 → 2 | state = -2; same AsyncVoidMethodBuilder.SetException |
| `Voodoo.Sauce.Core.VoodooSauceBehaviour+<Awake>d__31::MoveNext` | 37 → 2 | state = -2; same AsyncVoidMethodBuilder.SetException |
| `Voodoo.Sauce.Tools.AccessButton.HidePanel+<UIAppear>d__15::MoveNext` | 36 → 2 | state = -2; same AsyncVoidMethodBuilder.SetException |
| `MatchTelemetryTrackerController::BuildDefenderUnitsWithDamage` | 52 → 20 | Dispose of the same List<Agent> enumerator |
| `NoInternetController+<ResumeGame>d__27::MoveNext` | 33 → 2 | separate protected ranges; same AsyncVoidMethodBuilder.SetException |
| `Voodoo.Live.VoodooLive+<Initialize>d__48::MoveNext` | 32 → 2 | state = -2; explicit AsyncTaskMethodBuilder class init; SetException |

The two logging handlers preserve the original literal, virtual exception Message
and cached call result. The six async handlers store -2 before SetException and
leave to the existing return. The two newly emitted finally clauses dispose the
same normal-path enumerator address. Uncovered calls remain outside split ranges;
unproven auxiliary pads keep their original warning text.

### Remaining proof boundaries

| Remaining coverage | Methods | Remaining pads |
|---|---:|---:|
| No native proof | 342 | 6,081 |
| All native pads proven; IL still refused | 70 | 1,321 |
| Mixed proven/unproven | 137 | 2,221 |

Native proofs cover **7,084 finally + 1,146 catch = 8,230 distinct pads**;
**2,316 proven pads remain unmaterialized**. A native proof does not create a
missing emitted protected unit or repair a diagnosed cleanup receiver.

- `CastleMaker.Build` still lacks a reachable emitted seed; `StoreController.OpenSection`
  still has a diagnosed/defaulted Dispose receiver. Normal-body fixes belong to the
  reserved dataflow/memory lane. The prior 1,209/713-pad refusal cohorts below are
  historical measurements, not new independent gains available from one guard.
- Async handlers still have native builder targets absent from MethodsByAddress
  and null MethodInfo, unknown exception-stack values, and cached owner/return
  values that join live normal code. A field reload after a throwing call would
  not prove the original cached receiver. A non-void or live-local merge needs an
  explicit SSA agreement; this slice still accepts a void epilogue only.
- Consuming the existing write-barrier/boxing alias contracts and tracking saved
  normal-path field locals were investigated separately. The write-barrier probe
  removes 169 non-owned pads but no owned pads; the state-machine catch count stays
  811. These probes are not included in the delivered change.
- The offset-16 defaults-table class still has no type from existing seeding.
  No new guessed Object-class recognizer, game-specific address, filter or fault
  interpretation is introduced. Across the 1,019-method cohort there are no
  negative selectors or undecoded action chains.

The remaining warning text is unchanged. The <50%-remaining objective is still
open; this PR stays a draft rather than treating missing native/SSA evidence as proof.

### Diagnostic-family output

#### Control: all game-owned

```text
scope: Assembly-CSharp, CastleClashers.Core, CastleClashers.Game, CastleClashers.Internal.Services, CastleClashers.Internal.UI, CastleClashers.Rules, CastleClashers.Rules.Client, CastleClashers.SDKGlue, CastleClashers.VoodooTune, Ranked
game-owned methods with diagnostics: 3944
methods naming a canonical shared-generic type: 170

| family | methods | sole | occurrences |
|---|---:|---:|---:|
| type: no legal conversion | 1581 | 577 | 6452 |
| memory: unmanaged load | 1230 | 322 | 6246 |
| dataflow: undefined local | 976 | 176 | 2459 |
| other | 936 | 225 | 11701 |
| type: synthetic default in operand slot | 709 | 170 | 1762 |
| lift: unimplemented or unrecoverable op | 660 | 108 | 2284 |
| call: unresolved target | 619 | 40 | 1122 |
| memory: unmanaged store dropped | 535 | 120 | 2610 |
| meta: native metadata pointer as value | 280 | 15 | 1102 |
| access: inaccessible member | 205 | 30 | 560 |
| call: indirect call | 179 | 8 | 293 |
| dataflow: zero on phi edge | 133 | 2 | 415 |
| call: hidden generic argument | 127 | 59 | 187 |
| dataflow: non-empty stack at end | 70 | 1 | 70 |
| dataflow: receiver not recovered | 55 | 12 | 106 |
| dataflow: undefined local, float lane V1-V7 | 32 | 2 | 49 |
| /Exception landing pad at/ | 557 | 111 | 10816 |

greedy fix order (methods cleared at each step):
  +  577 ->   577  type: no legal conversion
  +  351 ->   928  memory: unmanaged load
  +  409 ->  1337  other
  +  301 ->  1638  lift: unimplemented or unrecoverable op
  +  364 ->  2002  type: synthetic default in operand slot
  +  383 ->  2385  dataflow: undefined local
  +  383 ->  2768  memory: unmanaged store dropped
  +  324 ->  3092  call: unresolved target
  +  177 ->  3269  meta: native metadata pointer as value
  +  150 ->  3419  access: inaccessible member

top unresolved call targets (of 157):
    259  0x37C2D44
    171  0x37FC3B0
     69  0x32D69D0
     55  0x3C29C4C
     48  0x37C2A9C
     37  0x32D7C3C
     35  0x3988F84
     29  0x50921DC
     21  0x38E44AC
     15  0x37C2AA0
     15  0x52BD3BC
     14  0x3C29C08
     13  0x32D50FC
     13  0x37C2B6C
     12  0x39295B4
```

#### Control: CastleClashers.Game

```text
scope: CastleClashers.Game
game-owned methods with diagnostics: 2442
methods naming a canonical shared-generic type: 105

| family | methods | sole | occurrences |
|---|---:|---:|---:|
| type: no legal conversion | 1180 | 387 | 5423 |
| memory: unmanaged load | 707 | 204 | 3708 |
| dataflow: undefined local | 638 | 83 | 1677 |
| lift: unimplemented or unrecoverable op | 502 | 67 | 1786 |
| type: synthetic default in operand slot | 480 | 88 | 1355 |
| memory: unmanaged store dropped | 446 | 107 | 2214 |
| other | 433 | 65 | 7150 |
| call: unresolved target | 375 | 18 | 672 |
| access: inaccessible member | 140 | 22 | 457 |
| meta: native metadata pointer as value | 137 | 4 | 585 |
| dataflow: zero on phi edge | 102 | 1 | 369 |
| call: indirect call | 82 | 1 | 123 |
| call: hidden generic argument | 70 | 22 | 97 |
| dataflow: receiver not recovered | 44 | 9 | 73 |
| dataflow: non-empty stack at end | 28 | 0 | 28 |
| dataflow: undefined local, float lane V1-V7 | 22 | 2 | 30 |
| /Exception landing pad at/ | 247 | 29 | 6659 |

greedy fix order (methods cleared at each step):
  +  387 ->   387  type: no legal conversion
  +  221 ->   608  memory: unmanaged load
  +  199 ->   807  lift: unimplemented or unrecoverable op
  +  212 ->  1019  type: synthetic default in operand slot
  +  186 ->  1205  other
  +  219 ->  1424  dataflow: undefined local
  +  324 ->  1748  memory: unmanaged store dropped
  +  208 ->  1956  call: unresolved target
  +   90 ->  2046  access: inaccessible member
  +   83 ->  2129  meta: native metadata pointer as value

top unresolved call targets (of 112):
    177  0x37C2D44
     72  0x37FC3B0
     53  0x32D69D0
     33  0x3988F84
     29  0x50921DC
     21  0x32D7C3C
     15  0x52BD3BC
     14  0x3C29C08
     13  0x38E44AC
     13  0x37C2B6C
     10  0x446DFD4
     10  0x398925C
      9  0x446E560
      9  0x3BAD7C4
      7  0x3C01928
```

#### Branch: all game-owned

```text
scope: Assembly-CSharp, CastleClashers.Core, CastleClashers.Game, CastleClashers.Internal.Services, CastleClashers.Internal.UI, CastleClashers.Rules, CastleClashers.Rules.Client, CastleClashers.SDKGlue, CastleClashers.VoodooTune, Ranked
game-owned methods with diagnostics: 3944
methods naming a canonical shared-generic type: 170

| family | methods | sole | occurrences |
|---|---:|---:|---:|
| type: no legal conversion | 1580 | 577 | 6451 |
| memory: unmanaged load | 1230 | 322 | 6245 |
| dataflow: undefined local | 976 | 176 | 2459 |
| other | 928 | 225 | 10508 |
| type: synthetic default in operand slot | 709 | 170 | 1762 |
| lift: unimplemented or unrecoverable op | 660 | 108 | 2284 |
| call: unresolved target | 619 | 40 | 1122 |
| memory: unmanaged store dropped | 535 | 120 | 2610 |
| meta: native metadata pointer as value | 278 | 15 | 1099 |
| access: inaccessible member | 205 | 30 | 560 |
| call: indirect call | 179 | 8 | 293 |
| dataflow: zero on phi edge | 133 | 2 | 415 |
| call: hidden generic argument | 127 | 59 | 187 |
| dataflow: non-empty stack at end | 70 | 1 | 70 |
| dataflow: receiver not recovered | 55 | 12 | 106 |
| dataflow: undefined local, float lane V1-V7 | 32 | 2 | 49 |
| /Exception landing pad at/ | 549 | 111 | 9623 |

greedy fix order (methods cleared at each step):
  +  577 ->   577  type: no legal conversion
  +  351 ->   928  memory: unmanaged load
  +  409 ->  1337  other
  +  301 ->  1638  lift: unimplemented or unrecoverable op
  +  364 ->  2002  type: synthetic default in operand slot
  +  383 ->  2385  dataflow: undefined local
  +  383 ->  2768  memory: unmanaged store dropped
  +  324 ->  3092  call: unresolved target
  +  177 ->  3269  meta: native metadata pointer as value
  +  150 ->  3419  access: inaccessible member

top unresolved call targets (of 157):
    259  0x37C2D44
    171  0x37FC3B0
     69  0x32D69D0
     55  0x3C29C4C
     48  0x37C2A9C
     37  0x32D7C3C
     35  0x3988F84
     29  0x50921DC
     21  0x38E44AC
     15  0x37C2AA0
     15  0x52BD3BC
     14  0x3C29C08
     13  0x32D50FC
     13  0x37C2B6C
     12  0x39295B4
```

#### Branch: CastleClashers.Game

```text
scope: CastleClashers.Game
game-owned methods with diagnostics: 2442
methods naming a canonical shared-generic type: 105

| family | methods | sole | occurrences |
|---|---:|---:|---:|
| type: no legal conversion | 1179 | 387 | 5422 |
| memory: unmanaged load | 707 | 204 | 3708 |
| dataflow: undefined local | 638 | 83 | 1677 |
| lift: unimplemented or unrecoverable op | 502 | 67 | 1786 |
| type: synthetic default in operand slot | 480 | 88 | 1355 |
| memory: unmanaged store dropped | 446 | 107 | 2214 |
| other | 428 | 65 | 6698 |
| call: unresolved target | 375 | 18 | 672 |
| access: inaccessible member | 140 | 22 | 457 |
| meta: native metadata pointer as value | 135 | 4 | 582 |
| dataflow: zero on phi edge | 102 | 1 | 369 |
| call: indirect call | 82 | 1 | 123 |
| call: hidden generic argument | 70 | 22 | 97 |
| dataflow: receiver not recovered | 44 | 9 | 73 |
| dataflow: non-empty stack at end | 28 | 0 | 28 |
| dataflow: undefined local, float lane V1-V7 | 22 | 2 | 30 |
| /Exception landing pad at/ | 242 | 29 | 6207 |

greedy fix order (methods cleared at each step):
  +  387 ->   387  type: no legal conversion
  +  221 ->   608  memory: unmanaged load
  +  200 ->   808  lift: unimplemented or unrecoverable op
  +  214 ->  1022  type: synthetic default in operand slot
  +  183 ->  1205  other
  +  219 ->  1424  dataflow: undefined local
  +  324 ->  1748  memory: unmanaged store dropped
  +  208 ->  1956  call: unresolved target
  +   90 ->  2046  access: inaccessible member
  +   83 ->  2129  meta: native metadata pointer as value

top unresolved call targets (of 112):
    177  0x37C2D44
     72  0x37FC3B0
     53  0x32D69D0
     33  0x3988F84
     29  0x50921DC
     21  0x32D7C3C
     15  0x52BD3BC
     14  0x3C29C08
     13  0x38E44AC
     13  0x37C2B6C
     10  0x446DFD4
     10  0x398925C
      9  0x446E560
      9  0x3BAD7C4
      7  0x3C01928
```

---

## Merged slice 2: retained evidence

The following sections describe merged #175 and its historical control.

## Rule

An LSDA landing pad is evidence of native unwinding, not by itself evidence of a
managed catch or finally. Decode the action chain and its RTTI entries first.
Malformed chains keep the call site without granting a cleanup proof.

`EhRegionPartition` retains a snapshot before SSA rewrites register and frame
identities. `NativeExceptionRegionProof` compares each reachable protected call's
exceptional path with the normal cleanup copy. The comparison includes the call
target, every argument (including MethodInfo), frame storage identity, effect order,
and propagation of the original exception. Small unwind closures use the same
interpreter; a returning closure resumes its caller with the proven frame writes
and effects. Only propagation of the original exception completes a cleanup proof. C++ wrapper allocation, begin/end catch and termination guards are
protocol; unmatched calls and stores reject the proof.

Calls invalidate potentially written frame storage on normal and exceptional
edges. Existing parameter/field layout helpers bound known writes; unknown sizes
stay conservative. Native store widths distinguish an adjacent saved pointer from
an overlapping write. Recognized value boxing copies its input and therefore does
not invalidate the input frame storage. Direct and indirect calls clobber caller-saved registers.
A recovered no-return call cannot fall through into the next out-of-line throw site.
The normal dataflow and handler traversal have explicit limits; exceeding them
retains the diagnostic.

`ExceptionRegionRecovery` uses the already emitted, resolved normal cleanup IL.
It requires one entry, no extra protected native calls, equivalent cleanup copies,
and cleanup locals definitely assigned on every path before entry. Several effects
with identical protected site sets form one ordered handler; an outer effect that
also protects an inner cleanup stays in a separate enclosing finally. Every incoming edge to an erased cleanup
must exit a proven region. Regions must be disjoint or properly nested, and nested
cleanup order must agree with the native handler. The emitter moves the blocks into
contiguous clauses, preserves fallthroughs, rewrites exits to `leave`, and appends
`endfinally`. Switch cases that exit use leave trampolines, preserving the default
path. Shared entry anchors prevent branches into a try body.

Typed catch requires a recognized `Object::IsInst` or `Class::IsAssignableFrom`,
a resolved exception type, original-exception propagation on mismatch, and a
supported handler. Facts at a shared handler are intersected across every throwing
call in the range. The exception is stored in a typed local; a void merge or separate
void return ends with `leave` to a normal return outside the clause. Proven this-field stores and addresses of value-type fields are supported. Other
captured locals, non-void return values, arbitrary catch CFGs, filters and faults
still need proofs.

The narrow class-predicate recognizer is the authorized exception to the
[dankondr/castle-recovery#208](https://github.com/dankondr/castle-recovery/issues/208)
lane boundary, in its own commit `4c6a4c6e`. It follows only bounded, pure ARM64 B
veneers from the binary's `il2cpp_class_is_assignable_from` export and compares the
terminal body with the call target. It does not change the general key-function
rewrite table. In r241, export `37CC198` and call veneer `37C3128` both branch to
`3824E38`; these are evidence addresses, never production constants.

A pad's exact slice-1 warning is removed only after its proof is materialized and
all reachable incoming protected calls are covered. Other warnings are retained.

## Runnable checks

```sh
dotnet build Cpp2IL/Cpp2IL.csproj -c Release -f net10.0
dotnet test --project Cpp2IL.Core.Tests
dotnet test --project LibCpp2ILTests
dotnet test --project Cpp2IL.JitOracle.Tests
```

`ExceptionRegionRecoveryTests` uses synthetic ISIL to check:

- matching foreach/Dispose becomes a real finally; a different argument or an
  extra store keeps exactly one diagnostic;
- repeated reads of mutable heap storage do not prove equal cleanup arguments;
- constant cleanup dispatch is resolved, but caller-saved values across an
  indirect call cannot establish a proof;
- an adjacent eight-byte saved pointer survives a write to the next object;
  an overlapping sixteen-byte store does not establish a proof;
- nested finally clauses execute inner then outer, exactly once, on both normal
  and exceptional exits in a serialized assembly loaded by the CLR;
- flat compound and nested cleanup have distinct behavior when the first cleanup throws;
- two incoming branches may assign the same handler local; omitting either store refuses it;
- switch case exits and the default path run exactly one finally;
- recognized object/class type tests receive the actual exception and leave to a
  normal merge or void return; an unknown test remains diagnosed;
- a shared catch proves every throwing input; recognized boxing preserves adjacent
  storage, while an unknown writer still invalidates it.

`KeyFunctionRecoveryTests` rejects BL wrappers, argument shuffles, cycles and absent
exports when recognizing the class predicate.

`ElfEhTablesTests` checks absolute and indirect PC-relative RTTI, a linked
catch-plus-cleanup action chain, and a cyclic malformed chain that preserves its
call site without a proof.

## Native/IL review

Reviewed sixteen methods made diagnostic-free by this PR against ARM64 disassembly, LSDA ranges and
serialized IL. Addresses below are evidence for r241, never recognizer constants.
All listed handlers load the same enumerator local/address used by the native
normal and exceptional Dispose copies and end in `endfinally`. Early returns use
`leave`; GetEnumerator stays outside its own protected region. Native runtime
initialization/write-barrier calls may have been removed by existing passes, and
native field reads may already be represented by managed getters.

| Method | Native entry | Normal / pad Dispose | Protected native behavior |
|---|---|---|---|
| CastleBuildingController.HowManyUpgradable | 3C8D7CC | 3C8D974 / 3C8DAB0; 3C8D9EC / 3C8DA70 | Two independent enumerations: MoveNext, price/currency calls and their null throws |
| CastleMaker.GetDecorationsAtPosition | 3E57108 | 3E57380 / 3E57420 | MoveNext, decoration lookup, Unity inequality, append and two null throws |
| CastleMaker.TryApplyFetchedDecorations | 3E58810 | 3E58ABC / 3E58B20 | MoveNext, allocation/constructor, append and three null throws |
| CastleMaker.ApplyPvpOpponentDecorations | 3E5583C | 3E55A30 / 3E55AA8 | MoveNext, allocation/constructor, append and three null throws |
| CastleMaker.MirrorFoundationPositions | 3E55C94 | 3E55E80 / 3E55EF4 | MoveNext, allocation/constructor, append and three null throws |
| CardController.GetAverageLevelOfEquippedCards | 3EE8F08 | 3EE8FF8 / 3EE905C | MoveNext, get_level, ObscuredInt conversion and the loop null throw |
| EngineersController.GetEngineerData(string) | 3BC8204 | 3BC82D8 / 3BC832C | MoveNext, string equality and the loop null throw |
| EngineersController.GetEngineerVisualData(string) | 3BC83D4 | 3BC84A8 / 3BC84FC | MoveNext, string equality and the loop null throw |
| EngineersController.GetEngineerThatUnlocksAtArenaIndex | 3BC852C | 3BC85F8 / 3BC8648 | MoveNext and the loop null throw |
| TimedCastleBuildingController.CheckIfBuildingAtThatPosition | 3D3DF18 | 3D3E01C / 3D3E078 | MoveNext and the loop null throw |
| TimedCastleBuildingController.CheckIfUpgradingAtThatPosition | 3D3EEC0 | 3D3EFC4 / 3D3F020 | MoveNext and the loop null throw |
| LevelCostTable.RebuildIndex | 3C875F8 | 3C8782C / 3C87898 | MoveNext, ContainsKey, boxing, warning formatting/logging, Add and null throws |
| MatchTelemetryTrackerController.BuildUnitsPayload | 3F13C24 | 3F13FEC / 3F140A8 | Agent enumeration, payload dictionary creation, boxing, Add and null throws |
| MatchTelemetryTrackerController.BuildUnitsEndStatePayload | 3F14410 | 3F14910 / 3F14A10 | Agent enumeration, end-state fields, boxing, Add and null throws |
| Voodoo.ADN.ContextSDK.AdnDictionaryConverter.ConvertValues | 3A539EC | 3A53C58 / 3A53CE4 | Dictionary enumeration, TryParse alternatives, boxing and output insertion |
| Voodoo.Live.Debugger.TransactionDebugUI.PopulateValues | 3AB11AC | 3AB1444 / 3AB14D0 | Receipt enumeration, widget population, boxing, formatting and null throws |

The CardController example protects native calls at 3EE8FC0, 3EE8FD4, 3EE8FDC
and 3EE9020. GetEnumerator at 3EE8FAC, Dispose at 3EE8FF8, and the pre-loop null
throw at 3EE9024 remain outside the try. The native handler saves the exception,
loads the enumerator address from `[sp+0x10]`, calls Dispose, and rethrows. Its
auxiliary cleanup closure reads the same exception/receiver record.

The third continuation also checks the real catch emitter, not only hand-built CIL.
The handler-entry `stloc` defines the exception local before its managed uses.
Field stores require the native width to match the resolved field; a builder address
names the whole field, rather than its first member. Hidden MethodInfo recovery
requires the exact argument slot and receiver type. Handler grouping compares declaring assemblies and full
callee signatures so overloads cannot collapse into one catch.

Absolute-address stores are effects even when `Instruction.Destination` omits them.
An unmatched store refuses the proof. Returning closure tests cover different
arguments, an extra global write and a caller that returns instead of unwinding.

## Verification after the foreach fix (#180)

Task: dankondr/castle-recovery#206 (slice 2). Continues PR #175 and addresses
[dankondr/Cpp2IL#80](https://github.com/dankondr/Cpp2IL/issues/80).
The separately committed class-predicate recognizer remains the authorized
castle-recovery#208 exception; this continuation changes no key-function recognition.

Control: `19dc0743f7820dca0138bf369e5a9ce7093445ba` (`development`, merged #180). PR #175 was rebased after
[the review comment about stale Current reads](https://github.com/dankondr/Cpp2IL/pull/175#issuecomment-5921843917).
The merged `FrameStructFieldReads` fix runs in both control and branch. EH code:
`0c825bfa`; measured branch: `c884b394`. This recheck changes no lifter source.
Both full sweeps process 69,982 native methods, emit 183 assemblies and report
178,274 methods. Outputs: `astra206-r6-control` and `astra206-r6-branch`.

| Scope | Methods | Diagnosed control → branch | Newly clean | Clean regressions | Pads control → branch |
|---|---:|---:|---:|---:|---:|
| All | 178,274 | 16,768 → 16,228 | 540 | 0 | 54,380 → 47,263 |
| Game-owned | 25,348 | 4,274 → 3,944 | 330 | 0 | 15,537 → 10,816 |
| CastleClashers.Game | 14,423 | 2,673 → 2,442 | 231 | 0 | 9,865 → 6,659 |
| Castle-building owners + nested types | 280 | 100 → 87 | 13 | 0 | 882 → 684 |

Against this fresh control, no method gains a diagnostic in any scope; the
regression list is empty. The 330-method diagnostic-free list is unchanged from
before the rebase. Here, "clean" means no recovery diagnostics; it is not a claim
that all behavior has been tested. The Current defect is checked separately below.
Warning text was not hidden or reworded.

Compared with the previous branch output on #179, owned diagnostic occurrences
increase from 37,410 to 37,418 in four already-diagnosed methods. The same eight
additional synthetic-default warnings appear in the new control. They are exposed
by #180, not introduced by EH recovery:

| Method | Additional warnings | Operand type |
|---|---:|---|
| `CastleMaker.SpawnShieldsFromPlacements` | 5 | SpriteOutlineController |
| `Voodoo.Live.RandomReward.GetItems` | 1 | Reward |
| `Voodoo.Live.Offers.FeatureClient.Dispose` | 1 | Campaign |
| `Tournament.TournamentsData.PruneExcept` | 1 | String |


### Castle-building newly clean methods

- ``System.Int32 CastleBuildingController::HowManyUpgradable()``
- ``System.Collections.Generic.List`1<DecorationSO> CastleMaker::GetDecorationsAtPosition(UnityEngine.Vector2)``
- ``DecorationRoofSO CastleMaker::GetRoofDecorationAtPosition(UnityEngine.Vector2)``
- ``DecorationFoundataionSO CastleMaker::GetAnyFoundationDecoration()``
- ``System.Boolean CastleMaker::TryApplyFetchedDecorations(CastleClashers.HumanLikeBots.HumanLikeBotProfile)``
- ``System.Void CastleMaker::ApplyPvpOpponentFoundations(CastleClashers.HumanLikeBots.FetchedPlayerProfile)``
- ``System.Void CastleMaker::ApplyPvpOpponentDecorations(CastleClashers.HumanLikeBots.FetchedPlayerProfile)``
- ``System.Collections.Generic.List`1<FoundationData> CastleMaker::MirrorFoundationPositions(System.Collections.Generic.List`1<FoundationData>, System.Int32)``
- ``EngineerData EngineersController::GetEngineerData(System.String)``
- ``EngineerVisualData EngineersController::GetEngineerVisualData(System.String)``
- ``EngineerData EngineersController::GetEngineerThatUnlocksAtArenaIndex(System.Int32)``
- ``System.Boolean TimedCastleBuildingController::CheckIfBuildingAtThatPosition(UnityEngine.Vector2)``
- ``System.Boolean TimedCastleBuildingController::CheckIfUpgradingAtThatPosition(UnityEngine.Vector2)``

### Ordered measurements

The fixed state-machine cohort contains 124 void MoveNext methods (3,587 pads)
and nine iterator MoveNext methods (382 pads).

| Step on #177 control | Owned pads remaining | State-machine pads remaining | Additional clean state machines |
|---|---:|---:|---:|
| Prior continuation | 10,969 | 3,969 | 0 |
| Metadata helper, this fields and catch boundaries | 10,908 | 3,969 | 0 |
| Register the catch-entry stloc as a definition | 10,816 | 3,878 | 0 |
| Returning closures and absolute-store rejection | 10,816 | 3,878 | 0 |

The state-machine step removed 91 pad messages across five methods before the final
measurements. They retain other/unproven pads, so none becomes completely clean.
The intermediate implementation had 19 state-machine native catch proofs but the
emitter rejected every one: its local-definition check did not see the emitted
handler-entry stloc. The fix is local to EH emission.

| State machine | Pads before → after |
|---|---:|
| `System.Void Voodoo.Analytics.AnalyticsApi+<SendEvents>d__13::MoveNext()` | 55 → 43 |
| `System.Void Voodoo.Sauce.Privacy.PrivacyManager+<OpenCmpPrivacySettings>d__40::MoveNext()` | 20 → 2 |
| `System.Void Voodoo.Sauce.Privacy.PrivacyManager+<SendConsent>d__58::MoveNext()` | 32 → 15 |
| `System.Void Voodoo.Sauce.Privacy.PrivacyManager+<UpdateConsent>d__54::MoveNext()` | 38 → 2 |
| `System.Void Voodoo.Sauce.Internal.StoreUtility.AndroidAppInfo+<GetAppUpdateStatus>d__5::MoveNext()` | 10 → 2 |

The final corpus adds real catch clauses in 14 owned methods and removes 153 pad
messages beyond round 2. It adds no further completely clean method; the overall
PR still makes 330 owned methods clean. Returning closures are covered by synthetic
checks but add zero native finally proofs on this corpus.

### Tests and ILVerify

- Release `net10.0` build: success, 13 existing warnings. `netstandard2.0` was left alone.
- Full rebased Core.Tests: **1205/1205**.
- LibCpp2ILTests: **12/12**; JitOracle.Tests: **9/9**.
- The full Core run includes the 36 EH cases and three new FrameStructFieldRead cases.
  EH cases include serialized-assembly execution through the real emitter.
- In the prior continuation, disabling catch-local registration and returning-closure
  continuation made six regression cases fail; restoring the changes passed them.
- Both audits: **170,144 valid**, **416 invalid**,
  7,714 partial/no-body entries. **0 status transitions**,
  including **0 valid→invalid**. The broader Bootstrap reachability gate remains
  blocked at 29/29 in both scans; scan's nonzero exit is not an ILVerify regression.

### Additional native/IL review

The 16 finally examples in the checked-in report were checked again against their
ARM64 disassembly and the new serialized IL. Nine bodies change with #180: four
CastleMaker methods, LevelCostTable.RebuildIndex, both MatchTelemetryTracker payload
methods, AdnDictionaryConverter.ConvertValues and TransactionDebugUI.PopulateValues.
The other seven bodies are unchanged. In all 16, each get_Current is unreachable
from normal entry without passing MoveNext on the same enumerator. Each finally
still calls Dispose on that enumerator and ends in endfinally. The sequence of
other managed calls is unchanged. The pre-loop Current copies disappear in the
nine corrected bodies; their loop-body consumers read the fresh value.

For example, GetDecorationsAtPosition has native MoveNext at `3E57278`, a false-exit
test at `3E5727C`, and the Current reload from `[SP+0x30]` at `3E57280`. Its emitted
MoveNext is IL_00B3, Current is IL_00C5/IL_00D7, and Dispose is IL_029A. The try spans
IL_00AE–IL_0296. RebuildIndex similarly moves Current from the pre-loop copy to
IL_008E after MoveNext at IL_007C, preserving Dispose at IL_01E8.

All 14 typed-catch bodies from round 3 are unchanged after this rebase. Their
original ARM64/LSDA review remains applicable.
Every type-test mismatch rewraps/propagates the original exception. Metadata global
`81AAA48` points to the usage at `839E900`, which resolves to `System.Exception`;
the already-recognized metadata-inline helper supplies that class to the predicate.
These addresses are evidence for r241 only.

| Method | Entry | Native handler behavior / emitted catch |
|---|---|---|
| `Voodoo.ADN.Internal.AdnAdsSignalsCollector::UpdateAdLoadedInfo` | `0x3a562c0` | Empty managed handler; leave to existing void return |
| `Voodoo.ADN.Internal.AdnAdsSignalsCollector::UpdateAdCloseInfo` | `0x3a56c74` | Empty managed handler; leave to existing void return |
| `Voodoo.ADN.Internal.AdnSignalsHelper::SaveAdsSession` | `0x3a57640` | Empty managed handler; leave to existing void return |
| `Voodoo.ADN.Internal.AdnSignalsHelper::SaveAdsRevenue` | `0x3a57734` | Empty managed handler; leave to existing void return |
| `Voodoo.ADN.Internal.AdnSignalsHelper::SaveAttributionData` | `0x3a58a6c` | Empty managed handler; leave to existing void return |
| `Voodoo.ADN.Internal.AdnSignalsHelper::SaveAdsCount` | `0x3a57828` | Empty managed handler; leave to existing void return |
| `Voodoo.Sauce.Internal.Analytics.BaseAnalyticsEvent::Track` | `0x39d2ed4` | LogEventExceptionInDebugger(this, caught object); leave |
| `Voodoo.Analytics.AnalyticsApi+<SendEvents>d__13::MoveNext` | `0x39833c0` | State = -2; address of builder; SetException with the caught object; leave to void epilogue |
| `Voodoo.Sauce.Privacy.PrivacyManager+<OpenCmpPrivacySettings>d__40::MoveNext` | `0x3aff05c` | State = -2; address of builder; SetException with the caught object; leave to void epilogue |
| `Voodoo.Sauce.Privacy.PrivacyManager+<SendConsent>d__58::MoveNext` | `0x3b00250` | State = -2; address of builder; SetException with the caught object; leave to void epilogue |
| `Voodoo.Sauce.Privacy.PrivacyManager+<UpdateConsent>d__54::MoveNext` | `0x3b019ac` | State = -2; address of builder; SetException with the caught object; leave to void epilogue |
| `Voodoo.Sauce.Internal.StoreUtility.AndroidAppInfo+<GetAppUpdateStatus>d__5::MoveNext` | `0x3b1bcf0` | State = -2; address of builder; SetException with the caught object; leave to void epilogue |
| `TrustedTimeService::FireFetchFailed` | `0x3f324c0` | Empty managed handler; leave to existing void return |
| `TrustedTimeService::ApplyNewTrustedTime` | `0x3f325e0` | Empty managed handler; leave to existing void return |

The five async SetException calls are at `3983D2C`, `3AFF3A4`, `3B00824`,
`3B01FBC` and `3B1BF2C`. Each follows the four-byte state-field store of -2 and
passes the same saved exception to the builder at this + 8. SetResult remains
outside its catch range. Native stack exception-record bookkeeping is discarded
only after its address and value are known. Unknown index values still refuse proof.

`UpdateAdCloseInfo` illustrates why pad counts are not recovered-body counts: its
emitted try is only IL_0913–IL_091A, the reachable protected unit. Dropped native
ranges do not become an invented larger try. Its other diagnostics remain.

## Gaps

The >50% target is **not met**. Owned pad messages fall by 4,721/15,537
(**30.4%**), with **10,816** remaining; the target is at most 7,768.
The user authorized merging this verified slice and continuing toward that target
in a follow-up PR. 557 owned methods retain pads, including
111 pad-only methods.

| Remaining coverage | Methods | Remaining pad messages |
|---|---:|---:|
| No native proof | 393 | 6,844 |
| All native pads proven, IL region refused | 78 | 1,464 |
| Mixed proven/unproven pads | 86 | 2,508 |

Native finally proofs still cover 7,084 pads. Typed catches prove 454 more,
for a union of 7,538; 2,817 proven pads remain
unmaterialized. All 1,019 native proof summaries match the previous branch output. A proof can cover more native sites than survive in emitted IL.

### Why previously proven finally pads are refused

For the 136-method round-2 cohort, assign each method its first observed refusal
in the table order below (a method may also have later independent refusals).
Counts of proven remaining pads refer to the original 2,516-pad backlog, so they
are not a claim that one guard accounts for all pads in a mixed method.

| First refusal | Methods | Previously proven pads still awaiting IL |
|---|---:|---:|
| No reachable emitted seed | 62 | 1,209 |
| Unusable or unequal cleanup IL | 22 | 713 |
| Handler local not definitely assigned | 13 | 153 |
| Protected CFG boundary | 25 | 437 |
| Shared cleanup incoming edge | 1 | 4 |
| Only an unproven remainder | 13 | 0 |

The top two causes are unchanged in kind. `CastleMaker.Build` has no reachable
emitted protected unit for its candidates. `StoreController.OpenSection` still has
a diagnostic and zero-initialized substitute receiver in its emitted Dispose copy.
Neither is fixed by weakening a region check. `CastleMaker.BuildGridAuto` still has
an uncovered List constructor. The catch-entry-local defect was the independently
fixable emission gap and was fixed here.

### Remaining shapes and lane boundaries

- The 133 state-machine cohort retains 3,878 pads: 3,496 in async methods and 382
  in iterators. Only five async methods gain emitted catch clauses; iterator
  state-guard/Dispose dispatch still lacks an equivalent normal cleanup proof.
  Native catch proofs exist in 19 of the 133 methods. Other pads need unknown
  exception-stack indices, captured receiver/return merges or additional CFG proofs.
- `Bootstrap.<InitializeVoodooLive>d__21.MoveNext` and Pvp `RunAsync` call specialized
  native builder bodies absent from MethodsByAddress and pass null MethodInfo.
  The targets at `398913C`/`398907C` cannot be renamed SetException from the name of
  the state-machine field. The normal path has the same unresolved-call limitation.
  A generic SetException with an exact MethodInfo and matching field type is proven
  in `PlayerProfileFetcher.TryFetchProfileAsync`, but its full IL region is refused.
- The global behind the offset-16 class load is identified: GOT `81AAA10` contains
  `8719180`, and exported `il2cpp_get_corlib` reaches a body at `381A72C` that loads
  `[8719180]`. It is the defaults table. This is consistent with the Unity 6 object_class position;
  the existing `Unity6PrimitiveDefaultsClass` seeding begins at byte_class (+0x18)
  and returns no type for +0x10. Metadata usages also provide no type at the BSS
  slot. This continuation adds no guessed class identity or new defaults-table
  recognizer. Catch(Object), non-void fallback merges and the affected 23 straight
  prefixes remain gaps. By contrast, the separate System.Exception metadata usage
  above supplies a concrete type proof and now yields real catches.
- Returning closures now resume the caller's proof; none adds a native finally
  proof in r241. Unknown cleanup arguments and side effects still refuse proof.
- `Simplifier.cs`, `LocalVariables.cs`, `MetadataResolver.cs`, `ArrayRecovery.cs`,
  `DeadCodeEliminator.cs`, enumerator emission and block-operation emission were
  not edited by the EH branch. The previously reported frame-cell Current defect is
  now addressed by merged #180 and included in both measured builds. Its own report
  still lists one unexamined enumerator pattern; this recheck does not claim to
  prove every foreach method's behavior.
- No negative LSDA selectors or undecodable action chains were observed in these
  1,019 methods. Managed filters and fault blocks remain unsupported; iterator
  unwind dispatch is not relabelled as finally without a normal-path equivalence.

## diag_families.py

### Control: all game-owned

```text
scope: Assembly-CSharp, CastleClashers.Core, CastleClashers.Game, CastleClashers.Internal.Services, CastleClashers.Internal.UI, CastleClashers.Rules, CastleClashers.Rules.Client, CastleClashers.SDKGlue, CastleClashers.VoodooTune, Ranked
game-owned methods with diagnostics: 4274
methods naming a canonical shared-generic type: 170

| family | methods | sole | occurrences |
|---|---:|---:|---:|
| type: no legal conversion | 1581 | 554 | 6462 |
| other | 1389 | 555 | 16422 |
| memory: unmanaged load | 1230 | 313 | 6247 |
| dataflow: undefined local | 976 | 171 | 2459 |
| type: synthetic default in operand slot | 709 | 152 | 1762 |
| lift: unimplemented or unrecoverable op | 660 | 106 | 2284 |
| call: unresolved target | 619 | 40 | 1122 |
| memory: unmanaged store dropped | 535 | 117 | 2610 |
| meta: native metadata pointer as value | 280 | 15 | 1102 |
| access: inaccessible member | 205 | 30 | 560 |
| call: indirect call | 179 | 8 | 293 |
| dataflow: zero on phi edge | 133 | 2 | 415 |
| call: hidden generic argument | 127 | 57 | 187 |
| dataflow: non-empty stack at end | 70 | 1 | 70 |
| dataflow: receiver not recovered | 55 | 12 | 106 |
| dataflow: undefined local, float lane V1-V7 | 32 | 2 | 49 |
| /Exception landing pad at/ | 1019 | 441 | 15537 |

greedy fix order (methods cleared at each step):
  +  555 ->   555  other
  +  605 ->  1160  type: no legal conversion
  +  507 ->  1667  memory: unmanaged load
  +  301 ->  1968  lift: unimplemented or unrecoverable op
  +  364 ->  2332  type: synthetic default in operand slot
  +  383 ->  2715  dataflow: undefined local
  +  383 ->  3098  memory: unmanaged store dropped
  +  324 ->  3422  call: unresolved target
  +  177 ->  3599  meta: native metadata pointer as value
  +  150 ->  3749  access: inaccessible member

top unresolved call targets (of 157):
    259  0x37C2D44
    171  0x37FC3B0
     69  0x32D69D0
     55  0x3C29C4C
     48  0x37C2A9C
     37  0x32D7C3C
     35  0x3988F84
     29  0x50921DC
     21  0x38E44AC
     15  0x37C2AA0
     15  0x52BD3BC
     14  0x3C29C08
     13  0x32D50FC
     13  0x37C2B6C
     12  0x39295B4
```

### Control: CastleClashers.Game

```text
scope: CastleClashers.Game
game-owned methods with diagnostics: 2673
methods naming a canonical shared-generic type: 105

| family | methods | sole | occurrences |
|---|---:|---:|---:|
| type: no legal conversion | 1180 | 370 | 5431 |
| other | 754 | 296 | 10356 |
| memory: unmanaged load | 707 | 199 | 3709 |
| dataflow: undefined local | 638 | 80 | 1677 |
| lift: unimplemented or unrecoverable op | 502 | 67 | 1786 |
| type: synthetic default in operand slot | 480 | 79 | 1355 |
| memory: unmanaged store dropped | 446 | 104 | 2214 |
| call: unresolved target | 375 | 18 | 672 |
| access: inaccessible member | 140 | 22 | 457 |
| meta: native metadata pointer as value | 137 | 4 | 585 |
| dataflow: zero on phi edge | 102 | 1 | 369 |
| call: indirect call | 82 | 1 | 123 |
| call: hidden generic argument | 70 | 20 | 97 |
| dataflow: receiver not recovered | 44 | 9 | 73 |
| dataflow: non-empty stack at end | 28 | 0 | 28 |
| dataflow: undefined local, float lane V1-V7 | 22 | 2 | 30 |
| /Exception landing pad at/ | 574 | 260 | 9865 |

greedy fix order (methods cleared at each step):
  +  370 ->   370  type: no legal conversion
  +  331 ->   701  other
  +  275 ->   976  memory: unmanaged load
  +  218 ->  1194  lift: unimplemented or unrecoverable op
  +  242 ->  1436  type: synthetic default in operand slot
  +  219 ->  1655  dataflow: undefined local
  +  324 ->  1979  memory: unmanaged store dropped
  +  208 ->  2187  call: unresolved target
  +   90 ->  2277  access: inaccessible member
  +   83 ->  2360  meta: native metadata pointer as value

top unresolved call targets (of 112):
    177  0x37C2D44
     72  0x37FC3B0
     53  0x32D69D0
     33  0x3988F84
     29  0x50921DC
     21  0x32D7C3C
     15  0x52BD3BC
     14  0x3C29C08
     13  0x38E44AC
     13  0x37C2B6C
     10  0x446DFD4
     10  0x398925C
      9  0x446E560
      9  0x3BAD7C4
      7  0x3C01928
```

### Branch: all game-owned

```text
scope: Assembly-CSharp, CastleClashers.Core, CastleClashers.Game, CastleClashers.Internal.Services, CastleClashers.Internal.UI, CastleClashers.Rules, CastleClashers.Rules.Client, CastleClashers.SDKGlue, CastleClashers.VoodooTune, Ranked
game-owned methods with diagnostics: 3944
methods naming a canonical shared-generic type: 170

| family | methods | sole | occurrences |
|---|---:|---:|---:|
| type: no legal conversion | 1581 | 577 | 6452 |
| memory: unmanaged load | 1230 | 322 | 6246 |
| dataflow: undefined local | 976 | 176 | 2459 |
| other | 936 | 225 | 11701 |
| type: synthetic default in operand slot | 709 | 170 | 1762 |
| lift: unimplemented or unrecoverable op | 660 | 108 | 2284 |
| call: unresolved target | 619 | 40 | 1122 |
| memory: unmanaged store dropped | 535 | 120 | 2610 |
| meta: native metadata pointer as value | 280 | 15 | 1102 |
| access: inaccessible member | 205 | 30 | 560 |
| call: indirect call | 179 | 8 | 293 |
| dataflow: zero on phi edge | 133 | 2 | 415 |
| call: hidden generic argument | 127 | 59 | 187 |
| dataflow: non-empty stack at end | 70 | 1 | 70 |
| dataflow: receiver not recovered | 55 | 12 | 106 |
| dataflow: undefined local, float lane V1-V7 | 32 | 2 | 49 |
| /Exception landing pad at/ | 557 | 111 | 10816 |

greedy fix order (methods cleared at each step):
  +  577 ->   577  type: no legal conversion
  +  351 ->   928  memory: unmanaged load
  +  409 ->  1337  other
  +  301 ->  1638  lift: unimplemented or unrecoverable op
  +  364 ->  2002  type: synthetic default in operand slot
  +  383 ->  2385  dataflow: undefined local
  +  383 ->  2768  memory: unmanaged store dropped
  +  324 ->  3092  call: unresolved target
  +  177 ->  3269  meta: native metadata pointer as value
  +  150 ->  3419  access: inaccessible member

top unresolved call targets (of 157):
    259  0x37C2D44
    171  0x37FC3B0
     69  0x32D69D0
     55  0x3C29C4C
     48  0x37C2A9C
     37  0x32D7C3C
     35  0x3988F84
     29  0x50921DC
     21  0x38E44AC
     15  0x37C2AA0
     15  0x52BD3BC
     14  0x3C29C08
     13  0x32D50FC
     13  0x37C2B6C
     12  0x39295B4
```

### Branch: CastleClashers.Game

```text
scope: CastleClashers.Game
game-owned methods with diagnostics: 2442
methods naming a canonical shared-generic type: 105

| family | methods | sole | occurrences |
|---|---:|---:|---:|
| type: no legal conversion | 1180 | 387 | 5423 |
| memory: unmanaged load | 707 | 204 | 3708 |
| dataflow: undefined local | 638 | 83 | 1677 |
| lift: unimplemented or unrecoverable op | 502 | 67 | 1786 |
| type: synthetic default in operand slot | 480 | 88 | 1355 |
| memory: unmanaged store dropped | 446 | 107 | 2214 |
| other | 433 | 65 | 7150 |
| call: unresolved target | 375 | 18 | 672 |
| access: inaccessible member | 140 | 22 | 457 |
| meta: native metadata pointer as value | 137 | 4 | 585 |
| dataflow: zero on phi edge | 102 | 1 | 369 |
| call: indirect call | 82 | 1 | 123 |
| call: hidden generic argument | 70 | 22 | 97 |
| dataflow: receiver not recovered | 44 | 9 | 73 |
| dataflow: non-empty stack at end | 28 | 0 | 28 |
| dataflow: undefined local, float lane V1-V7 | 22 | 2 | 30 |
| /Exception landing pad at/ | 247 | 29 | 6659 |

greedy fix order (methods cleared at each step):
  +  387 ->   387  type: no legal conversion
  +  221 ->   608  memory: unmanaged load
  +  199 ->   807  lift: unimplemented or unrecoverable op
  +  212 ->  1019  type: synthetic default in operand slot
  +  186 ->  1205  other
  +  219 ->  1424  dataflow: undefined local
  +  324 ->  1748  memory: unmanaged store dropped
  +  208 ->  1956  call: unresolved target
  +   90 ->  2046  access: inaccessible member
  +   83 ->  2129  meta: native metadata pointer as value

top unresolved call targets (of 112):
    177  0x37C2D44
     72  0x37FC3B0
     53  0x32D69D0
     33  0x3988F84
     29  0x50921DC
     21  0x32D7C3C
     15  0x52BD3BC
     14  0x3C29C08
     13  0x38E44AC
     13  0x37C2B6C
     10  0x446DFD4
     10  0x398925C
      9  0x446E560
      9  0x3BAD7C4
      7  0x3C01928
```

## Game-owned methods made diagnostic-free

- `CastleClashers.Rules`: ``CastleClashers.Protobuf.CCInventoryState CastleClashers.Rules.Engine::NewState()``
- `CastleClashers.Game`: ``System.Void SDFSpriteGenerator_SR::OnDrawGizmosSelected()``
- `CastleClashers.Game`: ``System.Void RecordingObjectDisabler::DisableObjects()``
- `CastleClashers.Game`: ``System.Void LevelCostTable::RebuildIndex()``
- `CastleClashers.Game`: ``System.Int32 LevelCostTable::GetTotalPiecesForMaxLevel()``
- `CastleClashers.Game`: ``System.Int32 CastleBuildingController::HowManyUpgradable()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<DecorationSO> CastleMaker::GetDecorationsAtPosition(UnityEngine.Vector2)``
- `CastleClashers.Game`: ``DecorationRoofSO CastleMaker::GetRoofDecorationAtPosition(UnityEngine.Vector2)``
- `CastleClashers.Game`: ``DecorationFoundataionSO CastleMaker::GetAnyFoundationDecoration()``
- `CastleClashers.Game`: ``System.Boolean CastleMaker::TryApplyFetchedDecorations(CastleClashers.HumanLikeBots.HumanLikeBotProfile)``
- `CastleClashers.Game`: ``System.Void CastleMaker::ApplyPvpOpponentFoundations(CastleClashers.HumanLikeBots.FetchedPlayerProfile)``
- `CastleClashers.Game`: ``System.Void CastleMaker::ApplyPvpOpponentDecorations(CastleClashers.HumanLikeBots.FetchedPlayerProfile)``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<FoundationData> CastleMaker::MirrorFoundationPositions(System.Collections.Generic.List`1<FoundationData>, System.Int32)``
- `CastleClashers.Game`: ``UnityEngine.Vector2 CastleManager::GetMinMaxY()``
- `CastleClashers.Game`: ``System.Void CastleMovement::TriggerParticleWithDelay()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<FoundationData> CastleLoadoutDataFactory::ConvertFetchedFoundations(System.Collections.Generic.List`1<CastleClashers.HumanLikeBots.FetchedFoundationData>)``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<DecorationData> CastleLoadoutDataFactory::ConvertFetchedDecorations(System.Collections.Generic.List`1<CastleClashers.HumanLikeBots.FetchedDecorationData>)``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<ArenaReward> ArenaProgressionController::GetRewardsBetweenTrophies(System.Int32, System.Int32)``
- `CastleClashers.Game`: ``System.Int32 ArenaProgressionController::NumberOfReceivedRewardsInArena(System.Int32)``
- `CastleClashers.Game`: ``System.Void BotEmoteController::SetFixedEmotes(System.Collections.Generic.List`1<EmoteData>)``
- `CastleClashers.Game`: ``System.Single CardController::GetAverageLevelOfEquippedCards()``
- `CastleClashers.Game`: ``System.Single CardController::GetAverageLevelCards()``
- `CastleClashers.Game`: ``CardData CardController::UnequipUnitOnLastEquippedPosition()``
- `CastleClashers.Game`: ``System.Void CardController::UnlockCardFromArena(System.Int32)``
- `CastleClashers.Game`: ``System.Void CardController::UnlockSpecificCard(CardData)``
- `CastleClashers.Game`: ``CardData CardController::GetUnlockedUnequippedCardWithHighestLevel()``
- `CastleClashers.Game`: ``System.Boolean CardController::CanUpgradeAny(System.Int32&)``
- `CastleClashers.Game`: ``System.Int32 CardController::GetNumberOfUpgradesAvailable()``
- `CastleClashers.Game`: ``System.String ChestOpenResult::ToString()``
- `CastleClashers.Game`: ``System.Collections.Generic.Dictionary`2<System.String, System.Int32> ChestController::FilterMaxedCards(System.Collections.Generic.Dictionary`2<System.String, System.Int32>)``
- `CastleClashers.Game`: ``Chests.CurrencyChestData CurrencyChestController::GetChestData(Chests.CurrencyChestType, Chests.CurrencyChestTier)``
- `CastleClashers.Game`: ``System.Int32 DeckController::GetNumberOfDeckSlotsAvailable(System.Int32, System.Int32)``
- `CastleClashers.Game`: ``System.Single MatchTelemetryTrackerController::ComputeDefenderUnitDamage(PlayingSide)``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<System.Collections.Generic.Dictionary`2<System.String, System.Object>> MatchTelemetryTrackerController::BuildUnitsPayload(System.Collections.Generic.List`1<Agent>, PlayingSide)``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<System.Collections.Generic.Dictionary`2<System.String, System.Object>> MatchTelemetryTrackerController::BuildUnitsEndStatePayload(System.Collections.Generic.List`1<Agent>, PlayingSide)``
- `CastleClashers.Game`: ``System.Collections.Generic.Dictionary`2<System.String, System.Object> MatchTelemetryTrackerController::BuildWheelStartPayload(System.String, System.Int32)``
- `CastleClashers.Game`: ``CastleClashers.PvP.UnitHit[] PoisonCloudsController::CollectPendingTickHits(System.Int32)``
- `CastleClashers.Game`: ``System.Void PoisonCloudsController::TickAndClean(System.Int32, PlayingSide)``
- `CastleClashers.Game`: ``System.Boolean ProfileInfoController::IsBundleInPremiumPacksAB(System.Collections.Generic.List`1<System.String>)``
- `CastleClashers.Game`: ``System.Boolean ProfileInfoController::DidPurchaseAnyBundle(System.Collections.Generic.List`1<System.String>)``
- `CastleClashers.Game`: ``System.Int32 ProfileInfoController::CalculateHighestForgeUnlockLevel()``
- `CastleClashers.Game`: ``ProfileIconData ProfileInfoController::GetProfileIconData(System.String)``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<ProfileIconData> ProfileInfoController::GetPossibleAvatars(System.Int32, System.Int32)``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<ProfileIconData> ProfileInfoController::GetUnlockedIcons()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<ProfileIconData> ProfileInfoController::GetUncollectedIcons()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<ProfileIconData> ProfileInfoController::GetUncollectedPremiumIcons()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<ProfileIconData> ProfileInfoController::GetUncollectedNonPremiumIcons()``
- `CastleClashers.Game`: ``EmoteData ProfileInfoController::GetEmoteData(System.String)``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<EmoteData> ProfileInfoController::GetEquippedEmotes()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<EmoteData> ProfileInfoController::GetUnlockedEmotes()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<EmoteData> ProfileInfoController::GetUnlockedButNotEquippedEmotes()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<EmoteData> ProfileInfoController::GetUncollectedEmotes()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<EmoteData> ProfileInfoController::GetUncollectedPremiumEmotes()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<EmoteData> ProfileInfoController::GetUncollectedNonPremiumEmotes()``
- `CastleClashers.Game`: ``System.Void ProfileInfoController::HandleEmoteEquipSlots()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<EmoteData> ProfileInfoController::GetDefaultEmotes()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<EmoteData> ProfileInfoController::GetPossibleEmotes(System.Int32, System.Int32, System.Boolean)``
- `CastleClashers.Game`: ``BannerData ProfileInfoController::GetBannerData(System.String)``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<BannerData> ProfileInfoController::GetPossibleBanners(System.Int32, System.Int32, System.Boolean)``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<BannerData> ProfileInfoController::GetUnlockedBanners()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<BannerData> ProfileInfoController::GetUncollectedBanners()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<BannerData> ProfileInfoController::GetUncollectedPremiumBanners()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<BannerData> ProfileInfoController::GetUncollectedNonPremiumBanners()``
- `CastleClashers.Game`: ``BundleInfo ProfileInfoController::GetBundleInfo(System.String)``
- `CastleClashers.Game`: ``System.Void VoodoDebuggerController::<UnlockAllUnits>b__48_0()``
- `CastleClashers.Game`: ``System.Void CurrencyController::UpdateAllShownToActual()``
- `CastleClashers.Game`: ``CurrencyVisualData CurrencyController::GetCurrencyVisualData(CurrencyType)``
- `CastleClashers.Game`: ``EngineerData EngineersController::GetEngineerData(System.String)``
- `CastleClashers.Game`: ``EngineerVisualData EngineersController::GetEngineerVisualData(System.String)``
- `CastleClashers.Game`: ``EngineerData EngineersController::GetEngineerThatUnlocksAtArenaIndex(System.Int32)``
- `CastleClashers.Game`: ``System.Void EnviromentalEffectsController::StopAllEffects()``
- `CastleClashers.Game`: ``System.Void FoundationUIController::ReconcilePlacedFoundations()``
- `CastleClashers.Game`: ``DecorationFoundataionSO FoundationUIController::GetAnyFoundationDecoration()``
- `CastleClashers.Game`: ``System.Void RewardedAdController::OnInitialized()``
- `CastleClashers.Game`: ``System.Void AvatarsShopSection::SetDataLegacy()``
- `CastleClashers.Game`: ``System.Void BannersShopSection::SetDataLegacy()``
- `CastleClashers.Game`: ``System.Void EmotesShopSection::SetDataLegacy()``
- `CastleClashers.Game`: ``System.Void IngameUnitsGridHandler::SetUnitKOed(System.String)``
- `CastleClashers.Game`: ``System.Void IngameUnitsGridHandler::StopAllItemAnimations()``
- `CastleClashers.Game`: ``System.Void IngameUnitsGridHandler::Reset()``
- `CastleClashers.Game`: ``System.Void SocialInteractionsHandler::TogglePlayersHolder(System.Boolean)``
- `CastleClashers.Game`: ``System.Void ChainOfferPopUp::ClearStepItems()``
- `CastleClashers.Game`: ``System.Boolean ChainOfferPopUp::StepHasChestReward(ChainOffer.ChainOfferStepData)``
- `CastleClashers.Game`: ``ArenaRewardsData+ArenaRewardSet ArenaRewardsData::GetArenaRewardSetForArena(System.Int32)``
- `CastleClashers.Game`: ``System.Void QuestController::SaveDailyQuests()``
- `CastleClashers.Game`: ``System.Void QuestController::SaveWeeklyQuests()``
- `CastleClashers.Game`: ``System.Void QuestController::LoadDailyQuests()``
- `CastleClashers.Game`: ``System.Void QuestController::LoadWeeklyQuests()``
- `CastleClashers.Game`: ``QuestDefinition QuestController::GetQuestDefinition(QuestType)``
- `CastleClashers.Game`: ``System.Int32 QuestController::GetUnclaimedCompletedQuestAmount()``
- `CastleClashers.Game`: ``System.Boolean QuestController::IsQuestInstanceWeekly(QuestInstance)``
- `CastleClashers.Game`: ``System.Boolean QuestController::CanUseUnitLevelUpQuest(System.Int32)``
- `CastleClashers.Game`: ``System.Boolean QuestController::CanUseForgeLevelUpQuest(System.Int32)``
- `CastleClashers.Game`: ``QuestGoalAndRewardEntry QuestDefinition::GetGoalsAndRewardsEntry(QuestDifficulty)``
- `CastleClashers.Game`: ``System.Void QuestsProgressListener::BattleWon()``
- `CastleClashers.Game`: ``System.Void QuestsProgressListener::CheckUniqueList(QuestType, System.String)``
- `CastleClashers.Game`: ``System.Void FMUnitsGridHandler::StopAllItemAnimations()``
- `CastleClashers.Game`: ``System.Void FMUnitsGridHandler::Reset()``
- `CastleClashers.Game`: ``System.Void CurrencyParticlePanel::ClearParticleImages()``
- `CastleClashers.Game`: ``System.Void ForgeController::SavePastPassRewards()``
- `CastleClashers.Game`: ``System.Void ForgeController::SaveCollectedRewards()``
- `CastleClashers.Game`: ``System.Void ForgeExpParticlePanel::ClearParticleImages()``
- `CastleClashers.Game`: ``ForgeRewardsData ForgeRewardsManager::GetRewardsDataBasedOnLevelThreshold(System.Int32)``
- `CastleClashers.Game`: ``System.Void UnlockForgeRewardItem::SetData(System.Int32, ForgeRewardType, System.Boolean)``
- `CastleClashers.Game`: ``System.Void InfiniteScrollRect::UpdateCurrentPool()``
- `CastleClashers.Game`: ``HelperItemSO UtilitiesController::GetHelperItemData(System.String)``
- `CastleClashers.Game`: ``System.Int32 UtilitiesController::CalculateHighestForgeUnlockLevel()``
- `CastleClashers.Game`: ``WheelData UtilitiesController::GetWheelData(System.String)``
- `CastleClashers.Game`: ``HelperItemSO UtilitiesController::GetEquippedOffensiveHelperItemData()``
- `CastleClashers.Game`: ``HelperItemSO UtilitiesController::GetEquippedDefensiveHelperItemData()``
- `CastleClashers.Game`: ``WheelData UtilitiesController::GetEquippedWheelData()``
- `CastleClashers.Game`: ``System.Void UtilitiesController::UnlockNewlyAddedUtilities(System.Int32)``
- `CastleClashers.Game`: ``HelperItemSaveData UtilitiesController::GetHelperItemSaveData(System.String)``
- `CastleClashers.Game`: ``WheelSaveData UtilitiesController::GetWheelSaveData(System.String)``
- `CastleClashers.Game`: ``System.Boolean UtilitiesController::IsHelperItemDiscovered(System.String)``
- `CastleClashers.Game`: ``System.Boolean UtilitiesController::IsHelperItemUnlocked(System.String)``
- `CastleClashers.Game`: ``System.Boolean UtilitiesController::AnyLevelsAvailableForHelperItem(System.String)``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<System.String> UtilitiesController::GetPossibleHelperItemIdsForOpponent(HelperItemType)``
- `CastleClashers.Game`: ``System.Void UtilitiesController::SaveHelperItemsData()``
- `CastleClashers.Game`: ``System.Boolean UtilitiesController::AreWheelsDiscovered(System.String)``
- `CastleClashers.Game`: ``System.Boolean UtilitiesController::IsWheelUnlocked(System.String)``
- `CastleClashers.Game`: ``System.Boolean UtilitiesController::AnyLevelsAvailableForWheel(System.String)``
- `CastleClashers.Game`: ``System.Void UtilitiesController::SaveWheelsData()``
- `CastleClashers.Game`: ``System.Boolean UtilitiesController::AnyUpgradesAvailableForHelperItems(HelperItemType)``
- `CastleClashers.Game`: ``System.Boolean UtilitiesController::AnyUpgradesAvailableForWheels()``
- `CastleClashers.Game`: ``System.Int32 UtilitiesController::GetNumberOfUpgradesAvailable()``
- `CastleClashers.Game`: ``System.Int32 UtilitiesController::GetTotalNumberOfUpgradesYetToGet()``
- `CastleClashers.Game`: ``System.Void UtilitiesTabSwitcher::OnTabSelected(System.Int32)``
- `CastleClashers.Game`: ``System.Void UtilitiesTabSwitcher::ToggleNotifyDotOnTab(System.Int32, System.Boolean)``
- `CastleClashers.Game`: ``System.Void CosmeticsTabSwitcher::OnTabSelected(System.Int32)``
- `CastleClashers.Game`: ``System.Void CosmeticsTabSwitcher::ToggleNotifyDotOnTab(System.Int32, System.Boolean)``
- `CastleClashers.Game`: ``System.Void PanelController::OpenSinglePanel(System.Type)``
- `CastleClashers.Game`: ``System.Void PanelController::OpenSinglePanelWithoutFade(System.Type)``
- `CastleClashers.Game`: ``System.Void PanelController::CloseSinglePanel(System.Type, System.Single)``
- `CastleClashers.Game`: ``System.Void ArenaProgressionPanel::PrepareArenas()``
- `CastleClashers.Game`: ``System.Void ArenaProgressionPanel::SetArenaDatas()``
- `CastleClashers.Game`: ``System.Void ArenaProgressionPanel::SetNextBigUnlockData(NextBigUnlockData)``
- `CastleClashers.Game`: ``System.Void ChestOpeningPanel::DetachEvents()``
- `CastleClashers.Game`: ``System.Void ChestOpeningPanel::ClearRewardUnitItems()``
- `CastleClashers.Game`: ``System.Void EmotesSelectionPanel::EquipProcess(EmoteData)``
- `CastleClashers.Game`: ``System.Void EmotesSelectionPanel::StopEquippingProcess()``
- `CastleClashers.Game`: ``System.Void ForgePassRewardsAlertPanel::Init()``
- `CastleClashers.Game`: ``System.Void ForgePassRewardsAlertPanel::SetData()``
- `CastleClashers.Game`: ``System.Void MenuPanel::Init()``
- `CastleClashers.Game`: ``System.Void MenuPanel::UpdateShopButtonNotify()``
- `CastleClashers.Game`: ``System.Void NewProfileCosmeticPanel::SetDataEmotes(System.Collections.Generic.List`1<System.String>)``
- `CastleClashers.Game`: ``System.Void NewProfileCosmeticPanel::SetDataAvatars(System.Collections.Generic.List`1<System.String>)``
- `CastleClashers.Game`: ``System.Void NewProfileCosmeticPanel::SetDataBanners(System.Collections.Generic.List`1<System.String>)``
- `CastleClashers.Game`: ``System.Void NewProfileCosmeticPanel::ClearSpawnedCosmetics()``
- `CastleClashers.Game`: ``System.Void ProfileInfoPanel::EnableAutoLinkAndRestart()``
- `CastleClashers.Game`: ``System.Void TopBarPanel::SetCurrencySetup(CurrencySetupType)``
- `CastleClashers.Game`: ``UICurrencySetup TopBarPanel::GetCurrencySetup(CurrencySetupType)``
- `CastleClashers.Game`: ``System.Void TopBarPanelIAP::UpdateCurrencyFields()``
- `CastleClashers.Game`: ``System.Void UnitsPanel::EquipProcess(CardData)``
- `CastleClashers.Game`: ``System.Void UnitsPanel::StopEquippingProcess()``
- `CastleClashers.Game`: ``System.Void UnitsPanel::CheckWildCardsTutorial()``
- `CastleClashers.Game`: ``System.Void UtilitiesPanel::ToggleSelectedBorderOnCards(WheelData)``
- `CastleClashers.Game`: ``System.Void UtilitiesPanel::ToggleSelectedBorderOnCards(HelperItemSO)``
- `CastleClashers.Game`: ``System.Void CleanCockroachProjectile::OnDestroy()``
- `CastleClashers.Game`: ``System.Single RadialCarveGenerator::GetLastCarveRadius()``
- `CastleClashers.Game`: ``System.Boolean TimedCastleBuildingController::CheckIfBuildingAtThatPosition(UnityEngine.Vector2)``
- `CastleClashers.Game`: ``System.Boolean TimedCastleBuildingController::CheckIfUpgradingAtThatPosition(UnityEngine.Vector2)``
- `CastleClashers.Game`: ``System.Boolean TimedUnitsUpgradeController::CheckIfUpgrading(System.String)``
- `CastleClashers.Game`: ``TrainerData TrainersController::GetTrainerData(System.String)``
- `CastleClashers.Game`: ``TrainerVisualData TrainersController::GetTrainerVisualData(System.String)``
- `CastleClashers.Game`: ``TrainerData TrainersController::GetTrainerThatUnlocksAtArenaIndex(System.Int32)``
- `CastleClashers.Game`: ``System.Void RVButtonsController::OnInitialized()``
- `CastleClashers.Game`: ``System.Void RVButtonsController::UpdateNoRVBought()``
- `CastleClashers.Game`: ``System.Void RVButtonsController::UnsubscribeAllButtons()``
- `CastleClashers.Game`: ``System.Void RVButtonsController::ShowAllRVButtons()``
- `CastleClashers.Game`: ``System.Void RVButtonsController::ResetAllRVButtons()``
- `CastleClashers.Game`: ``System.Void SpecialOffer_StoreController::PopulateCards(System.Collections.Generic.List`1<CardValuePair>, UnityEngine.Transform)``
- `CastleClashers.Game`: ``System.Void UICurrencySetup::UpdateCurrencyFields()``
- `CastleClashers.Game`: ``System.Void UnitsController::InitUnitsOnBeginMatch()``
- `CastleClashers.Game`: ``System.Void UnitsController::DetermineEnemyUnitsToSpawn()``
- `CastleClashers.Game`: ``System.Single UnitsController::ComputeAverageDamage(System.Collections.Generic.List`1<Agent>)``
- `CastleClashers.Game`: ``System.Single UnitsController::ComputeAverageHealth(System.Collections.Generic.List`1<Agent>)``
- `CastleClashers.Game`: ``System.Void UnitsController::VampireHealAllUnits(PlayingSide, System.Single)``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<Agent> UnitsController::GetAllExposed(PlayingSide)``
- `CastleClashers.Game`: ``System.Void UnitsHolder::EnableAgentWithCardId(System.String)``
- `CastleClashers.Game`: ``System.Void UnitsHolder::EnableAgentByUnitData(UnitData)``
- `CastleClashers.Game`: ``System.Void UnitsHolder::SetAgentAnimationByUnitData(UnitData, System.Boolean)``
- `CastleClashers.Game`: ``System.Int32 WeeklyLeaderboardController::GetPlayerRank(System.Int32)``
- `CastleClashers.Game`: ``System.ValueTuple`2<System.Int32, System.Int32> WeeklyLeaderboardController::GetRewardAmountForRank(System.Int32)``
- `CastleClashers.Game`: ``UnityEngine.GameObject WorldSpaceUI::GetOrAssignIndicator(UnityEngine.GameObject)``
- `CastleClashers.Game`: ``ArenaData SOHolder::GetArenaDataByArenaIndex(System.Int32)``
- `CastleClashers.Game`: ``RarityDesign SOHolder::GetRarityDesign(RarityType)``
- `CastleClashers.Game`: ``System.Void VideoController::Awake()``
- `CastleClashers.Game`: ``Tournament.TournamentsData+SaveData Tournament.TournamentsData::ToSaveData()``
- `CastleClashers.Game`: ``Tournament.TournamentsData Tournament.TournamentsData::FromSaveData(Tournament.TournamentsData+SaveData)``
- `CastleClashers.Game`: ``RoyalBlessing.DailyRewardEntry RoyalBlessing.RoyalBlessingConfigSO::GetRewardForDay(System.Int32)``
- `CastleClashers.Game`: ``System.Boolean MonetizationEvents.MonetizationEventConfigBase::IsDateSpecificActiveNow(System.DateTime)``
- `CastleClashers.Game`: ``System.Int32 MonetizationEvents.MonetizationEventSchedulerConfig::GetRotationCycleDays()``
- `CastleClashers.Game`: ``System.Void MonetizationEvents.MonetizationEventController::InitializeScheduler()``
- `CastleClashers.Game`: ``System.Boolean MonetizationEvents.MonetizationEventController::IsEventRegistered(System.String)``
- `CastleClashers.Game`: ``System.Int32 ChainOffer.ChainOfferConfigSO::GetFreeStepsCount()``
- `CastleClashers.Game`: ``System.Int32 ChainOffer.ChainOfferConfigSO::GetPaidStepsCount()``
- `CastleClashers.Game`: ``ChainOffer.ChainOfferSaveData ChainOffer.ChainOfferData::ToSaveData()``
- `CastleClashers.Game`: ``System.Void ChainOffer.ChainOfferData::MigratePendingRewardTypeKeys()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<System.ValueTuple`2<ProfileIconData, System.Boolean>> EpiCoro.Internal.IAP.AvatarShopRotationController::GetCurrentShopAvatars()``
- `CastleClashers.Game`: ``System.Boolean EpiCoro.Internal.IAP.AvatarShopRotationController::HasUnownedItemsInCurrentRotation()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<System.ValueTuple`2<BannerData, System.Boolean>> EpiCoro.Internal.IAP.BannerShopRotationController::GetCurrentShopBanners()``
- `CastleClashers.Game`: ``System.Boolean EpiCoro.Internal.IAP.BannerShopRotationController::HasUnownedItemsInCurrentRotation()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<System.ValueTuple`2<EmoteData, System.Boolean>> EpiCoro.Internal.IAP.EmoteShopRotationController::GetCurrentShopEmotes()``
- `CastleClashers.Game`: ``System.Boolean EpiCoro.Internal.IAP.EmoteShopRotationController::HasUnownedItemsInCurrentRotation()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<System.ValueTuple`2<DecorationSO, System.Boolean>> EpiCoro.Internal.IAP.DecorationShopRotationController::GetCurrentShopDecorations()``
- `CastleClashers.Game`: ``System.Boolean EpiCoro.Internal.IAP.DecorationShopRotationController::HasUnownedItemsInCurrentRotation()``
- `CastleClashers.Game`: ``System.Void EpiCoro.Internal.IAP.BuyForgePass::GrantReward(UnityEngine.Transform)``
- `CastleClashers.Game`: ``System.Void EpiCoro.Internal.IAP.BuyUltimateUnitPack::GrantReward(UnityEngine.Transform)``
- `CastleClashers.Game`: ``System.Void EpiCoro.Internal.IAP.BuySpecialOffer::GrantReward(UnityEngine.Transform)``
- `CastleClashers.Game`: ``System.Void EpiCoro.Internal.IAP.IAPEventUIItem::GrantReward(System.Boolean)``
- `CastleClashers.Game`: ``System.Void EpiCoro.Internal.IAP.NoneConsumableIAPUIItem::TurnOffRotation()``
- `CastleClashers.Game`: ``System.Void EpiCoro.Internal.IAP.NoneConsumableIAPUIItem::DisableGameObjects()``
- `CastleClashers.Game`: ``System.Void EpiCoro.Internal.IAP.RVUIItem::OnPurchaseComplete(System.Boolean)``
- `CastleClashers.Game`: ``System.Void EpiCoro.Internal.IAP.StoreController::ResolveStoreNotificationDot()``
- `CastleClashers.Game`: ``System.Void EpiCoro.Internal.IAP.StoreController::TryRestorePremiumUnitCosmeticsIfPurchased()``
- `CastleClashers.Game`: ``System.Void EpiCoro.Internal.IAP.CurrencyPurchaseUIItem::OnPurchaseComplete(System.Boolean)``
- `CastleClashers.Game`: ``System.Collections.Generic.Dictionary`2<System.String, System.Int32> CastleClashers.Rewards.ChestRoller::FilterMaxedCards(System.Collections.Generic.Dictionary`2<System.String, System.Int32>)``
- `CastleClashers.Game`: ``System.String CastleClashers.HumanLikeBots.ArenaLogsManager::GetJsonData()``
- `CastleClashers.Game`: ``System.Single CastleClashers.HumanLikeBots.AimConfigSO::GetArenaOffsetMultiplier(System.Int32, System.Boolean)``
- `CastleClashers.Game`: ``Agent CastleClashers.HumanLikeBots.HumanLikeAimController::GetHighValueExposedUnit(System.Collections.Generic.List`1<Agent>, CastleClashers.HumanLikeBots.HumanLikeConfig)``
- `CastleClashers.Game`: ``System.Int32 CastleClashers.HumanLikeBots.HumanLikeAimController::SelectLegendaryUnitFromValid(System.Collections.Generic.List`1<Agent>, System.Collections.Generic.List`1<System.Int32>)``
- `CastleClashers.Game`: ``System.Single CastleClashers.HumanLikeBots.HumanLikeCastleBuilder::GetPlayerAverageCastleLevel()``
- `CastleClashers.Game`: ``System.Single CastleClashers.HumanLikeBots.HumanLikePurchaseBoostTracker::GetCurrentCastleUpgradeAvg()``
- `CastleClashers.Game`: ``System.Collections.Generic.List`1<CastleClashers.HumanLikeBots.FetchedUnitPosition> CastleClashers.HumanLikeBots.PlayerProfileFetcher::MirrorUnitPositions(System.Collections.Generic.List`1<CastleClashers.HumanLikeBots.FetchedUnitPosition>, System.Int32)``
- `CastleClashers.Game`: ``System.Void CastleClashers.UI.IAPOffersView::PopulateCards(System.Collections.Generic.List`1<CardValuePair>, UnityEngine.Transform)``
- `CastleClashers.Game`: ``System.Void CardData+SaveData::.ctor(System.Collections.Generic.List`1<CardData>)``
- `CastleClashers.Game`: ``System.Void VoodoDebuggerController+<>c__DisplayClass38_0::<AddUnitPieces>b__0()``
- `CastleClashers.Game`: ``System.Boolean MapController+<DisableColldiersAtStart>d__37::MoveNext()``
- `CastleClashers.Game`: ``System.Boolean AnimatedWeeklyLeaderboardPanel+<>c__DisplayClass37_0::<CreateMilestoneAwareScrollTween>g__IsSlow|3(System.Single, System.Single)``
- `CastleClashers.Game`: ``System.Void WeeklyHistoryData+SaveData::.ctor(System.Collections.Generic.List`1<WeeklyResult>, WeeklyResult)``
- `CastleClashers.Game`: ``System.Void Tournament.TournamentController+<>c__DisplayClass145_0::<FetchAllTournamentConfigs>b__0(NakamaHttp.CastleClashersTournamentGetConfigsResp)``
- `Assembly-CSharp`: ``System.Collections.Generic.Dictionary`2<System.String, System.Object> JsonUtils::JObjectToDictionary(Newtonsoft.Json.Linq.JObject)``
- `Assembly-CSharp`: ``System.Void DebugCopyButton::OnButtonClick()``
- `Assembly-CSharp`: ``System.Void ConsentManagementProvider.CMP::Initialize(System.Int32, System.Int32, System.String, ConsentManagementProvider.MESSAGE_LANGUAGE, System.Collections.Generic.List`1<ConsentManagementProvider.SpCampaign>, ConsentManagementProvider.CAMPAIGN_ENV, System.Int64)``
- `Assembly-CSharp`: ``System.Boolean ConsentManagementProvider.Android.ConsentWrapperAndroid::ValidateSpCampaigns(System.Collections.Generic.List`1<ConsentManagementProvider.SpCampaign>&)``
- `Assembly-CSharp`: ``System.Collections.Generic.List`1<ConsentManagementProvider.Consentable> ConsentManagementProvider.Json.JsonUnwrapperHelper::UnwrapConsentable(System.Collections.Generic.List`1<ConsentManagementProvider.Json.ConsentableWrapper>)``
- `Assembly-CSharp`: ``System.Collections.Generic.List`1<ConsentManagementProvider.ConsentString> ConsentManagementProvider.Json.JsonUnwrapperHelper::UnwrapConsentStrings(System.Collections.Generic.List`1<ConsentManagementProvider.Json.ConsentStringWrapper>)``
- `Assembly-CSharp`: ``System.Void PaperPlaneTools.AlertAndroidAdapter::PaperPlaneTools.IAlertPlatformAdapter.Show(PaperPlaneTools.Alert)``
- `Assembly-CSharp`: ``System.Void CastleClashers.VoodooLiveIntegration.VoodooLiveChainOfferAdapter::ApplyNonAdultSubstitution(System.Collections.Generic.List`1<ChainOffer.ChainOfferStepData>, System.Func`2<Chests.ChestType, System.Int32>)``
- `Assembly-CSharp`: ``System.Boolean CastleClashers.VoodooLiveIntegration.VoodooLiveChainOfferAdapter::StepHasChestReward(System.Collections.Generic.List`1<ChainOffer.ChainOfferStepData>, System.Int32)``
- `Assembly-CSharp`: ``System.Collections.Generic.IReadOnlyList`1<Voodoo.Live.Offers.IFeature> CastleClashers.VoodooLiveIntegration.VoodooLiveOfferRouter::GetBadgeEligibleFeatures(System.Predicate`1<Voodoo.Live.Offers.IFeature>)``
- `Assembly-CSharp`: ``System.Collections.Generic.List`1<VoodooSauce+AnalyticsProvider> CastleClashers.SDKAdapters.AnalyticsEnumMapper::ToVoodoo(System.Collections.Generic.List`1<CastleClashers.SDKGlue.AnalyticsProvider>)``
- `Assembly-CSharp`: ``System.Collections.Generic.IReadOnlyList`1<CastleClashers.SDKGlue.IAPProduct> CastleClashers.SDKAdapters.VoodooIAPPriceAdapter::GetProducts()``
- `Assembly-CSharp`: ``System.String Voodoo.Analytics.AnalyticsUtil::ConvertDictionaryToContextVarJson(System.Collections.Generic.Dictionary`2<System.String, System.Object>)``
- `Assembly-CSharp`: ``System.Void Voodoo.Analytics.VoodooAnalyticsManager::FillGlobalContextVariables(System.Collections.Generic.Dictionary`2<System.String, System.Object>&)``
- `Assembly-CSharp`: ``System.Void Voodoo.Analytics.VoodooAnalyticsManager::FillEventSpecificContextVariables(System.Collections.Generic.Dictionary`2<System.String, System.Object>&, System.String)``
- `Assembly-CSharp`: ``System.Void Voodoo.ADN.AdnSdk::Initialize(Voodoo.ADN.AdnSdkInitializationMode, System.Boolean, System.Collections.Generic.Dictionary`2<System.String, System.String>, Voodoo.ADN.ContextSDK.AdnContextSDKConfiguration)``
- `Assembly-CSharp`: ``System.Collections.Generic.Dictionary`2<System.String, System.Object> Voodoo.ADN.ContextSDK.AdnDictionaryConverter::ConvertValues(System.Collections.Generic.Dictionary`2<System.String, System.String>)``
- `Assembly-CSharp`: ``System.Boolean Voodoo.Live.Conditionnal::CanUse(System.Collections.Generic.List`1<System.String>)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.DecoratorFactory::Dispose()``
- `Assembly-CSharp`: ``Voodoo.Live.IOperator Voodoo.Live.OperatorFactory::CreateOperator(System.String, Voodoo.Live.IBlackboard)``
- `Assembly-CSharp`: ``System.Boolean Voodoo.Live.Inventory::HasNonConsumableItemPurchased(System.Collections.Generic.List`1<System.String>, System.String&)``
- `Assembly-CSharp`: ``Voodoo.Live.ItemQuantity[] Voodoo.Live.RandomReward::Resolve()``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.RandomReward::Validate()``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.TransactionRegistry::RelaunchPendingTransactions()``
- `Assembly-CSharp`: ``Voodoo.Live.Transaction Voodoo.Live.TransactionRegistry::GetTransactionBySKU(System.String)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.TransactionRegistry::Dispose()``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.VoodooLive::RetrieveTransaction()``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Shop.GameShop::.ctor(Voodoo.Live.Shop.GameShopDTO, System.Collections.Generic.List`1<Voodoo.Live.Shop.ShopSection>)``
- `Assembly-CSharp`: ``Voodoo.Live.Shop.ShopSection Voodoo.Live.Shop.GameShop::GetSectionByProductId(System.String)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Shop.ShopManager::Dispose()``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Sample.Utils.InventorySystem::SaveInventory()``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Sample.Shop.UI.GameShopUI::Init()``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Sample.Shop.UI.ShopSectionUI::Init(Voodoo.Live.Shop.ShopSection, System.Action, Voodoo.Live.Shop.GameShop, UnityEngine.RectTransform, Voodoo.Live.Utils.SpriteDictionarySO)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Sample.Shop.UI.ShopSectionUI::OnEnable()``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Sample.Offers.UI.OfferBadgesManagerUI::Init(Voodoo.Live.Sample.Offers.UI.OfferBadgeUI[], System.Collections.Generic.List`1<Voodoo.Live.Offers.IFeature>)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Sample.Offers.UI.OfferBadgesManagerUI::OnEnable()``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Sample.Offers.UI.EndlessOfferPopupUI::PurchaseClicked(Voodoo.Live.Product)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Sample.Offers.UI.TwoThreePOPopupUI::InitFeatures()``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Offers.FeatureGroup::Validate()``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Offers.FeatureClient::ResetFeatures()``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Offers.FeatureQueue::Show(System.Collections.Generic.List`1<Voodoo.Live.Offers.IFeature>)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Offers.Conditions::CollectNonConsumableItemsFromProducts(System.Collections.Generic.List`1<Voodoo.Live.Product>, System.Collections.Generic.List`1<System.String>)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Offers.Campaigns.Campaign::SyncServerFeaturesWithProgression(System.Collections.Generic.List`1<Voodoo.Live.Offers.IServerFeature>)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Offers.Campaigns.Campaign::Dispose()``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Offers.Campaigns.CampaignProgression::Dispose()``
- `Assembly-CSharp`: ``System.Collections.Generic.Dictionary`2<System.String, System.Object> Voodoo.Live.Analytics.BaseEvent::GetParameters(Voodoo.Live.IBlackboard)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Analytics.FeatureEventsClient::.ctor(System.Collections.Generic.List`1<Voodoo.Live.Analytics.BaseEvent>)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Analytics.FeatureEventsClient::AddEventsToTrack(System.Collections.Generic.List`1<Voodoo.Live.Analytics.BaseEvent>)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Analytics.FeatureEventsClient::SetEventsToTrack(System.Collections.Generic.List`1<Voodoo.Live.Analytics.BaseEvent>)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Analytics.FeatureEventsClient::CleanEventsToTrack(System.Collections.Generic.List`1<Voodoo.Live.Analytics.BaseEvent>)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Analytics.FeatureEventsClient::Dispose()``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Analytics.FeatureTrackingRegistry::Initialize(System.Collections.Generic.List`1<Voodoo.Live.Offers.IFeature>)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Debugger.CampaignDebugUI::PopulateValues()``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Debugger.CampaignSubHeader::Init(System.Collections.Generic.List`1<Voodoo.Live.Offers.Campaigns.Campaign>, UnityEngine.Transform)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Debugger.DebugScreen::ClearTabMessage()``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Debugger.ShopProductDebug::OnValueChanged(System.Boolean)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Debugger.ShopSubheader::Init(Voodoo.Live.Shop.GameShop, UnityEngine.Transform)``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Debugger.TransactionDebugUI::PopulateValues()``
- `Assembly-CSharp`: ``System.Void Voodoo.Live.Debugger.VoodooLiveDebugUI::Clear()``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Debugger.DebuggerCanvas::Awake()``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Debugger.Screen::RefreshWidgets()``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Debugger.Screen::ResetRadioGroups(System.Boolean)``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Debugger.TabbedScreen::Start()``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Debugger.EventConsoleListScreen::RefreshSessionsSize()``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Debugger.HomeDebugScreen::Refresh()``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Debugger.SDKListDebugScreen::InstantiateSdkList(Voodoo.Sauce.Internal.SDKs.SDKList)``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Debugger.SDKListDebugScreen::CreateMediation(Voodoo.Sauce.Internal.SDKs.MediationSDK)``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Debugger.SDKListDebugScreen::CreateSdk(System.Collections.Generic.List`1<Voodoo.Sauce.Internal.SDKs.SDK>)``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Debugger.VoodooTuneConfigurationDetailsScreen::Start()``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Debugger.VoodooTuneSegmentsDebugScreen::OnNoneSegmentButtonClicked()``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Debugger.DebugHideableSection::UpdateDisplay(System.Boolean)``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Internal.LoggerSettingsManager::InitializeLogCategories()``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Internal.VoodooTune.VoodooTuneAbTestsTracker::TrackAbTestModifications(System.Collections.Generic.List`1<System.String>, System.Collections.Generic.List`1<System.String>, System.String)``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Internal.VoodooTune.WatchedRewardedVideosCounter::CleanUpOldCounts()``
- `Assembly-CSharp`: ``System.Collections.Generic.List`1<Voodoo.Sauce.Debugger.CustomDebugger> Voodoo.Sauce.Internal.DebugScreen.DebugCustomUtility::GetAllCustomDebugger()``
- `Assembly-CSharp`: ``System.String Voodoo.Sauce.Internal.Common.Utils.QueryParameters::GetFormattedUrl()``
- `Assembly-CSharp`: ``System.Boolean Voodoo.Sauce.Internal.Utils.ManifestUtilsImpl::Replace(System.Collections.Generic.Dictionary`2<System.String, System.String>)``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Internal.Firebase.FirebaseInitializer::OnInitComplete()``
- `Assembly-CSharp`: ``System.Collections.Generic.Dictionary`2<System.String, System.Object> Voodoo.Sauce.Internal.Extension.DictionaryExtension::RemoveNullValues(System.Collections.Generic.Dictionary`2<System.String, System.Object>)``
- `Assembly-CSharp`: ``System.Boolean Voodoo.Sauce.Internal.Attribution.FallbackPayingUserProvider::IsPayingUser()``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Internal.Analytics.AdjustAnalyticsEvent::PerformTrackEvent()``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Internal.Analytics.AdjustWrapper::AddAdjustSessionCallbackParameters(System.Collections.Generic.Dictionary`2<System.String, System.String>)``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Internal.Analytics.AmplitudeAnalyticsEvent::LogEventDebugInfo()``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Internal.Analytics.AmplitudeWrapper::FillGlobalContextVariables(System.Collections.Generic.Dictionary`2<System.String, System.Object>)``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Internal.Analytics.AmplitudeWrapper::FillEventSpecificContextVariables(System.Collections.Generic.Dictionary`2<System.String, System.Object>, System.String)``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Internal.Analytics.AmplitudeCustomEventsHandler::TrackCustomEvent(System.String, System.String, System.Collections.Generic.List`1<VoodooSauce+AnalyticsProvider>, System.Collections.Generic.Dictionary`2<System.String, System.Object>)``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Internal.Analytics.AmplitudeFunnelEventsHandler::OnTrackVoodooFunnel(System.String, System.String, System.Int32, System.Collections.Generic.Dictionary`2<System.String, System.Object>)``
- `Assembly-CSharp`: ``System.Collections.Generic.IEnumerable`1<Voodoo.Sauce.Internal.Analytics.IAnalyticsAttributionProvider> Voodoo.Sauce.Internal.Analytics.AnalyticsManager::AnalyticsAttributionProviders()``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Internal.Analytics.FirebaseAnalyticsEvent::UpdateParamKeysToFirebaseSpecific()``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Internal.Analytics.PerformanceTracking.CustomPerformanceTrackingManager::Dispose()``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Internal.Analytics.PerformanceTracking.FrameCounterService::Dispose()``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Internal.Ads.AdsManager::TriggerPendingRewardedButtonShownEvents()``
- `Assembly-CSharp`: ``Voodoo.Sauce.Internal.SDKs.SDK Voodoo.Sauce.Internal.Ads.MaxMediation.MaxMediationAdapterSDK::GetSDKInformations()``
- `Assembly-CSharp`: ``System.Void RetroArsenalLib.RetroVFXLibrary::DestroyLoopingParticleEffects()``
- `Assembly-CSharp`: ``System.Void ShapeFX.Demo.ShFX_Atlas::Update()``
- `Assembly-CSharp`: ``System.Void ShapeFX.Demo.ShFX_Atlas::DeactivateGroup(System.Int32)``
- `Assembly-CSharp`: ``System.Void Voodoo.Sauce.Privacy.PrivacyManager+VendorIdHelperAndroid::DisposeObjects(System.Collections.Generic.List`1<UnityEngine.AndroidJavaObject>)``
- `Assembly-CSharp`: ``System.Boolean Voodoo.Sauce.Internal.Analytics.PerformanceTracking.FrameCounterService+<UpdateLoop>d__9::MoveNext()``
