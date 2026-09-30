# EH region recovery (206, slice 2)

Task: dankondr/castle-recovery#206. Continues slice 1 and addresses dankondr/Cpp2IL#80.

## Rule

An LSDA landing pad is evidence of native unwinding, not by itself evidence of a
managed catch or finally. Decode the action chain and its RTTI entries first.
Malformed chains keep the call site without granting a cleanup proof.

`EhRegionPartition` retains a snapshot before SSA rewrites register and frame
identities. `NativeExceptionRegionProof` compares each reachable protected call's
exceptional path with the normal cleanup copy. The comparison includes the call
target, every argument (including MethodInfo), frame storage identity, effect order,
and propagation of the original exception. Small unwind closures use the same
interpreter. C++ wrapper allocation, begin/end catch and termination guards are
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
void return ends with `leave` to a normal return outside the clause. Captured native
locals, non-void return values, arbitrary catch CFGs, filters and faults still need
proofs.

The narrow class-predicate recognizer is the authorized exception to the
[dankondr/castle-recovery#208](https://github.com/dankondr/castle-recovery/issues/208)
lane boundary, in its own commit `bb2e4930`. It follows only bounded, pure ARM64 B
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

## r241 verification, continuation

Control: `fef0729da8eccc2a3dc722af9dc3b6aa67d584b3` (`development`, merge of #176), after the requested second rebase.
Both full sweeps process 69,982 native methods and emit 183 assemblies. The inputs
and all generated binaries/logs stay outside the repository under `/private/tmp`.
Final output: `astra206-r3-final` (93.8 seconds); control: `astra206-r3-control`.

| Scope | Methods | Diagnosed, control → branch | Newly clean | Clean regressions | Pad messages, control → branch |
|---|---:|---:|---:|---:|---:|
| All assemblies | 178,274 | 16,782 → 16,242 | 540 | 0 | 54,380 → 47,468 |
| Game-owned | 25,348 | 4,289 → 3,959 | 330 | 0 | 15,537 → 10,969 |
| CastleClashers.Game | 14,423 | 2,688 → 2,457 | 231 | 0 | 9,865 → 6,659 |
| Four castle-building types and descendants | 280 | 103 → 90 | 13 | 0 | 882 → 684 |

No method gains a diagnostic, including methods already diagnosed. All 330 newly
clean owned methods previously had only pad diagnostics. “Clean” here means no
emitted diagnostic; it is not a claim of whole-method semantic equivalence. The
manual review found a pre-existing non-EH loop defect, described under Gaps.

The castle scope uses the four exact owner names and every `Owner+...` descendant,
keyed by assembly/token. It measures 280 methods, rather than the brief's 273.
### Castle-building newly clean methods

The thirteen newly clean methods are:

- `System.Int32 CastleBuildingController::HowManyUpgradable()`
- `System.Collections.Generic.List`1<DecorationSO> CastleMaker::GetDecorationsAtPosition(UnityEngine.Vector2)`
- `DecorationRoofSO CastleMaker::GetRoofDecorationAtPosition(UnityEngine.Vector2)`
- `DecorationFoundataionSO CastleMaker::GetAnyFoundationDecoration()`
- `System.Boolean CastleMaker::TryApplyFetchedDecorations(CastleClashers.HumanLikeBots.HumanLikeBotProfile)`
- `System.Void CastleMaker::ApplyPvpOpponentFoundations(CastleClashers.HumanLikeBots.FetchedPlayerProfile)`
- `System.Void CastleMaker::ApplyPvpOpponentDecorations(CastleClashers.HumanLikeBots.FetchedPlayerProfile)`
- `System.Collections.Generic.List`1<FoundationData> CastleMaker::MirrorFoundationPositions(System.Collections.Generic.List`1<FoundationData>, System.Int32)`
- `EngineerData EngineersController::GetEngineerData(System.String)`
- `EngineerVisualData EngineersController::GetEngineerVisualData(System.String)`
- `EngineerData EngineersController::GetEngineerThatUnlocksAtArenaIndex(System.Int32)`
- `System.Boolean TimedCastleBuildingController::CheckIfBuildingAtThatPosition(UnityEngine.Vector2)`
- `System.Boolean TimedCastleBuildingController::CheckIfUpgradingAtThatPosition(UnityEngine.Vector2)`

### Measurements after each rule

| Base / added rule | Owned pad messages | Newly clean owned methods versus previous row | New diagnostics |
|---|---:|---:|---:|
| `b620e057` control | 15,537 | — | — |
| Original PR, rebased | 11,198 | 311 | 0 |
| Compound cleanup sequences | 11,198 | 0 | 0 |
| Assignment on every incoming path | 11,198 | 0 | 0 |
| Switch exits through leave | 11,198 | 0 | 0 |
| Proper nesting rechecked with flat/nested execution tests | 11,198 | 0 | 0 |
| Rebase onto `fef0729d` (#176); control remains 15,537 | 11,162 | 326 versus new control | 0 |
| Export-proven class predicate | 11,162 | 0 | 0 |
| Intersect all incoming catch states | 11,162 | 0 | 0 |
| Preserve storage across value boxing | 10,967 | 5 | 0 |
| Separate void catch return | 10,967 | 0 | 0 |
| Invalidate writes between exceptional cleanup effects | 10,969 | −1 | 2 control warnings retained |

The final write guard retains two original pad warnings in
`VoodooLiveDiagnostics.CollectCampaignDiagnostics`, which the intermediate version
incorrectly cleared. Potential writes must invalidate facts before the next cleanup
or an auxiliary unwind path. This loses one intermediate clean result and has no
regression versus control. It removes 16 native pad proofs across that method,
`CollectFeatureDiagnostics` and `HumanLikeAimController.GetDeepInsideCastleTarget`.
The 23 focused EH cases include a negative test for a second cleanup reading
storage that the first call may change.

The reference cases do not fail the proper-subset nesting check. No additional
relaxation of the overlap guard was justified. Native effects with different site
sets still need proper nesting; equal site sets now form one compound handler.

### Validation

- Core.Tests: **1,181/1,181** on the final exceptional-write guard; focused EH
  tests: **23/23**. After equivalent portable API-overload substitutions,
  EH + KeyFunctionRecovery tests: **42/42**.
- LibCpp2ILTests: **12/12**; JitOracle.Tests: **9/9**.
- Release `net10.0` build succeeds with the same 13 existing warnings.
- Full sweeps and audit at code commit `56272907`: 178,274 methods; both control
  and branch have **170,144 ILVerify-valid**, **416 ILVerify-invalid** and 7,714
  partial/no-body entries. **Zero status transitions**, including **0 valid→invalid**.
  The broader Bootstrap reachability gate stays blocked at 29/29 in both scans.
- Final serialized IL for all sixteen manually reviewed methods is identical to
  the reviewed output. No regression list is needed: no method gains a diagnostic
  versus control. The complete newly clean list appears below.
- Additional `netstandard2.0` build does not pass: newer collection/LINQ APIs and
  reference-comparer compatibility remain unresolved in existing code and these
  EH files. Two avoidable overload dependencies were removed; legacy-target
  compatibility is not claimed by the successful `net10.0` checks.

## Gaps

The >50% pad-reduction target is **not met**. Reduction is 4,568/15,537 (29.4%);
557 owned methods retain 10,969 pad messages, including 111 pad-only methods.
Keep PR #175 a draft. No warning text was hidden or reworded.

| Remaining category | Methods | Remaining pad messages |
|---|---:|---:|
| No native cleanup proof | 421 | 7,518 |
| Mixed proven and unproven native pads | 58 | 1,987 |
| All native pads proven, one or more IL regions refused | 78 | 1,464 |

Native proofs cover 7,084 of the original 15,537 pads (up from 6,495); 2,516 of
these remain unmaterialized. The 421 methods without a native cleanup proof are
classified below. Categories are assigned in table order, so counts do not double
count methods; a method can exhibit more than one unsupported shape. These are
observed shapes, not a claim that one cause accounts for every pad in a method.

| Shape | Methods | Remaining pads | Example | Missing proof |
|---|---:|---:|---|---|
| Async/iterator MoveNext | 133 | 3,969 | `Bootstrap.<InitializeVoodooLive>d__21.MoveNext` | State-dependent dispatch, captured fields and exception/return-state merges |
| Unsupported cleanup arguments | 39 | 605 | `MenuPanel.HandleArenaProgressionSetup` | A normal cleanup target exists, but receiver/arguments cannot be shown equal after possible writes |
| Class-test dispatch | 132 | 1,150 | `VoodooTuneJson.get_Json` | Class value and handler state/return merge are not established |
| Compound/shared cleanup with a returning closure | 100 | 1,422 | `VoodooTuneFieldProcessorInstance.ProcessFields` | Shared normal/exceptional paths and returning closure state/effects; reaching a native RET is insufficient |
| Other native state/CFG | 17 | 372 | `LoginStreakController.SetUIAndOpenPopUpIfNewDay` | No converged incoming state or supported reachable cleanup sequence |

The read-only boxing rule addresses a concrete argument-loss shape in this group:
605 additional native pads become proven and 195 additional owned pad messages
are removed before the final write guard; the net gain is 589 native proofs and
193 removed owned messages over the same-base intermediate branch. Further shape widening has no established argument/effect/CFG proof
in this continuation, so the remaining warnings stay.

Specific boundaries:

- `StoreController.OpenSection`: all 152 pads proven natively. Emitted Dispose still
  uses a zero-initialized replacement receiver and a diagnostic call. Copying that
  handler cannot establish a sound finally. This persists after #176.
- `CastleMaker.Build`: all 43 pads proven natively. Neither candidate has a
  reachable emitted unit in its protected native ranges. Its refusal is not an
  overlap problem; deleting the reachability check would invent a try body.
- `CastleMaker.BuildGridAuto`: the proposed region includes an uncovered
  `List<Vector2Int>` constructor. It is not safe to protect this extra call.
- 271 remaining methods contain 330 calls to the now-recognized class predicate;
  together they retain 5,171 pads (an overlapping subset, not 5,171 proven catches).
  Zero typed catches are materialized in r241. In 23 methods the straight prefix
  reaches the predicate but its class value is a load at offset 16 through a global
  pointer, with no metadata type proof. Other prefixes/handlers require additional
  control-flow or state recovery. Export identity alone does not prove catch(T).
- Manual review found a non-EH defect already present in control: in
  `LevelCostTable.RebuildIndex`, native `3C877A0` reads the current entry after each
  MoveNext, but control IL reads `get_Current` once at IL_005D before the loop
  (MoveNext at IL_0199). Branch IL retains that pre-loop read at IL_0067. The same
  pre-loop Current shape is visible in `AdnDictionaryConverter.ConvertValues`.
  This is a dataflow boundary; the prohibited simplifier/local-variable/emitter
  areas were not changed. The EH proof establishes the saved receiver and cleanup
  edges, not correctness of those pre-existing loop values.
- Zero negative LSDA selectors and zero undecodable action chains were found in
  the original 1,019 methods. Managed filters/faults: zero positively identified,
  occurrence count unknown; recovery remains unsupported.

## Game-owned methods made diagnostic-free

<details>
<summary>All 330 methods (assembly and output signature)</summary>

- `Assembly-CSharp`: `System.Boolean CastleClashers.VoodooLiveIntegration.VoodooLiveChainOfferAdapter::StepHasChestReward(System.Collections.Generic.List`1<ChainOffer.ChainOfferStepData>, System.Int32)`
- `Assembly-CSharp`: `System.Boolean ConsentManagementProvider.Android.ConsentWrapperAndroid::ValidateSpCampaigns(System.Collections.Generic.List`1<ConsentManagementProvider.SpCampaign>&)`
- `Assembly-CSharp`: `System.Boolean Voodoo.Live.Conditionnal::CanUse(System.Collections.Generic.List`1<System.String>)`
- `Assembly-CSharp`: `System.Boolean Voodoo.Live.Inventory::HasNonConsumableItemPurchased(System.Collections.Generic.List`1<System.String>, System.String&)`
- `Assembly-CSharp`: `System.Boolean Voodoo.Sauce.Internal.Analytics.PerformanceTracking.FrameCounterService+<UpdateLoop>d__9::MoveNext()`
- `Assembly-CSharp`: `System.Boolean Voodoo.Sauce.Internal.Attribution.FallbackPayingUserProvider::IsPayingUser()`
- `Assembly-CSharp`: `System.Boolean Voodoo.Sauce.Internal.Utils.ManifestUtilsImpl::Replace(System.Collections.Generic.Dictionary`2<System.String, System.String>)`
- `Assembly-CSharp`: `System.Collections.Generic.Dictionary`2<System.String, System.Object> JsonUtils::JObjectToDictionary(Newtonsoft.Json.Linq.JObject)`
- `Assembly-CSharp`: `System.Collections.Generic.Dictionary`2<System.String, System.Object> Voodoo.ADN.ContextSDK.AdnDictionaryConverter::ConvertValues(System.Collections.Generic.Dictionary`2<System.String, System.String>)`
- `Assembly-CSharp`: `System.Collections.Generic.Dictionary`2<System.String, System.Object> Voodoo.Live.Analytics.BaseEvent::GetParameters(Voodoo.Live.IBlackboard)`
- `Assembly-CSharp`: `System.Collections.Generic.Dictionary`2<System.String, System.Object> Voodoo.Sauce.Internal.Extension.DictionaryExtension::RemoveNullValues(System.Collections.Generic.Dictionary`2<System.String, System.Object>)`
- `Assembly-CSharp`: `System.Collections.Generic.IEnumerable`1<Voodoo.Sauce.Internal.Analytics.IAnalyticsAttributionProvider> Voodoo.Sauce.Internal.Analytics.AnalyticsManager::AnalyticsAttributionProviders()`
- `Assembly-CSharp`: `System.Collections.Generic.IReadOnlyList`1<CastleClashers.SDKGlue.IAPProduct> CastleClashers.SDKAdapters.VoodooIAPPriceAdapter::GetProducts()`
- `Assembly-CSharp`: `System.Collections.Generic.IReadOnlyList`1<Voodoo.Live.Offers.IFeature> CastleClashers.VoodooLiveIntegration.VoodooLiveOfferRouter::GetBadgeEligibleFeatures(System.Predicate`1<Voodoo.Live.Offers.IFeature>)`
- `Assembly-CSharp`: `System.Collections.Generic.List`1<ConsentManagementProvider.ConsentString> ConsentManagementProvider.Json.JsonUnwrapperHelper::UnwrapConsentStrings(System.Collections.Generic.List`1<ConsentManagementProvider.Json.ConsentStringWrapper>)`
- `Assembly-CSharp`: `System.Collections.Generic.List`1<ConsentManagementProvider.Consentable> ConsentManagementProvider.Json.JsonUnwrapperHelper::UnwrapConsentable(System.Collections.Generic.List`1<ConsentManagementProvider.Json.ConsentableWrapper>)`
- `Assembly-CSharp`: `System.Collections.Generic.List`1<Voodoo.Sauce.Debugger.CustomDebugger> Voodoo.Sauce.Internal.DebugScreen.DebugCustomUtility::GetAllCustomDebugger()`
- `Assembly-CSharp`: `System.Collections.Generic.List`1<VoodooSauce+AnalyticsProvider> CastleClashers.SDKAdapters.AnalyticsEnumMapper::ToVoodoo(System.Collections.Generic.List`1<CastleClashers.SDKGlue.AnalyticsProvider>)`
- `Assembly-CSharp`: `System.String Voodoo.Analytics.AnalyticsUtil::ConvertDictionaryToContextVarJson(System.Collections.Generic.Dictionary`2<System.String, System.Object>)`
- `Assembly-CSharp`: `System.String Voodoo.Sauce.Internal.Common.Utils.QueryParameters::GetFormattedUrl()`
- `Assembly-CSharp`: `System.Void CastleClashers.VoodooLiveIntegration.VoodooLiveChainOfferAdapter::ApplyNonAdultSubstitution(System.Collections.Generic.List`1<ChainOffer.ChainOfferStepData>, System.Func`2<Chests.ChestType, System.Int32>)`
- `Assembly-CSharp`: `System.Void ConsentManagementProvider.CMP::Initialize(System.Int32, System.Int32, System.String, ConsentManagementProvider.MESSAGE_LANGUAGE, System.Collections.Generic.List`1<ConsentManagementProvider.SpCampaign>, ConsentManagementProvider.CAMPAIGN_ENV, System.Int64)`
- `Assembly-CSharp`: `System.Void DebugCopyButton::OnButtonClick()`
- `Assembly-CSharp`: `System.Void PaperPlaneTools.AlertAndroidAdapter::PaperPlaneTools.IAlertPlatformAdapter.Show(PaperPlaneTools.Alert)`
- `Assembly-CSharp`: `System.Void RetroArsenalLib.RetroVFXLibrary::DestroyLoopingParticleEffects()`
- `Assembly-CSharp`: `System.Void ShapeFX.Demo.ShFX_Atlas::DeactivateGroup(System.Int32)`
- `Assembly-CSharp`: `System.Void ShapeFX.Demo.ShFX_Atlas::Update()`
- `Assembly-CSharp`: `System.Void Voodoo.ADN.AdnSdk::Initialize(Voodoo.ADN.AdnSdkInitializationMode, System.Boolean, System.Collections.Generic.Dictionary`2<System.String, System.String>, Voodoo.ADN.ContextSDK.AdnContextSDKConfiguration)`
- `Assembly-CSharp`: `System.Void Voodoo.Analytics.VoodooAnalyticsManager::FillEventSpecificContextVariables(System.Collections.Generic.Dictionary`2<System.String, System.Object>&, System.String)`
- `Assembly-CSharp`: `System.Void Voodoo.Analytics.VoodooAnalyticsManager::FillGlobalContextVariables(System.Collections.Generic.Dictionary`2<System.String, System.Object>&)`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Analytics.FeatureEventsClient::.ctor(System.Collections.Generic.List`1<Voodoo.Live.Analytics.BaseEvent>)`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Analytics.FeatureEventsClient::AddEventsToTrack(System.Collections.Generic.List`1<Voodoo.Live.Analytics.BaseEvent>)`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Analytics.FeatureEventsClient::CleanEventsToTrack(System.Collections.Generic.List`1<Voodoo.Live.Analytics.BaseEvent>)`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Analytics.FeatureEventsClient::Dispose()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Analytics.FeatureEventsClient::SetEventsToTrack(System.Collections.Generic.List`1<Voodoo.Live.Analytics.BaseEvent>)`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Analytics.FeatureTrackingRegistry::Initialize(System.Collections.Generic.List`1<Voodoo.Live.Offers.IFeature>)`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Debugger.CampaignDebugUI::PopulateValues()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Debugger.CampaignSubHeader::Init(System.Collections.Generic.List`1<Voodoo.Live.Offers.Campaigns.Campaign>, UnityEngine.Transform)`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Debugger.DebugScreen::ClearTabMessage()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Debugger.ShopProductDebug::OnValueChanged(System.Boolean)`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Debugger.ShopSubheader::Init(Voodoo.Live.Shop.GameShop, UnityEngine.Transform)`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Debugger.TransactionDebugUI::PopulateValues()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Debugger.VoodooLiveDebugUI::Clear()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.DecoratorFactory::Dispose()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Offers.Campaigns.Campaign::Dispose()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Offers.Campaigns.Campaign::SyncServerFeaturesWithProgression(System.Collections.Generic.List`1<Voodoo.Live.Offers.IServerFeature>)`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Offers.Campaigns.CampaignProgression::Dispose()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Offers.Conditions::CollectNonConsumableItemsFromProducts(System.Collections.Generic.List`1<Voodoo.Live.Product>, System.Collections.Generic.List`1<System.String>)`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Offers.FeatureClient::ResetFeatures()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Offers.FeatureGroup::Validate()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Offers.FeatureQueue::Show(System.Collections.Generic.List`1<Voodoo.Live.Offers.IFeature>)`
- `Assembly-CSharp`: `System.Void Voodoo.Live.RandomReward::Validate()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Sample.Offers.UI.EndlessOfferPopupUI::PurchaseClicked(Voodoo.Live.Product)`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Sample.Offers.UI.OfferBadgesManagerUI::Init(Voodoo.Live.Sample.Offers.UI.OfferBadgeUI[], System.Collections.Generic.List`1<Voodoo.Live.Offers.IFeature>)`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Sample.Offers.UI.OfferBadgesManagerUI::OnEnable()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Sample.Offers.UI.TwoThreePOPopupUI::InitFeatures()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Sample.Shop.UI.GameShopUI::Init()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Sample.Shop.UI.ShopSectionUI::Init(Voodoo.Live.Shop.ShopSection, System.Action, Voodoo.Live.Shop.GameShop, UnityEngine.RectTransform, Voodoo.Live.Utils.SpriteDictionarySO)`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Sample.Shop.UI.ShopSectionUI::OnEnable()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Sample.Utils.InventorySystem::SaveInventory()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Shop.GameShop::.ctor(Voodoo.Live.Shop.GameShopDTO, System.Collections.Generic.List`1<Voodoo.Live.Shop.ShopSection>)`
- `Assembly-CSharp`: `System.Void Voodoo.Live.Shop.ShopManager::Dispose()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.TransactionRegistry::Dispose()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.TransactionRegistry::RelaunchPendingTransactions()`
- `Assembly-CSharp`: `System.Void Voodoo.Live.VoodooLive::RetrieveTransaction()`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Debugger.DebugHideableSection::UpdateDisplay(System.Boolean)`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Debugger.DebuggerCanvas::Awake()`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Debugger.EventConsoleListScreen::RefreshSessionsSize()`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Debugger.HomeDebugScreen::Refresh()`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Debugger.SDKListDebugScreen::CreateMediation(Voodoo.Sauce.Internal.SDKs.MediationSDK)`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Debugger.SDKListDebugScreen::CreateSdk(System.Collections.Generic.List`1<Voodoo.Sauce.Internal.SDKs.SDK>)`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Debugger.SDKListDebugScreen::InstantiateSdkList(Voodoo.Sauce.Internal.SDKs.SDKList)`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Debugger.Screen::RefreshWidgets()`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Debugger.Screen::ResetRadioGroups(System.Boolean)`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Debugger.TabbedScreen::Start()`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Debugger.VoodooTuneConfigurationDetailsScreen::Start()`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Debugger.VoodooTuneSegmentsDebugScreen::OnNoneSegmentButtonClicked()`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Internal.Ads.AdsManager::TriggerPendingRewardedButtonShownEvents()`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Internal.Analytics.AdjustAnalyticsEvent::PerformTrackEvent()`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Internal.Analytics.AdjustWrapper::AddAdjustSessionCallbackParameters(System.Collections.Generic.Dictionary`2<System.String, System.String>)`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Internal.Analytics.AmplitudeAnalyticsEvent::LogEventDebugInfo()`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Internal.Analytics.AmplitudeCustomEventsHandler::TrackCustomEvent(System.String, System.String, System.Collections.Generic.List`1<VoodooSauce+AnalyticsProvider>, System.Collections.Generic.Dictionary`2<System.String, System.Object>)`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Internal.Analytics.AmplitudeFunnelEventsHandler::OnTrackVoodooFunnel(System.String, System.String, System.Int32, System.Collections.Generic.Dictionary`2<System.String, System.Object>)`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Internal.Analytics.AmplitudeWrapper::FillEventSpecificContextVariables(System.Collections.Generic.Dictionary`2<System.String, System.Object>, System.String)`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Internal.Analytics.AmplitudeWrapper::FillGlobalContextVariables(System.Collections.Generic.Dictionary`2<System.String, System.Object>)`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Internal.Analytics.FirebaseAnalyticsEvent::UpdateParamKeysToFirebaseSpecific()`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Internal.Analytics.PerformanceTracking.CustomPerformanceTrackingManager::Dispose()`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Internal.Analytics.PerformanceTracking.FrameCounterService::Dispose()`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Internal.Firebase.FirebaseInitializer::OnInitComplete()`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Internal.LoggerSettingsManager::InitializeLogCategories()`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Internal.VoodooTune.VoodooTuneAbTestsTracker::TrackAbTestModifications(System.Collections.Generic.List`1<System.String>, System.Collections.Generic.List`1<System.String>, System.String)`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Internal.VoodooTune.WatchedRewardedVideosCounter::CleanUpOldCounts()`
- `Assembly-CSharp`: `System.Void Voodoo.Sauce.Privacy.PrivacyManager+VendorIdHelperAndroid::DisposeObjects(System.Collections.Generic.List`1<UnityEngine.AndroidJavaObject>)`
- `Assembly-CSharp`: `Voodoo.Live.IOperator Voodoo.Live.OperatorFactory::CreateOperator(System.String, Voodoo.Live.IBlackboard)`
- `Assembly-CSharp`: `Voodoo.Live.ItemQuantity[] Voodoo.Live.RandomReward::Resolve()`
- `Assembly-CSharp`: `Voodoo.Live.Shop.ShopSection Voodoo.Live.Shop.GameShop::GetSectionByProductId(System.String)`
- `Assembly-CSharp`: `Voodoo.Live.Transaction Voodoo.Live.TransactionRegistry::GetTransactionBySKU(System.String)`
- `Assembly-CSharp`: `Voodoo.Sauce.Internal.SDKs.SDK Voodoo.Sauce.Internal.Ads.MaxMediation.MaxMediationAdapterSDK::GetSDKInformations()`
- `CastleClashers.Game`: `Agent CastleClashers.HumanLikeBots.HumanLikeAimController::GetHighValueExposedUnit(System.Collections.Generic.List`1<Agent>, CastleClashers.HumanLikeBots.HumanLikeConfig)`
- `CastleClashers.Game`: `ArenaData SOHolder::GetArenaDataByArenaIndex(System.Int32)`
- `CastleClashers.Game`: `ArenaRewardsData+ArenaRewardSet ArenaRewardsData::GetArenaRewardSetForArena(System.Int32)`
- `CastleClashers.Game`: `BannerData ProfileInfoController::GetBannerData(System.String)`
- `CastleClashers.Game`: `BundleInfo ProfileInfoController::GetBundleInfo(System.String)`
- `CastleClashers.Game`: `CardData CardController::GetUnlockedUnequippedCardWithHighestLevel()`
- `CastleClashers.Game`: `CardData CardController::UnequipUnitOnLastEquippedPosition()`
- `CastleClashers.Game`: `CastleClashers.PvP.UnitHit[] PoisonCloudsController::CollectPendingTickHits(System.Int32)`
- `CastleClashers.Game`: `ChainOffer.ChainOfferSaveData ChainOffer.ChainOfferData::ToSaveData()`
- `CastleClashers.Game`: `Chests.CurrencyChestData CurrencyChestController::GetChestData(Chests.CurrencyChestType, Chests.CurrencyChestTier)`
- `CastleClashers.Game`: `CurrencyVisualData CurrencyController::GetCurrencyVisualData(CurrencyType)`
- `CastleClashers.Game`: `DecorationFoundataionSO CastleMaker::GetAnyFoundationDecoration()`
- `CastleClashers.Game`: `DecorationFoundataionSO FoundationUIController::GetAnyFoundationDecoration()`
- `CastleClashers.Game`: `DecorationRoofSO CastleMaker::GetRoofDecorationAtPosition(UnityEngine.Vector2)`
- `CastleClashers.Game`: `EmoteData ProfileInfoController::GetEmoteData(System.String)`
- `CastleClashers.Game`: `EngineerData EngineersController::GetEngineerData(System.String)`
- `CastleClashers.Game`: `EngineerData EngineersController::GetEngineerThatUnlocksAtArenaIndex(System.Int32)`
- `CastleClashers.Game`: `EngineerVisualData EngineersController::GetEngineerVisualData(System.String)`
- `CastleClashers.Game`: `ForgeRewardsData ForgeRewardsManager::GetRewardsDataBasedOnLevelThreshold(System.Int32)`
- `CastleClashers.Game`: `HelperItemSO UtilitiesController::GetEquippedDefensiveHelperItemData()`
- `CastleClashers.Game`: `HelperItemSO UtilitiesController::GetEquippedOffensiveHelperItemData()`
- `CastleClashers.Game`: `HelperItemSO UtilitiesController::GetHelperItemData(System.String)`
- `CastleClashers.Game`: `HelperItemSaveData UtilitiesController::GetHelperItemSaveData(System.String)`
- `CastleClashers.Game`: `ProfileIconData ProfileInfoController::GetProfileIconData(System.String)`
- `CastleClashers.Game`: `QuestDefinition QuestController::GetQuestDefinition(QuestType)`
- `CastleClashers.Game`: `QuestGoalAndRewardEntry QuestDefinition::GetGoalsAndRewardsEntry(QuestDifficulty)`
- `CastleClashers.Game`: `RarityDesign SOHolder::GetRarityDesign(RarityType)`
- `CastleClashers.Game`: `RoyalBlessing.DailyRewardEntry RoyalBlessing.RoyalBlessingConfigSO::GetRewardForDay(System.Int32)`
- `CastleClashers.Game`: `System.Boolean AnimatedWeeklyLeaderboardPanel+<>c__DisplayClass37_0::<CreateMilestoneAwareScrollTween>g__IsSlow|3(System.Single, System.Single)`
- `CastleClashers.Game`: `System.Boolean CardController::CanUpgradeAny(System.Int32&)`
- `CastleClashers.Game`: `System.Boolean CastleMaker::TryApplyFetchedDecorations(CastleClashers.HumanLikeBots.HumanLikeBotProfile)`
- `CastleClashers.Game`: `System.Boolean ChainOfferPopUp::StepHasChestReward(ChainOffer.ChainOfferStepData)`
- `CastleClashers.Game`: `System.Boolean EpiCoro.Internal.IAP.AvatarShopRotationController::HasUnownedItemsInCurrentRotation()`
- `CastleClashers.Game`: `System.Boolean EpiCoro.Internal.IAP.BannerShopRotationController::HasUnownedItemsInCurrentRotation()`
- `CastleClashers.Game`: `System.Boolean EpiCoro.Internal.IAP.DecorationShopRotationController::HasUnownedItemsInCurrentRotation()`
- `CastleClashers.Game`: `System.Boolean EpiCoro.Internal.IAP.EmoteShopRotationController::HasUnownedItemsInCurrentRotation()`
- `CastleClashers.Game`: `System.Boolean MapController+<DisableColldiersAtStart>d__37::MoveNext()`
- `CastleClashers.Game`: `System.Boolean MonetizationEvents.MonetizationEventConfigBase::IsDateSpecificActiveNow(System.DateTime)`
- `CastleClashers.Game`: `System.Boolean MonetizationEvents.MonetizationEventController::IsEventRegistered(System.String)`
- `CastleClashers.Game`: `System.Boolean ProfileInfoController::DidPurchaseAnyBundle(System.Collections.Generic.List`1<System.String>)`
- `CastleClashers.Game`: `System.Boolean ProfileInfoController::IsBundleInPremiumPacksAB(System.Collections.Generic.List`1<System.String>)`
- `CastleClashers.Game`: `System.Boolean QuestController::CanUseForgeLevelUpQuest(System.Int32)`
- `CastleClashers.Game`: `System.Boolean QuestController::CanUseUnitLevelUpQuest(System.Int32)`
- `CastleClashers.Game`: `System.Boolean QuestController::IsQuestInstanceWeekly(QuestInstance)`
- `CastleClashers.Game`: `System.Boolean TimedCastleBuildingController::CheckIfBuildingAtThatPosition(UnityEngine.Vector2)`
- `CastleClashers.Game`: `System.Boolean TimedCastleBuildingController::CheckIfUpgradingAtThatPosition(UnityEngine.Vector2)`
- `CastleClashers.Game`: `System.Boolean TimedUnitsUpgradeController::CheckIfUpgrading(System.String)`
- `CastleClashers.Game`: `System.Boolean UtilitiesController::AnyLevelsAvailableForHelperItem(System.String)`
- `CastleClashers.Game`: `System.Boolean UtilitiesController::AnyLevelsAvailableForWheel(System.String)`
- `CastleClashers.Game`: `System.Boolean UtilitiesController::AnyUpgradesAvailableForHelperItems(HelperItemType)`
- `CastleClashers.Game`: `System.Boolean UtilitiesController::AnyUpgradesAvailableForWheels()`
- `CastleClashers.Game`: `System.Boolean UtilitiesController::AreWheelsDiscovered(System.String)`
- `CastleClashers.Game`: `System.Boolean UtilitiesController::IsHelperItemDiscovered(System.String)`
- `CastleClashers.Game`: `System.Boolean UtilitiesController::IsHelperItemUnlocked(System.String)`
- `CastleClashers.Game`: `System.Boolean UtilitiesController::IsWheelUnlocked(System.String)`
- `CastleClashers.Game`: `System.Collections.Generic.Dictionary`2<System.String, System.Int32> CastleClashers.Rewards.ChestRoller::FilterMaxedCards(System.Collections.Generic.Dictionary`2<System.String, System.Int32>)`
- `CastleClashers.Game`: `System.Collections.Generic.Dictionary`2<System.String, System.Int32> ChestController::FilterMaxedCards(System.Collections.Generic.Dictionary`2<System.String, System.Int32>)`
- `CastleClashers.Game`: `System.Collections.Generic.Dictionary`2<System.String, System.Object> MatchTelemetryTrackerController::BuildWheelStartPayload(System.String, System.Int32)`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<Agent> UnitsController::GetAllExposed(PlayingSide)`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<ArenaReward> ArenaProgressionController::GetRewardsBetweenTrophies(System.Int32, System.Int32)`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<BannerData> ProfileInfoController::GetPossibleBanners(System.Int32, System.Int32, System.Boolean)`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<BannerData> ProfileInfoController::GetUncollectedBanners()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<BannerData> ProfileInfoController::GetUncollectedNonPremiumBanners()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<BannerData> ProfileInfoController::GetUncollectedPremiumBanners()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<BannerData> ProfileInfoController::GetUnlockedBanners()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<CastleClashers.HumanLikeBots.FetchedUnitPosition> CastleClashers.HumanLikeBots.PlayerProfileFetcher::MirrorUnitPositions(System.Collections.Generic.List`1<CastleClashers.HumanLikeBots.FetchedUnitPosition>, System.Int32)`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<DecorationData> CastleLoadoutDataFactory::ConvertFetchedDecorations(System.Collections.Generic.List`1<CastleClashers.HumanLikeBots.FetchedDecorationData>)`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<DecorationSO> CastleMaker::GetDecorationsAtPosition(UnityEngine.Vector2)`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<EmoteData> ProfileInfoController::GetDefaultEmotes()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<EmoteData> ProfileInfoController::GetEquippedEmotes()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<EmoteData> ProfileInfoController::GetPossibleEmotes(System.Int32, System.Int32, System.Boolean)`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<EmoteData> ProfileInfoController::GetUncollectedEmotes()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<EmoteData> ProfileInfoController::GetUncollectedNonPremiumEmotes()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<EmoteData> ProfileInfoController::GetUncollectedPremiumEmotes()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<EmoteData> ProfileInfoController::GetUnlockedButNotEquippedEmotes()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<EmoteData> ProfileInfoController::GetUnlockedEmotes()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<FoundationData> CastleLoadoutDataFactory::ConvertFetchedFoundations(System.Collections.Generic.List`1<CastleClashers.HumanLikeBots.FetchedFoundationData>)`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<FoundationData> CastleMaker::MirrorFoundationPositions(System.Collections.Generic.List`1<FoundationData>, System.Int32)`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<ProfileIconData> ProfileInfoController::GetPossibleAvatars(System.Int32, System.Int32)`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<ProfileIconData> ProfileInfoController::GetUncollectedIcons()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<ProfileIconData> ProfileInfoController::GetUncollectedNonPremiumIcons()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<ProfileIconData> ProfileInfoController::GetUncollectedPremiumIcons()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<ProfileIconData> ProfileInfoController::GetUnlockedIcons()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<System.Collections.Generic.Dictionary`2<System.String, System.Object>> MatchTelemetryTrackerController::BuildUnitsEndStatePayload(System.Collections.Generic.List`1<Agent>, PlayingSide)`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<System.Collections.Generic.Dictionary`2<System.String, System.Object>> MatchTelemetryTrackerController::BuildUnitsPayload(System.Collections.Generic.List`1<Agent>, PlayingSide)`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<System.String> UtilitiesController::GetPossibleHelperItemIdsForOpponent(HelperItemType)`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<System.ValueTuple`2<BannerData, System.Boolean>> EpiCoro.Internal.IAP.BannerShopRotationController::GetCurrentShopBanners()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<System.ValueTuple`2<DecorationSO, System.Boolean>> EpiCoro.Internal.IAP.DecorationShopRotationController::GetCurrentShopDecorations()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<System.ValueTuple`2<EmoteData, System.Boolean>> EpiCoro.Internal.IAP.EmoteShopRotationController::GetCurrentShopEmotes()`
- `CastleClashers.Game`: `System.Collections.Generic.List`1<System.ValueTuple`2<ProfileIconData, System.Boolean>> EpiCoro.Internal.IAP.AvatarShopRotationController::GetCurrentShopAvatars()`
- `CastleClashers.Game`: `System.Int32 ArenaProgressionController::NumberOfReceivedRewardsInArena(System.Int32)`
- `CastleClashers.Game`: `System.Int32 CardController::GetNumberOfUpgradesAvailable()`
- `CastleClashers.Game`: `System.Int32 CastleBuildingController::HowManyUpgradable()`
- `CastleClashers.Game`: `System.Int32 CastleClashers.HumanLikeBots.HumanLikeAimController::SelectLegendaryUnitFromValid(System.Collections.Generic.List`1<Agent>, System.Collections.Generic.List`1<System.Int32>)`
- `CastleClashers.Game`: `System.Int32 ChainOffer.ChainOfferConfigSO::GetFreeStepsCount()`
- `CastleClashers.Game`: `System.Int32 ChainOffer.ChainOfferConfigSO::GetPaidStepsCount()`
- `CastleClashers.Game`: `System.Int32 DeckController::GetNumberOfDeckSlotsAvailable(System.Int32, System.Int32)`
- `CastleClashers.Game`: `System.Int32 LevelCostTable::GetTotalPiecesForMaxLevel()`
- `CastleClashers.Game`: `System.Int32 MonetizationEvents.MonetizationEventSchedulerConfig::GetRotationCycleDays()`
- `CastleClashers.Game`: `System.Int32 ProfileInfoController::CalculateHighestForgeUnlockLevel()`
- `CastleClashers.Game`: `System.Int32 QuestController::GetUnclaimedCompletedQuestAmount()`
- `CastleClashers.Game`: `System.Int32 UtilitiesController::CalculateHighestForgeUnlockLevel()`
- `CastleClashers.Game`: `System.Int32 UtilitiesController::GetNumberOfUpgradesAvailable()`
- `CastleClashers.Game`: `System.Int32 UtilitiesController::GetTotalNumberOfUpgradesYetToGet()`
- `CastleClashers.Game`: `System.Int32 WeeklyLeaderboardController::GetPlayerRank(System.Int32)`
- `CastleClashers.Game`: `System.Single CardController::GetAverageLevelCards()`
- `CastleClashers.Game`: `System.Single CardController::GetAverageLevelOfEquippedCards()`
- `CastleClashers.Game`: `System.Single CastleClashers.HumanLikeBots.AimConfigSO::GetArenaOffsetMultiplier(System.Int32, System.Boolean)`
- `CastleClashers.Game`: `System.Single CastleClashers.HumanLikeBots.HumanLikeCastleBuilder::GetPlayerAverageCastleLevel()`
- `CastleClashers.Game`: `System.Single CastleClashers.HumanLikeBots.HumanLikePurchaseBoostTracker::GetCurrentCastleUpgradeAvg()`
- `CastleClashers.Game`: `System.Single MatchTelemetryTrackerController::ComputeDefenderUnitDamage(PlayingSide)`
- `CastleClashers.Game`: `System.Single RadialCarveGenerator::GetLastCarveRadius()`
- `CastleClashers.Game`: `System.Single UnitsController::ComputeAverageDamage(System.Collections.Generic.List`1<Agent>)`
- `CastleClashers.Game`: `System.Single UnitsController::ComputeAverageHealth(System.Collections.Generic.List`1<Agent>)`
- `CastleClashers.Game`: `System.String CastleClashers.HumanLikeBots.ArenaLogsManager::GetJsonData()`
- `CastleClashers.Game`: `System.String ChestOpenResult::ToString()`
- `CastleClashers.Game`: `System.ValueTuple`2<System.Int32, System.Int32> WeeklyLeaderboardController::GetRewardAmountForRank(System.Int32)`
- `CastleClashers.Game`: `System.Void ArenaProgressionPanel::PrepareArenas()`
- `CastleClashers.Game`: `System.Void ArenaProgressionPanel::SetArenaDatas()`
- `CastleClashers.Game`: `System.Void ArenaProgressionPanel::SetNextBigUnlockData(NextBigUnlockData)`
- `CastleClashers.Game`: `System.Void AvatarsShopSection::SetDataLegacy()`
- `CastleClashers.Game`: `System.Void BannersShopSection::SetDataLegacy()`
- `CastleClashers.Game`: `System.Void BotEmoteController::SetFixedEmotes(System.Collections.Generic.List`1<EmoteData>)`
- `CastleClashers.Game`: `System.Void CardController::UnlockCardFromArena(System.Int32)`
- `CastleClashers.Game`: `System.Void CardController::UnlockSpecificCard(CardData)`
- `CastleClashers.Game`: `System.Void CardData+SaveData::.ctor(System.Collections.Generic.List`1<CardData>)`
- `CastleClashers.Game`: `System.Void CastleClashers.UI.IAPOffersView::PopulateCards(System.Collections.Generic.List`1<CardValuePair>, UnityEngine.Transform)`
- `CastleClashers.Game`: `System.Void CastleMaker::ApplyPvpOpponentDecorations(CastleClashers.HumanLikeBots.FetchedPlayerProfile)`
- `CastleClashers.Game`: `System.Void CastleMaker::ApplyPvpOpponentFoundations(CastleClashers.HumanLikeBots.FetchedPlayerProfile)`
- `CastleClashers.Game`: `System.Void CastleMovement::TriggerParticleWithDelay()`
- `CastleClashers.Game`: `System.Void ChainOffer.ChainOfferData::MigratePendingRewardTypeKeys()`
- `CastleClashers.Game`: `System.Void ChainOfferPopUp::ClearStepItems()`
- `CastleClashers.Game`: `System.Void ChestOpeningPanel::ClearRewardUnitItems()`
- `CastleClashers.Game`: `System.Void ChestOpeningPanel::DetachEvents()`
- `CastleClashers.Game`: `System.Void CleanCockroachProjectile::OnDestroy()`
- `CastleClashers.Game`: `System.Void CosmeticsTabSwitcher::OnTabSelected(System.Int32)`
- `CastleClashers.Game`: `System.Void CosmeticsTabSwitcher::ToggleNotifyDotOnTab(System.Int32, System.Boolean)`
- `CastleClashers.Game`: `System.Void CurrencyController::UpdateAllShownToActual()`
- `CastleClashers.Game`: `System.Void CurrencyParticlePanel::ClearParticleImages()`
- `CastleClashers.Game`: `System.Void EmotesSelectionPanel::EquipProcess(EmoteData)`
- `CastleClashers.Game`: `System.Void EmotesSelectionPanel::StopEquippingProcess()`
- `CastleClashers.Game`: `System.Void EmotesShopSection::SetDataLegacy()`
- `CastleClashers.Game`: `System.Void EnviromentalEffectsController::StopAllEffects()`
- `CastleClashers.Game`: `System.Void EpiCoro.Internal.IAP.BuyForgePass::GrantReward(UnityEngine.Transform)`
- `CastleClashers.Game`: `System.Void EpiCoro.Internal.IAP.BuySpecialOffer::GrantReward(UnityEngine.Transform)`
- `CastleClashers.Game`: `System.Void EpiCoro.Internal.IAP.BuyUltimateUnitPack::GrantReward(UnityEngine.Transform)`
- `CastleClashers.Game`: `System.Void EpiCoro.Internal.IAP.CurrencyPurchaseUIItem::OnPurchaseComplete(System.Boolean)`
- `CastleClashers.Game`: `System.Void EpiCoro.Internal.IAP.IAPEventUIItem::GrantReward(System.Boolean)`
- `CastleClashers.Game`: `System.Void EpiCoro.Internal.IAP.NoneConsumableIAPUIItem::DisableGameObjects()`
- `CastleClashers.Game`: `System.Void EpiCoro.Internal.IAP.NoneConsumableIAPUIItem::TurnOffRotation()`
- `CastleClashers.Game`: `System.Void EpiCoro.Internal.IAP.RVUIItem::OnPurchaseComplete(System.Boolean)`
- `CastleClashers.Game`: `System.Void EpiCoro.Internal.IAP.StoreController::ResolveStoreNotificationDot()`
- `CastleClashers.Game`: `System.Void EpiCoro.Internal.IAP.StoreController::TryRestorePremiumUnitCosmeticsIfPurchased()`
- `CastleClashers.Game`: `System.Void FMUnitsGridHandler::Reset()`
- `CastleClashers.Game`: `System.Void FMUnitsGridHandler::StopAllItemAnimations()`
- `CastleClashers.Game`: `System.Void ForgeController::SaveCollectedRewards()`
- `CastleClashers.Game`: `System.Void ForgeController::SavePastPassRewards()`
- `CastleClashers.Game`: `System.Void ForgeExpParticlePanel::ClearParticleImages()`
- `CastleClashers.Game`: `System.Void ForgePassRewardsAlertPanel::Init()`
- `CastleClashers.Game`: `System.Void ForgePassRewardsAlertPanel::SetData()`
- `CastleClashers.Game`: `System.Void FoundationUIController::ReconcilePlacedFoundations()`
- `CastleClashers.Game`: `System.Void InfiniteScrollRect::UpdateCurrentPool()`
- `CastleClashers.Game`: `System.Void IngameUnitsGridHandler::Reset()`
- `CastleClashers.Game`: `System.Void IngameUnitsGridHandler::SetUnitKOed(System.String)`
- `CastleClashers.Game`: `System.Void IngameUnitsGridHandler::StopAllItemAnimations()`
- `CastleClashers.Game`: `System.Void LevelCostTable::RebuildIndex()`
- `CastleClashers.Game`: `System.Void MenuPanel::Init()`
- `CastleClashers.Game`: `System.Void MenuPanel::UpdateShopButtonNotify()`
- `CastleClashers.Game`: `System.Void MonetizationEvents.MonetizationEventController::InitializeScheduler()`
- `CastleClashers.Game`: `System.Void NewProfileCosmeticPanel::ClearSpawnedCosmetics()`
- `CastleClashers.Game`: `System.Void NewProfileCosmeticPanel::SetDataAvatars(System.Collections.Generic.List`1<System.String>)`
- `CastleClashers.Game`: `System.Void NewProfileCosmeticPanel::SetDataBanners(System.Collections.Generic.List`1<System.String>)`
- `CastleClashers.Game`: `System.Void NewProfileCosmeticPanel::SetDataEmotes(System.Collections.Generic.List`1<System.String>)`
- `CastleClashers.Game`: `System.Void PanelController::CloseSinglePanel(System.Type, System.Single)`
- `CastleClashers.Game`: `System.Void PanelController::OpenSinglePanel(System.Type)`
- `CastleClashers.Game`: `System.Void PanelController::OpenSinglePanelWithoutFade(System.Type)`
- `CastleClashers.Game`: `System.Void PoisonCloudsController::TickAndClean(System.Int32, PlayingSide)`
- `CastleClashers.Game`: `System.Void ProfileInfoController::HandleEmoteEquipSlots()`
- `CastleClashers.Game`: `System.Void ProfileInfoPanel::EnableAutoLinkAndRestart()`
- `CastleClashers.Game`: `System.Void QuestController::LoadDailyQuests()`
- `CastleClashers.Game`: `System.Void QuestController::LoadWeeklyQuests()`
- `CastleClashers.Game`: `System.Void QuestController::SaveDailyQuests()`
- `CastleClashers.Game`: `System.Void QuestController::SaveWeeklyQuests()`
- `CastleClashers.Game`: `System.Void QuestsProgressListener::BattleWon()`
- `CastleClashers.Game`: `System.Void QuestsProgressListener::CheckUniqueList(QuestType, System.String)`
- `CastleClashers.Game`: `System.Void RVButtonsController::OnInitialized()`
- `CastleClashers.Game`: `System.Void RVButtonsController::ResetAllRVButtons()`
- `CastleClashers.Game`: `System.Void RVButtonsController::ShowAllRVButtons()`
- `CastleClashers.Game`: `System.Void RVButtonsController::UnsubscribeAllButtons()`
- `CastleClashers.Game`: `System.Void RVButtonsController::UpdateNoRVBought()`
- `CastleClashers.Game`: `System.Void RecordingObjectDisabler::DisableObjects()`
- `CastleClashers.Game`: `System.Void RewardedAdController::OnInitialized()`
- `CastleClashers.Game`: `System.Void SDFSpriteGenerator_SR::OnDrawGizmosSelected()`
- `CastleClashers.Game`: `System.Void SocialInteractionsHandler::TogglePlayersHolder(System.Boolean)`
- `CastleClashers.Game`: `System.Void SpecialOffer_StoreController::PopulateCards(System.Collections.Generic.List`1<CardValuePair>, UnityEngine.Transform)`
- `CastleClashers.Game`: `System.Void TopBarPanel::SetCurrencySetup(CurrencySetupType)`
- `CastleClashers.Game`: `System.Void TopBarPanelIAP::UpdateCurrencyFields()`
- `CastleClashers.Game`: `System.Void Tournament.TournamentController+<>c__DisplayClass145_0::<FetchAllTournamentConfigs>b__0(NakamaHttp.CastleClashersTournamentGetConfigsResp)`
- `CastleClashers.Game`: `System.Void UICurrencySetup::UpdateCurrencyFields()`
- `CastleClashers.Game`: `System.Void UnitsController::DetermineEnemyUnitsToSpawn()`
- `CastleClashers.Game`: `System.Void UnitsController::InitUnitsOnBeginMatch()`
- `CastleClashers.Game`: `System.Void UnitsController::VampireHealAllUnits(PlayingSide, System.Single)`
- `CastleClashers.Game`: `System.Void UnitsHolder::EnableAgentByUnitData(UnitData)`
- `CastleClashers.Game`: `System.Void UnitsHolder::EnableAgentWithCardId(System.String)`
- `CastleClashers.Game`: `System.Void UnitsHolder::SetAgentAnimationByUnitData(UnitData, System.Boolean)`
- `CastleClashers.Game`: `System.Void UnitsPanel::CheckWildCardsTutorial()`
- `CastleClashers.Game`: `System.Void UnitsPanel::EquipProcess(CardData)`
- `CastleClashers.Game`: `System.Void UnitsPanel::StopEquippingProcess()`
- `CastleClashers.Game`: `System.Void UnlockForgeRewardItem::SetData(System.Int32, ForgeRewardType, System.Boolean)`
- `CastleClashers.Game`: `System.Void UtilitiesController::SaveHelperItemsData()`
- `CastleClashers.Game`: `System.Void UtilitiesController::SaveWheelsData()`
- `CastleClashers.Game`: `System.Void UtilitiesController::UnlockNewlyAddedUtilities(System.Int32)`
- `CastleClashers.Game`: `System.Void UtilitiesPanel::ToggleSelectedBorderOnCards(HelperItemSO)`
- `CastleClashers.Game`: `System.Void UtilitiesPanel::ToggleSelectedBorderOnCards(WheelData)`
- `CastleClashers.Game`: `System.Void UtilitiesTabSwitcher::OnTabSelected(System.Int32)`
- `CastleClashers.Game`: `System.Void UtilitiesTabSwitcher::ToggleNotifyDotOnTab(System.Int32, System.Boolean)`
- `CastleClashers.Game`: `System.Void VideoController::Awake()`
- `CastleClashers.Game`: `System.Void VoodoDebuggerController+<>c__DisplayClass38_0::<AddUnitPieces>b__0()`
- `CastleClashers.Game`: `System.Void VoodoDebuggerController::<UnlockAllUnits>b__48_0()`
- `CastleClashers.Game`: `System.Void WeeklyHistoryData+SaveData::.ctor(System.Collections.Generic.List`1<WeeklyResult>, WeeklyResult)`
- `CastleClashers.Game`: `Tournament.TournamentsData Tournament.TournamentsData::FromSaveData(Tournament.TournamentsData+SaveData)`
- `CastleClashers.Game`: `Tournament.TournamentsData+SaveData Tournament.TournamentsData::ToSaveData()`
- `CastleClashers.Game`: `TrainerData TrainersController::GetTrainerData(System.String)`
- `CastleClashers.Game`: `TrainerData TrainersController::GetTrainerThatUnlocksAtArenaIndex(System.Int32)`
- `CastleClashers.Game`: `TrainerVisualData TrainersController::GetTrainerVisualData(System.String)`
- `CastleClashers.Game`: `UICurrencySetup TopBarPanel::GetCurrencySetup(CurrencySetupType)`
- `CastleClashers.Game`: `UnityEngine.GameObject WorldSpaceUI::GetOrAssignIndicator(UnityEngine.GameObject)`
- `CastleClashers.Game`: `UnityEngine.Vector2 CastleManager::GetMinMaxY()`
- `CastleClashers.Game`: `WheelData UtilitiesController::GetEquippedWheelData()`
- `CastleClashers.Game`: `WheelData UtilitiesController::GetWheelData(System.String)`
- `CastleClashers.Game`: `WheelSaveData UtilitiesController::GetWheelSaveData(System.String)`
- `CastleClashers.Rules`: `CastleClashers.Protobuf.CCInventoryState CastleClashers.Rules.Engine::NewState()`

</details>
