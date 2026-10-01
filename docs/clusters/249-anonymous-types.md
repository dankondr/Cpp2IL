# castle-recovery#249 — compiler-generated display classes and anonymous types

Cluster: `lane:types-ssa`. Compiler-generated closures (`<>c__DisplayClass*`),
anonymous types (`<>f__AnonymousType*`), `??` null-coalescing and cached
delegates. The C# compiler lowers these to a small set of IL idioms; the
decompiler only restores the source syntax (`new { … }`, lambdas, `??`) when
the emitted IL has exactly those shapes. The lifter must emit them.

## Rules

- A branch on a flag defined as `x == 0` / `x != 0` in the same block is the
  null-test idiom: emit `load x; brfalse/brtrue` instead of computing the flag
  local (`IlGenerator.TryEmitInlinedBranchCondition`). A generic-parameter
  operand is boxed first — `brtrue`/`brfalse` cannot take `!!T` — matching the
  reference-slot coercion the comparison itself used.
- `x ?? (x = v)` cache-store merges (the phi copies on both edges) canonicalize
  to one `merged = x` at the join head: after the store, `x` holds `v`, so a
  single post-join read is identical on both paths — the shape ILSpy's cached-
  `??` transforms fold (`CoalesceStoreRecovery`, in `MethodAnalysisContext`
  between `ConstantBranchFolder` and `EqualityBranchInverter`). Removing a merge
  copy can leave a dedicated copy-trampoline block empty; re-run
  `RemoveEmptyBlocks` so no branch operand keeps pointing at it.
- A null check on a `Newobj` result is constant (`== 0` → false, `!= 0` →
  true): fold the check and drop the edge it can never take, even when the
  branch target's throw provenance is undecidable
  (`InjectedCheckRemover.AllocatedNullCheckValue` + `DropImpossibleEdge`,
  before the `GetInjectedThrowType` gate). The fold keeps the edge when the
  drop would orphan instructions inside a landing pad's call-site range —
  their deletion would strip the coverage that pad's region proof needs
  (`OrphansCoveredInstructions` walks the transitively-orphaned block set and
  refuses the drop when any of its instructions fall inside
  `LandingPadRegion.CallSites` ranges).
- Phi operands are positional on a block's `Predecessors` list:
  `phi.Operands[1+i]` is the value arriving on the edge from `Predecessors[i]`.
  Any pass that removes an edge (or a block) while SSA is still built must drop
  that edge's operand slot from each phi in the successor, or every remaining
  predecessor reads the next edge's value when phi removal materializes the
  edge copies (`ISILControlFlowGraph.RemovePredecessor`, used by
  `DropImpossibleEdge`, `RemoveUnreachableBlocks` and `RemoveEmptyBlocks`).
- Anonymous types arrive from metadata already faithful (compiler name,
  `CompilerGenerated`, ctor parameters naming the properties, get-only
  properties over `<X>i__Field`); once the IL around their construction is
  canonical ILSpy emits `new { … }` and omits the declaration — fixing the
  instruction shapes is what removes the CS0246s, not a change to type
  emission.

## Tests

- `InjectedExceptionGuardTests.NullCheckOnFreshAllocationIsFolded` /
  `NullCheckWithoutAllocationIsNotFolded` /
  `DroppedImpossibleEdgeKeepsPhiOperandAlignment` /
  `ImpossibleEdgeInsideCallSiteRangeIsKept`
- `CoalesceStoreRecoveryTests.PairedMergesCollapseToSingleJoinHeadRead` /
  `NullCheckedBranchReadsTheFieldInline` /
  `NullCheckedGenericParameterBoxesBeforeTheBranch` /
  `EmptiedCopyTrampolineIsRetargeted`

## Attribution (recovery table)

`game_owned_table.py` on control and branch (fixed revision):

Control:

| assembly | verified | compiles_unverified | incomplete | stub | invalid_il | fails_compile | no_body | methods | refmode errors |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `Assembly-CSharp` | 0 | 7,258 | 1,307 | 298 | 0 | 0 | 561 | 9,424 | 11 |
| `CastleClashers.Core` | 0 | 159 | 72 | 6 | 0 | 0 | 4 | 241 | 12 |
| `CastleClashers.Game` | 0 | 11,096 | 2,434 | 800 | 0 | 0 | 93 | 14,423 | 25 |
| `CastleClashers.Internal.Services` | 0 | 43 | 9 | 11 | 0 | 0 | 0 | 63 | 6 |
| `CastleClashers.Internal.UI` | 0 | 539 | 78 | 4 | 0 | 0 | 3 | 624 | 10 |
| `CastleClashers.Rules` | 0 | 210 | 9 | 4 | 0 | 0 | 0 | 223 | 0 |
| `CastleClashers.Rules.Client` | 0 | 12 | 1 | 4 | 0 | 0 | 0 | 17 | 0 |
| `CastleClashers.SDKGlue` | 0 | 44 | 1 | 5 | 0 | 0 | 58 | 108 | 0 |
| `CastleClashers.VoodooTune` | 0 | 52 | 7 | 7 | 0 | 0 | 6 | 72 | 0 |
| `Ranked` | 0 | 116 | 18 | 4 | 0 | 0 | 15 | 153 | 1 |
| **total** | **0** | **19,529** | **3,936** | **1,143** | **0** | **0** | **740** | **25,348** | **65** |

Branch:

| assembly | verified | compiles_unverified | incomplete | stub | invalid_il | fails_compile | no_body | methods | refmode errors |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `Assembly-CSharp` | 0 | 7,485 | 1,307 | 71 | 0 | 0 | 561 | 9,424 | 94 |
| `CastleClashers.Core` | 0 | 161 | 72 | 4 | 0 | 0 | 4 | 241 | 4 |
| `CastleClashers.Game` | 0 | 11,598 | 2,434 | 298 | 0 | 0 | 93 | 14,423 | 2 |
| `CastleClashers.Internal.Services` | 0 | 46 | 9 | 8 | 0 | 0 | 0 | 63 | 6 |
| `CastleClashers.Internal.UI` | 0 | 539 | 78 | 4 | 0 | 0 | 3 | 624 | 10 |
| `CastleClashers.Rules` | 0 | 210 | 9 | 4 | 0 | 0 | 0 | 223 | 0 |
| `CastleClashers.Rules.Client` | 0 | 12 | 1 | 4 | 0 | 0 | 0 | 17 | 0 |
| `CastleClashers.SDKGlue` | 0 | 45 | 1 | 4 | 0 | 0 | 58 | 108 | 0 |
| `CastleClashers.VoodooTune` | 0 | 55 | 7 | 4 | 0 | 0 | 6 | 72 | 0 |
| `Ranked` | 0 | 116 | 18 | 4 | 0 | 0 | 15 | 153 | 1 |
| **total** | **0** | **20,267** | **3,936** | **405** | **0** | **0** | **740** | **25,348** | **117** |

Status changes: 738 methods move `stub` → `compiles_unverified`
(`CastleClashers.Game` −502, `Assembly-CSharp` −227,
`CastleClashers.Internal.Services` −3, `CastleClashers.Core` −2,
`CastleClashers.SDKGlue` −1, `CastleClashers.VoodooTune` −3). No method
becomes `fails_compile`, `invalid_il` or `no_body` anywhere; `verified`
unchanged at 0. The +52 refmode rows are the exposure/new rows split out
below, not new defects: every game-owned method's status is unchanged or
better.

## Unmasked rows (declaration-deletion control)

Roslyn stops reporting body-level diagnostics in a file that still has
declaration-level errors, so clearing the 39 anonymous-type declaration sites
in control's tree (same deletions as the branch produces, applied by hand)
exposes what the branch's new rows were hiding. Comparing the doctored
control compile against the branch compile, grouped by error code and file:

| assembly / file | code | branch − control | in doctored control |
|---|---|---:|---:|
| `Assembly-CSharp` AdDisplayConditions.cs | CS1061 | +1 | 1 |
| `Assembly-CSharp` AdnSdkCallbacks.cs | CS0103 | +1 | 1 |
| `Assembly-CSharp` AdnSdkCallbacks.cs | CS0165 | +1 | 1 |
| `Assembly-CSharp` AndroidAppInfo.cs | CS0104 | +1 | 1 |
| `Assembly-CSharp` AndroidNativeVolumeService.cs | CS0161 | +1 | 1 |
| `Assembly-CSharp` AppOpen.cs | CS0103 | +1 | 1 |
| `Assembly-CSharp` BaseOperator.cs | CS1061 | +2 | 2 |
| `Assembly-CSharp` CMPiOSListenerHelper.cs | CS1061 | +2 | 2 |
| `Assembly-CSharp` CmpAndroidLoggerProxy.cs | CS0117 | +1 | 1 |
| `Assembly-CSharp` CmpAndroidLoggerProxy.cs | CS1729 | +1 | 1 |
| `Assembly-CSharp` ConditionParser.cs | CS0103 | +1 | 1 |
| `Assembly-CSharp` ConditionParser.cs | CS1061 | +10 | 10 |
| `Assembly-CSharp` ConfigLoader.cs | CS0104 | +3 | 3 |
| `Assembly-CSharp` ConsentMessenger.cs | CS0246 | +1 | 0 |
| `Assembly-CSharp` CurrencyHelper.cs | CS0103 | +1 | 1 |
| `Assembly-CSharp` CustomConsentClient.cs | CS0117 | +1 | 1 |
| `Assembly-CSharp` CustomConsentClient.cs | CS1729 | +1 | 1 |
| `Assembly-CSharp` CustomPerformanceTrackingManager.cs | CS0117 | +1 | 1 |
| `Assembly-CSharp` CustomPerformanceTrackingManager.cs | CS7036 | +1 | 1 |
| `Assembly-CSharp` ExponentialBackoff.cs | CS0103 | +2 | 2 |
| `Assembly-CSharp` FcmController.cs | CS0165 | +1 | 1 |
| `Assembly-CSharp` FeatureClient.cs | CS0104 | +3 | 3 |
| `Assembly-CSharp` FirebaseAnalyticsEvent.cs | CS0103 | +1 | 1 |
| `Assembly-CSharp` FixedIntervalFrameCounter.cs | CS0117 | +1 | 1 |
| `Assembly-CSharp` Inventory.cs | CS0269 | +1 | 1 |
| `Assembly-CSharp` Inventory.cs | CS0411 | +1 | 0 |
| `Assembly-CSharp` Inventory.cs | CS8374 | +1 | 1 |
| `Assembly-CSharp` Inventory.cs | CS8917 | +3 | 0 |
| `Assembly-CSharp` IosDeviceDpiMapping.cs | CS0103 | +1 | 1 |
| `Assembly-CSharp` MaxNativeAdsSdkCallbacks.cs | CS0103 | +1 | 1 |
| `Assembly-CSharp` MaxNativeAdsSdkCallbacks.cs | CS0165 | +1 | 1 |
| `Assembly-CSharp` NewManifestUtilsImpl.cs | CS0269 | +1 | 1 |
| `Assembly-CSharp` NewManifestUtilsImpl.cs | CS8374 | +4 | 6 |
| `Assembly-CSharp` PrivacyManager.cs | CS0165 | +1 | 1 |
| `Assembly-CSharp` PrivacyManager.cs | CS1673 | +14 | 12 |
| `Assembly-CSharp` PrivacyUIManager.cs | CS0103 | +1 | 1 |
| `Assembly-CSharp` RateBox.cs | CS1061 | +1 | 1 |
| `Assembly-CSharp` RetroEffectCycler.cs | CS0104 | +1 | 1 |
| `Assembly-CSharp` RetroFireProjectile.cs | CS0104 | +1 | 1 |
| `Assembly-CSharp` RulesetParser.cs | CS1061 | +1 | 1 |
| `Assembly-CSharp` ShopManager.cs | CS0104 | +4 | 4 |
| `Assembly-CSharp` Sourcepoint.cs | CS1673 | +1 | 1 |
| `Assembly-CSharp` SpAndroidNativeUtils.cs | CS0165 | +1 | 0 |
| `Assembly-CSharp` SpClientProxy.cs | CS0117 | +1 | 1 |
| `Assembly-CSharp` SpClientProxy.cs | CS1061 | +2 | 2 |
| `Assembly-CSharp` SpClientProxy.cs | CS1729 | +1 | 1 |
| `Assembly-CSharp` StandardOperatorFactory.cs | CS0103 | +1 | 1 |
| `Assembly-CSharp` VoodooLive.cs | CS0104 | +1 | 1 |
| `Assembly-CSharp` VoodooLiveController.cs | CS0165 | +1 | 1 |
| `Assembly-CSharp` VoodooLiveDemo.cs | CS0104 | +2 | 2 |
| `Assembly-CSharp` VoodooLivePaginationDebugger.cs | CS0121 | +1 | 1 |
| `Assembly-CSharp` VoodooSauceBehaviour.cs | CS0104 | +1 | 1 |
| `Assembly-CSharp` VoodooTuneManager.cs | CS0165 | +1 | 1 |
| `Assembly-CSharp` VoodooTuneManager.cs | CS1673 | +1 | 1 |
| `Assembly-CSharp` WebRequest.cs | CS0104 | +1 | 1 |
| `EasySave3` ES3Cloud.cs | CS0161 | +8 | 8 |
| `EasySave3` ES3File.cs | CS0165 | +1 | 1 |
| `EasySave3` ES3File.cs | CS1510 | +1 | 1 |
| `EasySave3` ES3File.cs | CS8172 | +1 | 1 |
| `EasySave3` ES3FileStream.cs | CS0117 | +1 | 1 |
| `EasySave3` ES3FileStream.cs | CS1729 | +1 | 1 |
| `EasySave3` ES3ReferenceMgrBase.cs | CS0246 | +4 | 0 |
| `EasySave3` ES3Reflection.cs | CS0103 | +1 | 1 |
| `EasySave3` ES3Reflection.cs | CS8917 | +2 | 1 |
| `EasySave3` ES3Stream.cs | CS0121 | +1 | 1 |
| `EasySave3` ES3TypeMgr.cs | CS0165 | +1 | 1 |
| `EasySave3` ES3Type_Burst.cs | CS0103 | +1 | 1 |
| `EasySave3` ES3Type_ES3Ref.cs | CS7036 | +1 | 1 |
| `EasySave3` ES3Type_ForceOverLifetimeModule.cs | CS0103 | +1 | 1 |
| `EasySave3` ES3Type_IntPtr.cs | CS7036 | +1 | 1 |
| `EasySave3` ES3Type_LightsModule.cs | CS0103 | +1 | 1 |
| `EasySave3` ES3Type_LimitVelocityOverLifetimeModule.cs | CS0103 | +1 | 1 |
| `EasySave3` ES3Type_MainModule.cs | CS0103 | +1 | 1 |
| `EasySave3` ES3Type_MinMaxCurve.cs | CS0103 | +1 | 1 |
| `EasySave3` ES3Type_MinMaxGradient.cs | CS0103 | +1 | 1 |
| `EasySave3` ES3Type_NoiseModule.cs | CS0103 | +1 | 1 |
| `EasySave3` ES3Type_RotationBySpeedModule.cs | CS0103 | +1 | 1 |
| `EasySave3` ES3Type_RotationOverLifetimeModule.cs | CS0103 | +1 | 1 |
| `EasySave3` ES3Type_ShapeModule.cs | CS0103 | +1 | 1 |
| `EasySave3` ES3Type_SizeBySpeedModule.cs | CS0103 | +1 | 1 |
| `EasySave3` ES3Type_SizeOverLifetimeModule.cs | CS0103 | +1 | 1 |
| `EasySave3` ES3Type_TextureSheetAnimationModule.cs | CS0103 | +1 | 1 |
| `EasySave3` ES3Type_TrailModule.cs | CS0103 | +1 | 1 |
| `EasySave3` ES3Type_Type.cs | CS7036 | +1 | 1 |
| `EasySave3` ES3Type_UIntPtr.cs | CS7036 | +1 | 1 |
| `EasySave3` ES3Type_VelocityOverLifetimeModule.cs | CS0103 | +1 | 1 |
| `EasySave3` ES3Type_bool.cs | CS7036 | +1 | 1 |
| `EasySave3` ES3Type_byte.cs | CS7036 | +1 | 1 |
| `EasySave3` ES3Type_char.cs | CS7036 | +1 | 1 |
| `EasySave3` ES3Type_double.cs | CS7036 | +1 | 1 |
| `EasySave3` ES3Type_float.cs | CS7036 | +1 | 1 |
| `EasySave3` ES3Type_int.cs | CS7036 | +1 | 1 |
| `EasySave3` ES3Type_long.cs | CS7036 | +1 | 1 |
| `EasySave3` ES3Type_sbyte.cs | CS7036 | +1 | 1 |
| `EasySave3` ES3Type_short.cs | CS7036 | +1 | 1 |
| `EasySave3` ES3Type_string.cs | CS7036 | +1 | 1 |
| `EasySave3` ES3Type_uint.cs | CS7036 | +1 | 1 |
| `EasySave3` ES3Type_ulong.cs | CS7036 | +1 | 1 |
| `EasySave3` ES3Type_ushort.cs | CS7036 | +1 | 1 |

Grouped by (assembly, error code, message): the branch has 52 error rows
control lacks. 42 of the 49 non-`DisplayClass` rows appear verbatim in the
doctored control compile — the exposure set. The seven that do not are the
same defects under neighbouring codes, all inside the deleted-declaration
methods:

| row | branch | doctored control | same defect as |
|---|---:|---:|---|
| `Inventory.cs` CS0411 `SelectMany` type inference | 1 | CS0117×12 | deleted `<>9__*` display-class methods — the doctored build reports the call sites as missing members instead |
| `Inventory.cs` CS8917 delegate inference | 3 | — | same |
| `ES3Reflection.cs` CS8917 delegate inference | 2 | 1 | same |
| `SpAndroidNativeUtils.cs` CS0165 `CS$<>8__locals0` | 1 | 0 | display-class local left without its declaration — same partial fold |
| `NewManifestUtilsImpl.cs` CS8374 `xmlNode2`/`xmlNode5` | +2 | xmlNode4/6 rows present | narrower-escape ref-assign family, two more sites under the branch's local naming |
| `PrivacyManager.cs`/`Sourcepoint.cs`/`VoodooTuneManager.cs` CS1673 | 16 | 14 | lambda-in-struct family already proven masked, two additional sites |

## New rows

Five `<>c__DisplayClass*` CS0246 remain net-new versus control (down from six
before the call-site guard — the seventh site now keeps its edge and its
declaration):

| error | method | control status | branch status | defect and lane |
|---|---|---|---|---|
| `<>c__DisplayClass32_0` CS0246 ×2 (ES3ReferenceMgrBase.cs 1082/1184) | `ES3ReferenceMgrBase::Remove(Object)` | `lifted-unverified` (48 diags) | `lifted-unverified` (47) | ILSpy drops the display-class declaration but leaves `default`-typed references; `lane:types-ssa` follow-up: keep the declaration when references remain |
| `<>c__DisplayClass33_0` CS0246 ×2 (ES3ReferenceMgrBase.cs 1212/1299) | `ES3ReferenceMgrBase::Remove(Int64)` | `lifted-unverified` (40) | `lifted-unverified` (39) | same |
| `<>c__DisplayClass2_0<>` CS0246 ×1 (ConsentMessenger.cs 159) | `ConsentMessenger::Broadcast<T>(object[])` | `lifted-unverified` (23) | `lifted-unverified` (23) | same |

Each affected method was already non-`verified` in control and stays in the
same state; none of the diagnostics is suppressed. The residual is the
ILSpy-side partial fold — the declared-but-unreferenced display class is
dropped while `default` field references keep the type name alive — routed
as a `lane:types-ssa` task on the same shape this cluster documents.
