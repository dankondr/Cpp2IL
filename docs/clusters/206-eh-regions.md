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
lane boundary, in its own commit `a64ad3f6`. It follows only bounded, pure ARM64 B
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

## Verification, third continuation

Task: dankondr/castle-recovery#206 (slice 2). Continues PR #175 and addresses
[dankondr/Cpp2IL#80](https://github.com/dankondr/Cpp2IL/issues/80).
The separately committed class-predicate recognizer remains the authorized
castle-recovery#208 exception; this continuation changes no key-function recognition.

Control: `238110429dbf6ca2034ba327b4cf986277b87e03` (`development`, merged #179). The branch was rebased first
onto #177 and again when #179 landed during validation. Final code: `e0cf9ddb`.
Both full sweeps process 69,982 native methods, emit 183 assemblies and report
178,274 methods. Outputs: `astra206-r5-control` and `astra206-r5-verified`.

| Scope | Methods | Diagnosed control → branch | Newly clean | Clean regressions | Pads control → branch |
|---|---:|---:|---:|---:|---:|
| All | 178,274 | 16,768 → 16,228 | 540 | 0 | 54,380 → 47,263 |
| Game-owned | 25,348 | 4,274 → 3,944 | 330 | 0 | 15,537 → 10,816 |
| CastleClashers.Game | 14,423 | 2,673 → 2,442 | 231 | 0 | 9,865 → 6,659 |
| Castle-building owners + nested types | 280 | 100 → 87 | 13 | 0 | 882 → 684 |

No method gains a diagnostic in any scope; the regression list is empty. The final
clean list is below. Warning text was not hidden or reworded.

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
- Full rebased Core.Tests: **1199/1199**.
- LibCpp2ILTests: **12/12**; JitOracle.Tests: **9/9**.
- Focused EH tests: **36/36**, including serialized-assembly execution through the real emitter. These run after
  the final assembly-identity and unscaled-index guards.
- Disabling catch-local registration and returning-closure continuation makes six
  of these regression cases fail; restoring the changes passes them.
- Both audits: **170,144 valid**, **416 invalid**,
  7,714 partial/no-body entries. **0 status transitions**,
  including **0 valid→invalid**. The broader Bootstrap reachability gate remains
  blocked at 29/29 in both scans; scan's nonzero exit is not an ILVerify regression.

### Additional native/IL review

The 16 finally examples in the checked-in report remain the original clean-method
review; all 16 serialized bodies are unchanged in the final output. For this
continuation, all 14 methods with new clauses were read against ARM64 and LSDA.
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
Keep #175 a draft. 557 owned methods retain pads, including
111 pad-only methods.

| Remaining coverage | Methods | Remaining pad messages |
|---|---:|---:|
| No native proof | 393 | 6,844 |
| All native pads proven, IL region refused | 78 | 1,464 |
| Mixed proven/unproven pads | 86 | 2,508 |

Native finally proofs still cover 7,084 pads. Typed catches prove 454 more,
for a union of 7,538; 2,817 proven pads remain
unmaterialized. A proof can cover more native sites than survive in emitted IL.

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
  not edited. The prior get_Current hoisting observation remains with that lane.
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
| type: synthetic default in operand slot | 709 | 152 | 1754 |
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
| type: synthetic default in operand slot | 480 | 79 | 1349 |
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
| type: synthetic default in operand slot | 709 | 170 | 1754 |
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
| type: synthetic default in operand slot | 480 | 88 | 1349 |
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
