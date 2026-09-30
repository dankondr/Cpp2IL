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
an overlapping write. Direct and indirect calls clobber caller-saved registers.
A recovered no-return call cannot fall through into the next out-of-line throw site.
The normal dataflow and handler traversal have explicit limits; exceeding them
retains the diagnostic.

`ExceptionRegionRecovery` uses the already emitted, resolved normal cleanup IL.
It requires one entry, no extra protected native calls, equivalent cleanup copies,
and cleanup locals defined before entry. Every incoming edge to an erased cleanup
must exit a proven region. Regions must be disjoint or properly nested, and nested
cleanup order must agree with the native handler. The emitter moves the blocks into
contiguous clauses, preserves fallthroughs, rewrites exits to `leave`, and appends
`endfinally`. Shared entry anchors prevent branches into a try body.

Typed catch requires an already recognized `Object::IsInst` against a resolved
exception type, original-exception propagation on mismatch, and a supported handler
that joins a void epilogue. The exception is stored in a local of that type; the
handler ends with `leave` to the merge. Unknown `Class::IsAssignableFrom` calls are
left to the key-function lane. Captured native locals, arbitrary catch CFGs, filters
and fault blocks are not guessed.

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
- a recognized typed catch receives the actual exception and rejoins the method;
  an unknown class test remains diagnosed.

`ElfEhTablesTests` checks absolute and indirect PC-relative RTTI, a linked
catch-plus-cleanup action chain, and a cyclic malformed chain that preserves its
call site without a proof.

## Native/IL review

Reviewed eleven newly clean methods against ARM64 disassembly, LSDA ranges and
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

The CardController example protects native calls at 3EE8FC0, 3EE8FD4, 3EE8FDC
and 3EE9020. GetEnumerator at 3EE8FAC, Dispose at 3EE8FF8, and the pre-loop null
throw at 3EE9024 remain outside the try. The native handler saves the exception,
loads the enumerator address from `[sp+0x10]`, calls Dispose, and rethrows. Its
auxiliary cleanup closure reads the same exception/receiver record.

## r241 verification

Control is the branch point `efd37627ac7ad9043d5e9434f152fedfce2a19f8`, which was
`origin/development` when this work began. Both full sweeps processed 69,982 native
methods and emitted 183 assemblies. The final sweep took 205.8 seconds locally.

| Scope | Methods | Diagnosed, control → branch | Newly clean | Clean regressions | Pad messages, control → branch |
|---|---:|---:|---:|---:|---:|
| All assemblies | 178,274 | 17,303 → 16,803 | 500 | 0 | 54,380 → 48,017 |
| Game-owned | 25,348 | 4,515 → 4,215 | 300 | 0 | 15,537 → 11,366 |
| CastleClashers.Game | 14,423 | 2,860 → 2,651 | 209 | 0 | 9,865 → 6,933 |
| Four castle-building types and descendants | 280 | 130 → 120 | 10 | 0 | 882 → 696 |

No method gained a diagnostic, including already diagnosed methods. All 300 newly
clean game-owned methods previously had only pad diagnostics. The castle-building
rows newly clean are the ten non-CardController entries in the review table.
The scope includes every exact owner and `Owner+...` descendant in the sidecar,
keyed by assembly/token: this control measures 280/130, rather than the brief's
273/124. All 280 identities are distinct; 278 are lifted and two use existing
semantic recovery.

Full recovery-audit comparison by assembly/output signature: 169,882 ILVerify-valid
and 678 ILVerify-invalid methods in both runs; zero status transitions, including
zero valid-to-invalid transitions. The old invalid methods are not fixed here.

Checks: Core.Tests 1,112/1,112; after the final mutable-load guard, the focused EH
suite passed 11/11. LibCpp2ILTests passed 12/12 and JitOracle.Tests 9/9 on the final
source. Build succeeded with the same 13 pre-existing warnings. The final serialized
IL for the eleven reviewed methods is identical to the reviewed output.

## Gaps

The 300-method clean target is met. The requested greater-than-half drop in pad
messages is **not met**: the measured reduction is 4,171/15,537 (26.8%). 580
owned methods retain 11,366 pad diagnostics, including 111 pad-only methods.

| Remaining category | Methods | Remaining pad messages |
|---|---:|---:|
| No native cleanup proof | 437 | 7,821 |
| Mixed proven and unproven native pads | 59 | 2,079 |
| All native pads proven, but one or more IL regions refused | 84 | 1,466 |

The native effect analysis proves 6,495 pads across the original 1,019 methods;
2,324 of these do not meet the IL materialization checks. Those checks require a
single resolved cleanup call, locals initialized before entry, no uncovered native
calls, no switch rewriting, and disjoint/nested regions. Unsupported cleanup
arguments, compound/returning closures, state-machine dispatch, and unmatched
native effects remain explicit gaps.

Measured examples:

- `CastleMaker.SpawnShields`: 224 remaining pads, 93 native proofs;
  `SpawnShieldsFromPlacements`: 217 remaining, 50 native proofs. Their compound
  cleanup/control-flow shapes cannot yet be materialized.
- `EpiCoro.Internal.IAP.StoreController.OpenSection`: all 152 native pads proven,
  but its IL region is refused. `CastleMaker.Build` similarly retains 43.
- 271 remaining methods contain 330 calls to the observed, unrecognized
  `Class::IsAssignableFrom` target; together they retain 5,239 pad warnings. This is
  an overlapping subset of the table, not 5,239 individually proven catch clauses.
  No typed catch is recovered in r241; the recognized Object::IsInst path is covered
  by the executable synthetic catch regression. Runtime recognition belongs to
  the key-function lane.
- Zero negative LSDA action selectors and zero undecodable action chains were found
  in these 1,019 methods. Managed filters/faults are not identified by that count:
  **zero positively identified**, recovery unsupported, occurrence count unknown
  among the unclassified handlers. Negative C++ selectors must not be reported as
  managed exception filters.

`KeyFunctionRecovery.IsExceptionWrapperTypeInfo` only changes visibility so EH can
reuse its existing RTTI proof. No new runtime/class recognizer, calling-convention
rule, memory resolver or inlining rule is introduced.
