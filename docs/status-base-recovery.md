# Recover object-field aliases, ARM64 barriers and virtual tail calls

This follows the integer recovery patch; while its PR is open this is a stacked
fork-only change. No game-specific addresses or names enter production code.

## Root causes and conservative boundaries

* ARM64 did not identify the generated GC write barrier. Anchor its **barrier-only**
  core through the exported `il2cpp_gc_wbarrier_set_field`: exact X0/X1 shuffle,
  branch to exact `STR X1,[X0]; B core`. Recognize only pure B aliases of that core.
  The exported setter and store-wrapper entry are deliberately not removed.
* Pre-indexed reference stores leave an SSA object+constant address. Memory uses
  relative to that address now fold back to the root only for a unique definition,
  unknown alias type, known reference-type root and exact known inherited/own
  field offset. Indexed, typed, ambiguous and unnamed/interior cases remain alone.
* Known vtable calls previously ignored indirect tail jumps. Recover the call and
  return without using the stale physical return register; require compatible
  return signature, real block terminator and nonstatic target. Preserve virtual
  dispatch explicitly through IL emission. Direct calls to virtual/base methods
  remain direct. Existing vtable-layout support assumptions are unchanged; this
  is not a new universal IL2CPP layout detector.

No failed method is replaced with a stub/default return. Native GC bookkeeping is
represented by the managed field store and CLR GC, as in existing x86 recovery.

## Exact evidence and results

Castle Busters1.11.1, Android AAPCS64, Unity6000.0.72f1, metadata31.1.
`LoadingUI.SetStatusBase(string)` native VA0x3c80dbc, raw0x3c7cdbc,176 bytes,
SHA256 `f356bb3a7deb0e7545192b7258f598a3508d955dbc910a225ce2cf8d8b40f303`.
Fields: statusTxt+0x30, _baseStatus+0x50. Metadata maps TMP slot66
((0x558-0x138)/16), paired MethodInfo at0x560, to virtual TMP_Text.set_text(string).
The null throw helper is anchored to actual System/NullReferenceException strings.

Generated barrier0x37c2a24 ->0x37c3f8c ->0x38694e0 shares the core with the exported
store-wrapper. Independent ELF decoding checked all1100 aliases are pure branch
chains and neither setter entry is included. Twelve actual native thunk/core/
atomic-helper executions confirm dirty-bit updates with GC flag0/1 and untouched
reference slot (single-threaded non-LSE path only).

SetStatusBase: diagnostics5->0, ILVerify-invalid->valid, MaxStack2. Fifteen actual
A64-versus-emitted-CIL cases cover null/empty/string text and null-false,
destroyed-false, live-true, cleared-after-check and replacement-after-check target
contracts. Native field store, order, target reload and exception branch agree.
The adapter preserves candidate opcodes/branches/callvirt, rebinding only exact
fields/call boundaries and receiver representation. Cold init, original Unity/TMP
implementations, concurrent GC and global equivalence are not claimed.

The audited17,026-method game subset changes:

| Metric | Before | After |
|---|---:|---:|
| ILVerify valid |6814|7703|
| ILVerify invalid |9958|9069|
| Structural failures |217|75|
| Methods with diagnostics |7844|5562|
| Diagnostic strings |63345|53643|

No valid->invalid regressions. Three already-invalid methods gain warnings:
ProfileInfoController.GetUncollectedEmotes1->3; ReferralManager async MoveNext39->40;
TournamentPanel.Close5->6. Controlled barrier-on/off SSA confirms the cause:
previously GC calls were falsely named List<ObscuredString>.Contains/SaveController.Load,
poisoning inferred types; removing those false calls reveals unresolved accesses.
Tournament's previously inlined unresolved delegate operands become explicit
loads. These methods remain unverified, not promoted. A broader alias-folding
trial was rejected and retained locally; only exact named fields are shipped.

Tests: two genuine pre-fix regressions fail; final114/114 Core,5/5 LibCpp2IL;
all four Core frameworks build. Void virtual tailcall fixture includes string
argument preservation and empty return; nonvoid fixture rejects stale result use.
Direct class calls stay direct, flagged vtable calls/interface calls use callvirt.

Local immutable report: Castle Busters history dataset,
`recovery/1.11.1/status-base-recovery-20260921`. Shared warm cache27hits/0misses.
Startup reachable30: two bounded case-verifications (Awake re-run24/24 and
SetStatusBase15/15),28 blocked,45 unresolved targets. The new target is the actual
TMP setter edge. Transplant plan32selected/58blocking reasons, no DLL writes.
Next smallest invalid method: LoadingUI.StartDots, IL002b stores I4 into an object
temporary; tween/delegate behavior remains unverified. No Unity/asset mutations
or recovered-boot claim.
