# #267 — inlined accessible forwarders respelled at leaf call sites

Cluster: `recovered code names a callee that source never wrote` — a call
edge lands on an `internal`/`private` member `N` of another assembly because
clang inlined the accessible forwarder `M` the source actually spelled
(`lane:inlining`). Reported family: 186× CS0122 in
`CastleClashers.Rules/CastleClashers.Protobuf/*.cs`, mapped to public
members by castle-recovery `docs/clusters/260-protobuf-cs0122.md`.

## Rule

When a call edge targets member `N`, check every type an argument's
projection is rooted at for a source-visible member `M` whose own body is
one call to `N` fed by projections of `this` and its parameters — plus at
most a pure transform on the result. A proven unique `M` is the spelling
the source wrote, so emit `recv.M(args…)`:

- `M` returning the leaf's raw value (identity forwarder) fits whatever the
  caller does with the result — the caller's own post-op is its loop's
  business (`tag = input.ReadTag(); tag != 0`).
- `M` applying a transform (`!= 0` → `ReadBool`, `DecodeZigZag32` →
  `ReadSInt32`) fits only when the caller computes exactly that transform,
  which the rewrite absorbs into the call.
- `M` void fits only where no result is read.
- No proven unique forwarder: the call keeps `N`'s name and stays
  diagnosed — never guessed.

Callee accessibility is not a gate: a visible leaf reached through a
forwarder is still the inlined spelling (`ParsingPrimitivesMessages` is
public in the game's il2cpp metadata — bundled protobuf predates 3.34.1's
internalization — and its sites were the same defect). The member `M`
itself must pass a source-scope visibility check: same or same-named
assembly, no emitted InternalsVisibleTo.

The leaf's argument temporaries (`ref state = ref input.state`,
`v = input + 16`) exist only to feed it; after the rewrite a temp whose
remaining uses were all the call dies with it, recursively — otherwise its
projection read surfaces as a stray CS0122 on the same internal field.

Forwarder bodies are proven structurally (`ForwarderShape`: strict single-
leaf-call scan over the member's own CFG — every instruction must be the
leaf call, an argument projection or result-transform temp, a
`Nop`/`Jump`/`ShiftStack`, or the one `Return`), never by name; detected on
every member type, not just the receiver's. Facts ride `MemberBodyFacts`
and are cached per candidate; `EnsureBody` lifts a candidate body under
its monitor exactly as the #181 passes do (a body inside `AnalyzeCore`
never runs this pass, so the wait cannot cycle — re-entry safe).

## Regression test

`Cpp2IL.Core.Tests/Analysis/InlinedMemberRecoveryTests.cs` — synthetic
bodies:

- `InaccessibleLeafCallCallsForwarder` — `ParsingPrimitives.ParseTag`
  shape: leaf call with `ref` field projections, accessible `ReadTag`
  forwarder; emits `input.ReadTag()`, caller's `!= 0` survives.
- `InaccessibleLeafCallCallsForwarderThroughRefThis` — `ref this`
  receiver plus a parameter (`ReadMessage` shape), `CallVoid`.
- `InaccessibleLeafCallAbsorbsSharedPostOp` — caller's `!= 0` equals the
  member's own transform; emits `input.ReadBool()` and collapses the op.
- `InaccessibleLeafCallStaysWhenMemberDoesMore` — negative: `M` does more
  than forward (second call); the leaf's name is kept.

The two positives and the `ref this` shape fail on `development`
(78ce02b6) — the leaf is emitted — and pass on this branch.

## Numbers — Castle Busters r241 whole-game sweep

`CastleClashers.Rules` decompiled (ilspycmd `-p`) and compiled nostdlib
against the stock nupkg `Google.Protobuf` 3.34.1 (sha256
`b05f9f01…65b`) + net10 reference pack:

| error code | control (78ce02b6) | branch |
|---|---|---|
| CS0122 `ParsingPrimitives` | 30 | 0 |
| CS0122 `ParserInternalState` | 30 | 0 |
| CS0122 `ParseContext.state` | 30 | 0 |
| CS0122 `ParseContext.buffer` | 30 | 0 |
| CS0122 `ParsingPrimitivesMessages` | 4 | 0 |
| **total** | **124** | **0** |

No other diagnostic code. The isolated decompile covers 7
`CastleClashers.Protobuf` files; the #247 rebuild project's tree reports
186 (more generated files, same per-site family) — the members are the
same set the 260 doc mapped, and every survivor is classified: none
survive.

### The three doc sites, emitted call before → after

`CCTrainerState::InternalMergeFrom` and `CCInventoryState::InternalMergeFrom`:

```csharp
ref ParserInternalState state = ref input.state;          // before
switch (ParsingPrimitives.ParseTag(ref input.buffer, ref state)) { … }

switch (input.ReadTag()) { … }                            // after
```

case bodies likewise: `ref ParserInternalState state3 = ref input.state;
uint n = ParsingPrimitives.ParseRawVarint32(ref input.buffer, ref state3);`
→ `uint n = input.ReadUInt32();`

`CCInventoryAsyncEvent::InternalMergeFrom` case 26u:

```csharp
ParsingPrimitivesMessages.ReadMessage(ref input, cCMatchCompletedPayload);  // before
input.ReadMessage(cCMatchCompletedPayload);                                  // after
```

## Scope check

`diag_families.py --assemblies CastleClashers.Game` control vs branch and
the ILVerify comparison: see the gate report in the PR's Verification —
no valid→invalid transition in any game-owned assembly, and the
castle-building scope does not regress.
