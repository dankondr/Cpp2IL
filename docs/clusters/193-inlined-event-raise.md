# #193 — inlined event raises respelled to the raiser

Cluster: `dataflow: duplicate-definition residual` — field-like event backing
fields that stay public because a foreign body inlines the raise
(`if (x.E != null) x.E()` on the backing field), colliding with the
same-named event as a CS0102 pair.

## Rule

The C# compiler compiles `x.E?.Invoke()` inside the declaring class as a call
to a private "raise" method or a guarded `Invoke` on the backing field; in
*other* types it inlines the guarded invoke on the field itself. When a
foreign body does that on a field-like event, Cpp2IL widens the field to
public for the access, and the widened field keeps the same name as the
event — CS0102.

`InlinedEventRaiseRecovery` (in `Cpp2IL.Core/Analysis`, run from
`IlGenerator` while branch operands are still blocks) respells a foreign
guarded raise back to a call on the declaring type's raiser, but only when
the binary itself proves it:

- The receiver chain of a `Call`/`CallVoid` on a delegate `Invoke` resolves
  through `Move` copies to a `FieldReference` that `HasEventTwin` — a private
  field whose declaring type is a reference type holding a same-named event.
- The call sits behind a single-source trampoline (`if (field != null)`), and
  the raise is reachable only through the guard's matching edge — the raise
  cannot fire when the field is null.
- `TryFindUniqueRaiser` finds *exactly one* accessible, signature-compatible
  method on the declaring type whose body loads and invokes the field. Zero
  or two candidates — or a private-scope declaring type — keeps the field
  access and its diagnostic; nothing is guessed.

When the respell happens, the null guard folds back into the call target
(`Jump` on the guard, `check` recomputed) and the foreign `FieldReference`
disappears, so the backing field folds back under the event private — no
duplicate definition. A fixpoint pass then prunes `Move` instructions whose
destination is never read again anywhere in the method (checked by a flat
operand scan, not reachability — a local still read or written anywhere else
keeps its store, so no read can lose a value), which clears the dead
`field`-load copies the respell strands. `Instruction.Sources` can throw on
malformed/synthetic ISIL (opcode-implied operand slots missing); reads go
through `SafeSources`, which falls back to the raw operands — an
over-approximation that can only refuse a rewrite, never make a wrong one.

## Measurement (castle-recovery r241, control `e1c8dd9`)

Game-owned refmode CS0102 `duplicate-definition` errors 27 → 2. The two
survivors are correctly refused: one has two signature-compatible raisers
(ambiguous), the other is a private event raised from its own constructor on
a non-game assembly. The widened fields fold private again; every foreign
raise body now calls the raiser the binary called.

## Test

`Cpp2IL.Core.Tests/Regression/InlinedEventRaiseRecoveryTests.cs` drives
synthetic ISIL through the real pipeline:

- `GuardedForeignRaiseRespellsToUniqueRaiser` — the emitted `Call` names the
  raiser and the guard block folds; fails on `development` (the field access
  and CS0102 stay).
- `AmbiguousRaisersKeepFieldAccess` — two candidate raisers ⇒ the field
  access and note stay.
- `UnguardedForeignRaiseKeepsFieldAccess` — no null guard ⇒ the field access
  and note stay.
