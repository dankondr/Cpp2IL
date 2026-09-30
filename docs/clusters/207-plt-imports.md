# Cluster: PLT imports and the stack protector

Task: dankondr/castle-recovery#207. Mechanism 4 of
`docs/P1_ROOT_CAUSES.md` in `dankondr/castle-recovery`: native calls through
the PLT were emitted as `Method not found @<address>`, and the compiler's
`__stack_chk_guard`/`__stack_chk_fail` stack protector survived into IL.

## Rule

`BlockMemoryImportRecovery` now names every call whose target is a PLT stub.
The stub's `b #addr` trampoline is decoded through the ELF's `.rela.plt`
relocations (`ResolveImportName`), which is lookup by relocation table only —
no address is hard-coded in recovery logic. Any resolvable call that does not
match a handled import still gets a `StringLiteral` target, so the emitted
diagnostic reads `Unknown call target operand: "<name>"` instead of an
address.

Named imports then dispatch:

- `memcpy`, `memmove`, `memset` — verified block copy/fill when destination,
  source and size operands are all proven; otherwise the call stays named and
  diagnosed.
- `modf`/`modff` — `System.Math.Truncate` (or `MathF`) call followed by
  `x - trunc(x)` subtraction and a store through the proven out-pointer.
- `sincos`/`sincosf` — `System.Math.Sin`/`Cos` (`MathF.Sin`/`Cos`) with stores
  through the two proven out-pointers.
- Unary math imports (`sin`, `cos`, `sqrt`, `log`, `exp`, `fabs`, `floor`,
  `ceil`, `trunc`, `atan`, `atan2`, `pow`, `fmod` where mappable) are
  rewritten at the ISIL lifting layer in
  `NewArmV8InstructionSet.EmitMathUnary`; the set now covers
  `cosh`, `sinh`, `tanh`, `log10` and `log2` (`System.Math` / `MathF`
  equivalents by float-ness). `logb` has no `System.Math` equivalent and
  stays a diagnosed named import.

`StackProtectorRecovery` runs after the import pass and excises the protector
only when all three elements are present: a canary check (`CheckEqual` /
`CheckNotEqual` where one side provably is the canary — the TLS cell
`[SYSREG + 0x28]`, a local or cell whose every def carries it — and both
sides are shapes it can take: a local, a `[base + 0x28]` read through any
base, or a cell proven to hold it), the `ConditionalJump` it feeds, and a
`__stack_chk_fail` call reachable from one of its successors through empty
connector blocks — nothing else ever calls it, so the reachable failure is
the structural co-proof when neither side is a direct TLS read. The fold
turns the branch into a `Jump` to the merge edge, nops the failure call
after all guards sharing a tail have been processed, and removes the
orphaned blocks. Two residuals fold on their own proofs: a compare already
collapsed to a constant (`CheckNotEqual x, x` / `CheckEqual x, x` — the
failure call is gone, the coalesced compare survived) folds to its live
edge, and the dead edge's failure call is collected and nopped the same way
when the shared tail stays reachable for real code. Anything else —
non-TLS bases, real-code successors, unproven frame slots, missing or
differing sides — is left diagnosed.

After the folds, `SweepDeadCanary` nops the machinery they left behind so it
emits no TLS-read or undefined-SYSREG diagnostics: pure defs
(`Move`/`Not`/compare) whose result no instruction reads, and stores to
cells proven to hold only protector values — a canary cell (every write
carries `[SYSREG + 0x28]`) or a thread-pointer cell (every write carries a
SYSREG-provenanced value) — once nothing reads the cell back. Stores to
cells carrying real data are never touched.

## Tests

`Cpp2IL.Core.Tests/Analysis/StackProtectorRecoveryTests.cs`:
`CanaryGuardFoldsToMergeAndExcisesFailBlock`,
`CanaryGuardWithLocalStoredCanaryFolds`, `SharedFailBlockFoldsEveryGuard`,
`StoredCanaryFrameSlotFolds`, `SpilledTlsPointerCompareFoldsAndSweepsMachinery`,
`UnprovenPointerCellStoreSurvivesTheSweep`, `UnprovenFrameSlotIsNotExcised`,
`AnImmediateFailTargetIsMatchedThroughTheResolver`,
`SelfCompareCanaryFoldsToFallThroughWithoutFailCall`,
`SelfCompareCanaryEqualFoldsToTakenEdge`, and the negative tests
`NonCanaryCompareIsNotExcised`, `MissingFailCallIsNotExcised`,
`DifferingCanarySidesWithoutFailCallStay`, `NonTlsCompareIsNotExcised`.

`Cpp2IL.Core.Tests/Analysis/BlockMemoryImportRecoveryTests.cs`:
`ModfRewritesToTruncateAndSubtract`, `SincosRewritesToSinAndCos`,
`ResolvedButUnhandledImportGetsNamedTarget`,
`UnresolvedCallTargetStaysUnnamed`, `AlreadyNamedImportStillRewrites`,
`UnprovenModfOutPointerStaysNamedCall` plus the pre-existing block-memory
cases.
