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
  `ceil`, `trunc`, `pow`-family excluded) are rewritten at the ISIL lifting
  layer in `NewArmV8InstructionSet.EmitMathUnary`; the set now covers
  `cosh`, `sinh`, `tanh`, `log10`, `log2` and `logb` (`System.Math.Log`/`Log`
  overloads / `MathF` equivalents by float-ness).

`StackProtectorRecovery` runs after the import pass and excises the protector
only when all three elements are present: a canary check (`CheckEqual` /
`CheckNotEqual` with the TLS cell `[SYSREG + 0x28]` on one side and a local or
`[base + 0x28]` on the other, the base's def chain ending at a `SYSREG` move),
the `ConditionalJump` it feeds, and a `__stack_chk_fail` call reachable from
one of its successors through empty connector blocks. The fold turns the
branch into a `Jump` to the merge edge, nops the failure call after all
guards sharing the tail have been processed, and removes the orphaned
blocks. A residual shape where the compare already collapsed to a constant
(`CheckNotEqual x, x` / `CheckEqual x, x`, i.e. the failure call is gone but
the coalesced compare survived) folds on the constant-proof alone. Anything
else — non-TLS bases, real-code successors, missing or differing sides — is
left diagnosed.

## Tests

`Cpp2IL.Core.Tests/Analysis/StackProtectorRecoveryTests.cs`:
`CanaryGuardFoldsToMergeAndExcisesFailBlock`,
`CanaryGuardWithLocalStoredCanaryFolds`, `SharedFailBlockFoldsEveryGuard`,
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
