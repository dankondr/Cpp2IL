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
  between `ConstantBranchFolder` and `EqualityBranchInverter`).
- A null check on a `Newobj` result is constant (`== 0` → false, `!= 0` →
  true): fold the check and drop the edge it can never take, even when the
  branch target's throw provenance is undecidable
  (`InjectedCheckRemover.AllocatedNullCheckValue` + `DropImpossibleEdge`,
  before the `GetInjectedThrowType` gate).
- Anonymous types arrive from metadata already faithful (compiler name,
  `CompilerGenerated`, ctor parameters naming the properties, get-only
  properties over `<X>i__Field`); once the IL around their construction is
  canonical ILSpy emits `new { … }` and omits the declaration — fixing the
  instruction shapes is what removes the CS0246s, not a change to type
  emission.

## Tests

- `InjectedExceptionGuardTests.NullCheckOnFreshAllocationIsFolded` /
  `NullCheckWithoutAllocationIsNotFolded`
- `CoalesceStoreRecoveryTests.PairedMergesCollapseToSingleJoinHeadRead` /
  `NullCheckedBranchReadsTheFieldInline` /
  `NullCheckedGenericParameterBoxesBeforeTheBranch`
