# castle-recovery#218 — multi-dimensional array accesses

Cluster: `lane:memory`. `T[,]` element reads, writes and lengths in native
code, as il2cpp lays them out: the bounds block pointer at `[array + 2p]`,
one `{length, lower bound}` pair of `2p` bytes per dimension, then the elements
row-major at `array + 4p + (i·len1 + j)·size`.

## Rule (`ArrayRecovery.RecoverMultiDimensionalAccesses`, first in `ArrayRecovery.Run`)

- `[b + 2p·k]` with `b = [array + 2p]` is `array.GetLength(k)`; it becomes a
  call of `System.Array.GetLength`.
- `[array + (flat << log2 size) + 4p + o]` is an element when `flat` unfolds
  row-major into one index per dimension. A dimension whose length never
  multiplies in has index 0: the compiler folds `0·len` away.
- Every index that is not a constant must be compared with its own dimension's
  length somewhere in the method (the bounds check il2cpp emits before the
  access). Without that proof the address is left alone.
- A whole element is read with `T[,]::Get`, written with `T[,]::Set`; a field of
  a struct element is read or written through `T[,]::Address`. A struct element
  passed whole to a call whose parameter is the element type counts as whole.
  The accessors are runtime methods of the array type:
  `InjectedMethodAnalysisContext` on the `ArrayTypeAnalysisContext`, emitted as
  a `MemberReference` on the array type signature.
- The address arithmetic the elements no longer read is removed before the
  lengths become calls.

## Not covered

Walks along the last dimension with a post-indexed pointer or a byte offset
(`LDR W17, [X15], #4`; `grid + off`, `off += 16`) need induction recovery.
`CastleBuildingController::GetSumOfCastleValuesFromGrid` is one of them.

## Tests

`Cpp2IL.Core.Tests/Regression/MultiDimensionalArrayTests.cs`: read, write, a
struct element field, an index never compared with its length, and the emitted
IL (`int32[0..., 0...]::Get`, `System.Array::GetLength`).
