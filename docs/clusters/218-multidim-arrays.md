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

## Walks along the last dimension (rank 2)

- A row walk: a pointer set to `data + len1·s` and stepped by the element size. `s` is the
  row index scaled by the element size, directly (`i << log2 size`) or as a counter that
  steps by the size alongside `i`. The element is `[i, column]`, `column` a counter the walk
  gets (0 where the pointer is set, +1 where it steps). `i` must be compared with length 0
  and must not change between the walk's start and the access.
- An offset walk: `[grid + off + 4p + k0·size]` with `off` stepping by the element size from
  0 alongside a counter `k` from `k0`. The element is `[0, k]`, and `k` must be compared
  with length 1.
- Two counters move together when both start in one block and either step in one block
  (the access is not between the steps), or no step runs before the first access, every
  cycle through the access runs each step, and no step repeats without the access.

Walks depend on loop-carried copies surviving the post-SSA simplifier (dankondr/Cpp2IL#176).

## Tests

`Cpp2IL.Core.Tests/Regression/MultiDimensionalArrayTests.cs`: read, write, a
struct element field, an index never compared with its length, the emitted
IL (`int32[0..., 0...]::Get`, `System.Array::GetLength`), a row walk, a row walk
whose row changes inside it (kept), and an offset walk.
