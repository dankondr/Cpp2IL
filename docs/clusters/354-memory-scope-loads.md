# 354 — scope loads: merged copies, folded element addresses, class-local newarr

Cluster: `lane:memory` — the field, array and metadata loads the castle-building
scope still reported as `Unmanaged memory load` after #340 (`a39c172d`), whose
store side is done. The shapes below are what remained on the load side:
merges and folds that hide a provably managed value behind a second layer of
copies.

## The shapes

1. **Merged copies of the same array** (`v = this.grid` reloaded on each edge
   of a merge). The multidim machinery keyed everything on a *single*
   definition — `bounds` locals required one `Move block, [array + 0x10]`
   seed — so a jit reload of the bounds block or the array field on both arms
   of a merge stranded every `GetLength`, bounds check and element access
   that flowed through it. `Root` now also unwinds a `MergedCopy`: a local
   whose every definition `Move`s from a `LocalVariable`/`FieldReference` and
   whose sources pairwise agree under `SameValue` names the shared root —
   `this.grid` reads on both paths canonicalize to one `FieldReference`.
   `BoundsArray` resolves every definition of a bounds block the same way
   (a `[base + bounds]` seed on any def, or a copy of another block) and
   requires all defs to agree on one array; `Length` gained the same
   multi-definition arm for merged `[block + dim·2p]` reloads. Emitted
   operands keep the *local* spelling of the array (`v`, not the
   `FieldReference` `Root` canonicalizes to): the check prover values a
   field read at the position of its load, so a copy local compares equal
   wherever it is used — writing `this.grid` into `GetLength`/element
   calls stranded the two length terms of one check on different write
   epochs and the bounds-check fold never fired (the `TileWrite2d`
   corpus regression).

2. **Element addresses folded into one register** (`p = arr + i·stride +
   header; …; [p]` / `[p + k]`). `GuardedIndexAccess` needed a
   `[base + index*scale]` operand; `DerivedElementAccess` needed the
   element-region offset in the addend. When the jit materializes the whole
   address once (dereferenced more than once), neither survives to match.
   `FoldedElementAccess` flattens the base local's address arithmetic
   (`Move`/`SignExtend32` copies, `Add`/`Subtract` terms, `Multiply`/`ShiftLeft`
   immediates) into leaf terms plus a folded constant: exactly one leaf must
   resolve to the array (same `ResolveArray` rule as the subscripted form),
   the rest fold into one index affine — mixed roots refuse — and the result
   feeds the same `GuardedIndexAccessResolved` path (guard proof, type-fit,
   emission) as the subscripted form. `ProveIndexGuard`'s index comparison
   was `ReferenceEquals` on roots; it now uses `SameOperandValue`, and
   `ValueRoot` unwinds `SignExtend32` like `Move` — a sign extension carries
   the same integer value, so the compare may run on a copy of the extended
   register while the address arithmetic reads the unextended one.

3. **`SzArrayNew` with the type in a class register** (shared-generic
   `new T[n]`). The type slot of the allocation call was required to be a
   literal `Type: T[]` constant; shared-generic sites keep
   `Il2CppClass<T[]>` in a register and only `Move` it there, sometimes along
   more than one definition edge. `NewArrayTypeOperand` resolves the operand
   to the array type: a `Type:` constant, a `RuntimeClass`-typed local whose
   represented type is `T[]`, or `Move` copies of either — every definition
   must agree on one array type, so a merge of two different classes never
   invents an element type. The allocation still stays a `Call` when nothing
   proves the type.

4. **Statics dereference on an unproven class constant** (`[klass + static_fields]`
   where the klass is a copy or phi created after the seeding fixpoint
   settled — an edge copy of a `Type:` move, a split phi input). #340's
   stand-in fold required `UnseededConstant`: a leaf `Move _, Type` or a
   phi already claimed by a non-`RuntimeClass` type. A class constant that
   simply stayed untyped fell between the two — and folding the operand to
   the stand-in there produced a value read of a storage block nothing
   spells (`Undefined local staticsNNN`). `ClassConstant` already proves
   the class; an untyped base cannot outrun the type the proof gives it,
   so `klass.Type == null` now *claims* `RuntimeClassTypeAnalysisContext`
   for the proven type — putting `Move x, [klass + static_fields]` on the
   classic schedule (the destination is typed `Il2CppStaticFields<T>` by
   `PropagateStaticFieldStorage` and the move is dropped at emission).

## The tests

`Cpp2IL.Core.Tests/Regression/MergedScopeLoadTests.cs` — one test per shape:

- `MergedBoundsReloadsStillNameTheirLengths` — two `Move block, [g + 0x10]`
  definitions through separate field-read copies of one `this.grid`: both
  dimension lengths come out as `GetLength` calls on the field.
- `FoldedElementAddressReadsAsAnIndex` — `[p]` where `p` is
  `arr + (sext idx << 2) + 0x20` under a `CheckLess` on a copy of the
  extended index: `arr[idx]`.
- `SharedGenericNewarrReadsItsTypeFromTheClassLocal` — `SzArrayNew` whose
  type operand is a `Move` copy of an `Il2CppClass<T[]>` constant: `NewArr`
  with the array type.
- `UnprovenClassConstantStaticsBaseClaimsRuntimeClass` — `[copy + 0xB8]`
  where `copy = Move` of a `Type:` constant leaf and stayed untyped: the
  copy claims `RuntimeClass`, the destination claims `Il2CppStaticFields`.

Each fails on `a39c172d` and passes on this branch.

## Still diagnosed (out-of-lane or unproven)

- Index guards the compare cannot prove (the length compared comes from a
  different read than the access's array) keep `Unmanaged memory load` —
  an unproven `arr[i]` is never guessed.
- The `SpawnShields` X8 value/address live-range split leaves late-formed
  operands no matcher sees — `lane:types-ssa`, tracked by #327.
- `T[,]` element reads through `ObscuredInt[,]`/`Int32[2]` shapes the
  element/field partition does not cover stay diagnosed.
- Object-field loads whose receiver local is untyped (the type would come
  from `lane:types-ssa` inference) stay diagnosed.
