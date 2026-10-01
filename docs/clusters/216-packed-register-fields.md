# castle-recovery#216 — a struct carried in an integer register

Cluster: `lane:callconv`. The AArch64 ABI passes a value type of two to sixteen
bytes in the integer registers that carry it: `Nullable<T>` (a `bool` plus the
payload), `ValueTuple<A,B>`, `KeyValuePair<K,V>`, a list `Enumerator`
(`list*`, `index`, `version`), `Vector2Int` (`m_X`, `m_Y`). Native code masks,
shifts and extends those registers where IL reads fields.

## Rule (`Analysis/PackedRegisterFields.cs`)

- A local whose resolved type is a value type the ABI never hands a V register,
  produced by a call result or parameter or by one register-wide store, holds
  that struct. A `Move`/`ShiftRight`/`And` on it that selects exactly the bits
  one field occupies is a read of that field; the whole register is the whole
  struct. Lifting records the extension's width and signedness
  (`Instruction.NativeReadWidthBits`, `NativeReadSignExtend`) so the pass can
  tell `hasValue` (`UXTB`) from a 32-bit lane (`LSR #32`, `ASR #32`, `UBFX`,
  `SBFX`). A mask names a field only for a contiguous bit run over all the
  leaf's bits: `0xFF` at offset 0 is `hasValue`, `0xFFFFFFFF` is `m_X`. A mask
  whose set bits all sit inside the offset-zero leaf keeps the `And` but reads
  the field instead of the pack (`pack & 0x80000000` is `m_X & 0x80000000`),
  while a discontiguous mask, bits in any other field, or a run crossing a
  field boundary stays diagnosed.
- An offset-zero `And` reads the leaf verbatim when the destination stores no
  more than the leaf's width (an untyped local takes the leaf's own type); a
  wider destination sees the zero extension, so there the leaf must be
  unsigned. A shifted-out leaf (`ShiftRight`, sign bits cleared) is integral
  when the shift drops sign bits out of a 64-bit lane, unsigned otherwise.
- The same layout lookup turns `packed OP constant` comparisons into field
  comparisons (`hasValue != 0`, `m_Y < n`) and spills (`STR X,[SP]` +
  `ADD X,SP`) into the addressed stack local's struct type, so a `&T` read
  lands the struct member.
- The pass runs inside the type-resolution fixpoint (register spill typing
  unlocks field reads) and once more out of SSA (late passes surface new
  selections; `TypeAddressedLocals` gives stack locals their type late).

## Emission boundaries (other lanes)

- A writable managed address of a boxed struct (`stfld`, `initobj`, a
  mutating call receiver, `ldflda`) needs either proof the boxing is a copy
  or the readonly `&T` `unbox` yields plus a diagnostic: routing the receiver
  through `unbox.any` + a scratch local would verify the IL but drop the
  store, so those receivers keep their diagnostic until `lane:memory` (#211)
  models boxed-value addressability honestly.
- A local declared `T*` stays a pointer through analysis and emission;
  mapping it to `native int` in the locals signature is `lane:types-ssa`
  (#249).

## Tests

`Cpp2IL.Core.Tests/Regression/PackedRegisterFieldTests.cs`: `Nullable<int>`
`hasValue` mask and `value` shift, `Nullable<bool>` bound check, a two-`int`
tuple's high lane, `Vector2Int.y` (`ASR #32`) indexing `T[,]` through `Get`, a
partial-byte mask staying diagnosed, a top-half mask on a signed lane, and a
low mask read into destinations of matching and wider width.
