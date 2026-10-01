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
- A container hop (`v.outer.inner`) emits `ldflda` on the root local, which
  verifies only when that local emits an address of the container's declaring
  struct; a leaf hop emits `ldfld`, which additionally rides a reference slot
  through `unbox` but never a primitive or mismatched-struct slot. The emitted
  type is provable early for `this`, parameters and locals defined only by
  non-void calls (`ProvenContainerReceiver`, the same derivation
  `CallDefinedLocalType` makes) or stamped and never written again (a local
  with no definitions); an arithmetic result or a register-reuse guess a
  later pass could restamp waits for the post-SSA pass where
  `EmittedLocalType` is settled, and a slot restamped to a primitive or a
  different struct keeps the register read diagnosed rather than emitting
  `ldfld` where the emitter must substitute a synthetic default. A local
  whose register was reused by a pointer-producing call is not a struct
  carrier: the whole method is skipped when operand and pointer slot locals
  overlap, and pointer-typed leaves are never projected.
- The projection itself is gated on the emission contract
  (`IlGenerator.FieldReferenceUsableFrom` with `requireToken: false` - the
  emitted definition does not exist yet at analysis time): a member the
  caller cannot name - a private corlib field like `System.Single.m_value`
  reached through a restamped primitive slot, or a compiler-generated
  backing field - would substitute a synthetic default at emission, so the
  pass declines and the register read keeps its own diagnostic. The two
  reads emission rewrites through an accessor - an enumerator's `_current`
  via `get_Current` and a list's `_size` via `get_Count` - stay projectable
  despite private accessibility (`EmissionRescuesFieldReference` mirrors
  the checks `TryEmitInlinedEnumeratorCurrent`/`TryEmitInlinedListCount`
  make).

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
partial-byte mask staying diagnosed, a top-half mask on a signed lane, a
low mask read into destinations of matching and wider width, an awaiter
chain whose root local's type is restamped after the early pass staying
diagnosed until the final pass projects it, a whole-read whose root
settles to `System.Single` staying the register operand in both passes
because the corlib member is unspellable
(`FieldReadOnRestampedPrimitiveSlotStaysDiagnosed`), and a pointer-typed
local keeping every read in its method diagnosed.
