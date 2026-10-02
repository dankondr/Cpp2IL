# 284 — switch lowered to a constant lookup table

Cluster: recovery, ROADMAP direction C («Как восстанавливаем код»), level L3.
Catalog: `docs/forward/catalog/llvm-switch-lookup-table.md` (lane
`control`).

## The rule

LLVM `SwitchToLookupTable` lowers an all-constant `switch` into an unsigned
bounds check followed by a data read — no case branches survive:

```
cmp wN, #<count>; b.<out-of-range> #default
adrp xT, #<page>; add xT, xT, #<off>      ; static table address
ldr wR, [xT, wN, uxtw #k]                  ; element size 2^k
b #merge                                   ; or ret
```

Cpp2IL lifted the indexed read as an unmanaged `*addr` load, so the method
kept an `Unmanaged memory load` diagnostic instead of a `switch`. The fix is
a new pass (`SwitchLookupTableRecovery`) that recognizes the shape — a
memory load indexed by an integer selector, `scale == access size`, guarded
by a raw-flag bounds check — reads the table constants at the static
address, and replaces the load with an ISIL `Switch` dispatching to blocks
that assign the table constants, which IlGenerator emits as a CIL `switch`.

Two spellings of the read survive lifting, both matched: `Move result, [tbl]`
followed by `Jump`/`Return` (the element feeds a local), and `Return [tbl]`
(the method returns the element in place — the corpus `switch-enum` shape);
the latter gets a synthesized result local so both emit the same case blocks.
The selector is recognized through an enum's `value__` field read as well as
the bare local — same bits, different spelling. The emitted switch input is
forced to `conv.u4` unless the operand already emits as `System.Int32`/`UInt32`,
so enum selectors verify cleanly.

## The rules it must not break

- **Constants only at proven addresses.** The table bytes are read from the
  image only inside a static, never-patched range (ELF read-only segment —
  the #273 constant-pool precedent). A table whose bytes cannot be proven
  keeps its diagnostic; nothing is synthesized.
- **Only raw flag shapes.** The guard must be the unsigned-compare flag
  pattern the lifter emits: `CheckLess` (carry flag — `b.lo`), `CheckEqual`
  on the post-subtraction result (zero flag — `b.ls` after `subs/cmp`), or
  their `And`/`Or` composite for a double-sided bound, with `Not` parity
  counted to find which edge means in-range. A bare `CheckLess` is
  signed-ambiguous and is not matched.
- **The guard is the only way in.** The load block's only non-trampoline
  predecessor is the guard block, and the guard's other edge is the single
  reachable default block. A table read reachable without the bounds check
  stays diagnosed — its constants are unproven for that path.

## The test

`Cpp2IL.Core.Tests/Analysis/SwitchLookupTableRecoveryTests.cs`: builds the
guarded load graph by hand (5-element u32 table, out-of-range default)
across three shapes — the merge form (`Move` + `Jump`), the local-return
form (`Move` + `Return`), and the corpus-exact direct-return form
(`Return [tbl]`, composite `And` bound, selector read through `value__`) —
asserts a `switch` with the table's constants and no `Unmanaged memory
load`, and asserts an unproven table keeps its diagnostic. Fails on
`development` without the pass.

## Milestone

`CastleMaker::GetWallType(System.Int32, System.Int32)` — the enum→value
table read at `0x3e6073c` — and the `corpus/switch-enum` round-trip, whose
il2cpp conversion previously aborted on the invalid IL this shape produced.
