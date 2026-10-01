# #254 — scalar ARM64 numeric conversions lift as Convert, not Move

Cluster: `dataflow: literal cannot fill a System.Double slot` — IL2CPP's
saturating `(int)x` / `Mathf.RoundToInt` sequence (`fcvtzs` + `csel`) merged
an integer local with the double it was converted from, so the saturation
literal could not fill the slot's type.

## Rule

The ARM64 lifter used to lift every scalar numeric conversion — `FCVT`,
`FCVTZS/FCVTZU`, `FCVTMS/FCVTMU`, `FCVTPS/FCVTPU`, `FCVTNS/FCVTNU`,
`FCVTAS/FCVTAU`, `SCVTF`, `UCVTF` — as a plain `OpCode.Move`, "conversions are
moves for analysis purposes". Copy forwarding then replaced the destination
with the source, and type inference gave the destination the source's type:

```
fcvtzs w8, d0
fmov   d1, x27          ; +inf bits
fcmp   d0, d1
csel   w19, w28, w8, eq ; w28 = 0x80000000
```

After forwarding `W8` is `D0`, so the `csel` merge `X19` unions
`{int.MinValue, v_double}` and is typed `Double`; the literal `-2147483648`
cannot fill a `System.Double` slot. The right result is an `int` local:
`x19 = (int)Math.Round(pos.x)`.

A new ISIL opcode `Convert` makes the conversion distinct from a copy, which
nothing `Move`-shaped (copy forwarding, type propagation, coalescing,
constant folding) touches without an explicit audit:

- The lifter emits `Convert dest, source` with three marks recording what
  register normalization erases: `ConversionFromFloat` (fcvt* reads float,
  scvtf/ucvtf reads int), `ConversionUnsigned` (fcvtzu/ucvtf family), and
  `ConversionSourceWidthBits` (the source register's width). The destination
  register's width is carried as `NativeIntegerWidthBits`/`NativeFloatWidthBits`,
  the same marks ADR/loads already seed with, so the local is typed by its own
  slot — `fcvtzs w8` gives `Int32`, `scvtf d0` gives `Double`.
- Rounding-mode conversions pre-round through the managed math helper
  (`FCVTMS`→`Math.Floor`, `FCVTPS`→`Ceiling`, `FCVTNS`→`Round`,
  `FCVTAS`→`Round(x, MidpointRounding.AwayFromZero)`) into a temporary the
  truncating `Convert` then reads; `FCVTZS`/`SCVTF`/`UCVTF`/`FCVT` truncate
  directly.
- `IlGenerator` emits the honest CIL conversion for the pair: float→int is
  `conv.i4/conv.u4/conv.i8/conv.u8`, int→float is `conv.r4/conv.r8`
  (`conv.r.un` for unsigned). A literal source converts as the number — an
  `scvtf` of `7` is `7.0f`, never its bit pattern; a float literal read as
  an integer keeps its bit pattern via `Int32BitsToSingle`/`Int64BitsToDouble`
  in reverse. A live operand source loads at its emitted type and reinterprets
  through `BitConverter` when its managed domain differs from the register
  the instruction reads.
- `FMOV` between GPR and FP registers is a bit move and is unchanged.
- The fixed-point forms keep their scale: `SCVTF`/`UCVTF <F>d,<W>n,#f` scale
  the converted integer by `2^-f` after the `Convert`, `FCVTZS`/`FCVTZU`
  `<W>d,<F>n,#f` scale the source by `2^f` before it — exact power-of-two
  `Multiply`s. Anything else unrecognized — a discarded result to `xzr` or a
  non-register form — stays a Nop or an explicit `NotImplemented` diagnostic.

Because `Convert` is a new opcode, every opcode-category enumeration that
treats it as a plain local write was audited and extended only where the
conversion is harmless: destination/source tracking, dead-code elimination,
`DefinedLocalRegisters`, `MayWriteMemory`, `BreaksConsumers`, interface-
dispatch scaffolding and the receiver-mutation safe list. Lists that see
*through* copies (phi-edge merging, boolean/pointer/`&`-proof look-throughs,
the union-find operand family) correctly do not include it — a converted
value is not its source.

## Measurement (castle-recovery r241, control `73496b28`)

Game-owned methods carrying `Literal operand cannot fill a System.Double
slot`: **155 → 47** (sole carrier: **58 → 14**), 128 → 34 of them in
`CastleClashers.Game`. Game-owned methods with any diagnostic: **3,966 →
3,919**; `incomplete` on the game-owned table: **3,967 → 3,920**. ILVerify
transitions on the sweep DLLs: **0 `valid → invalid`** (170,144 stay valid,
416 stay invalid).

Scope types (`CastleBuildingController`, `TimedCastleBuildingController`,
`CastleMaker`, `EngineersController` + nested): methods with diagnostics
**88 → 81**; 15 of the 18 named carriers lose the diagnostic, 6 of the 9
sole carriers now carry no diagnostic at all (`CheckIfHasFoundationAbove`,
`GetBottomPartAverageUpgradeLevel`, `GetImpactedObjects`, `AddFoundation`,
`RemoveFoundation`, `CheckIfBelongsToAnyFoundation`, plus
`WhereCanUpgrade`). The 3 that still carry it have different root causes:
`EngineersController::IsInRange` and `CheckIfTargetPositionIsTooClose`
compare an `fsqrt s` result — bridged `Math.Sqrt` whose managed signature
returns `Double` — against a 4-byte `fmov s,#imm` literal;
`CastleMaker+<>c__DisplayClass123_0::<DetectStep>b__0` reuses the `V0` bank
as both `fcvt d0` (Double) and `fmov s0,#±0.5`/`frintp s0` (Single), so the
local resolves Double and the 4-byte literal writes cannot fill it. Both
are the float-literal/slot-width class in `lane:types-ssa`, not conversion
defects.

Grown families (all unmasked, never new root causes): `type: no legal
conversion` 1,605 → 1,609 methods — the merge no longer lies about operand
types, so precise mismatches surface (`System.Object`/`Single` operands vs
`Double`/`Vector2`/`Vector2Int`/`Enumerator` slots; largest cluster
`UnitPanel::CalculateStats` +10); `type: synthetic default` 690 → 693 and
`canonical shared-generic` 173 → 174 are the same surfacing;
`dataflow: undefined local` in `CastleClashers.Game` 638 → 640 (`V9`/`stack`
reads downstream of the same unmasking); `lift: unimplemented` **641 → 629**
— the fixed-point `scvtf`/`fcvtzs` forms it now lifts close more than the
new unmasked adds open.

## Tests

`Cpp2IL.Core.Tests/Isil/Arm64ConversionOpcodeShapeTests.cs` pins the lifting
contract — direction, sign, source width, destination width marks on the
`Convert` — and `Cpp2IL.Core.Tests/Isil/Arm64NumericConversionTests.cs` drives
the emitted IL through the real analysis spine and JIT-invokes it:

- `FcvtzsCselSaturationFillsAnIntSlot` /
  `FcvtzsCselSaturationExecutesTruncatingSemantics` — the saturating
  `fcvtzs`/`csel` sequence produces an `int` local, the `int.MinValue`
  literal fills it, and the JIT-executed method returns `3` for `(3.7, 0.0)`
  and `int.MinValue` for `(1.5, 1.5)`. Fails on control with the exact
  production diagnostic `Literal operand cannot fill a System.Double slot`.
- `ScvtfOfIntegerConstantEmitsTheNumber` — `mov w1, #7; scvtf s0, w1` emits
  `ldc.i4 7; conv.r4`. Fails on control (no `conv.r4`, no `7` constant).
- `FmovBetweenBanksStaysBitMove` — `fmov d1,x8`, `fmov x8,d0`, `fmov w0,s0`
  keep lifting as `Move`; a regression guard that passes on control too.
