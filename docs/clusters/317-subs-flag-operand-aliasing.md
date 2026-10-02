# 317 — flag-setting subtract reads its operands after writing the result

Cluster: recovery, ROADMAP direction C («Как восстанавливаем код»), level L3.
Catalog: no entry yet — the shape is the flag-producer half of `llvm-select`
/`llvm-ccmp` (see Gaps in the PR).

## The rule

`subs wD, wS, #k` (and `negs`, register-form `subs wD, wS, wT`) writes flags
*and* a result. In the lifter (`NewArmV8InstructionSet`) the flag temps were
emitted after the `Subtract dest, src1, src2` instruction. When the
destination aliases a compare operand (`subs w8, w8, #1`, `subs w19, w26,
w19`, `negs w8, w8`), SSA rebinding made the flag subtraction
`TEMP1 = src1 - src2` read the post-definition version of `src1` — the
result itself — so every flag was computed one `k` too low. A following
`b.mi`/`b.lt`/`b.gt` (and `b.eq`/`b.ne` countdowns, `cset`/`csel` consumers)
recovered `(wS - k) <cond> k` instead of `wS <cond> k`.

The flag math is evaluated before the result write, so the flag temps bind
the same SSA versions the result subtraction reads. `adds`/`tst`/`ands` are
unaffected: their flags are defined on the result (`EmitResultFlags`), and
`cmp`/`cmn`/`ccmp` write no register.

## The test

`Cpp2IL.Core.Tests/Regression/SubsFlagOperandAliasingTests.cs`: lifts raw
ARM64 words through the real pipeline (disasm → CFG → dominators → SSA →
`LocalVariables` → `FlagConditionRecovery`) and asserts two invariants: the
flag subtraction reads the identical operand locals as the result
subtraction, and the recovered branch condition compares the
pre-subtraction operand (`CheckLess(w8, 1)`, not `CheckLess(w8 - 1, 1)`).
Covers `b.mi/pl/lt/ge/gt/le` on `subs w8, w8, #1`, non-unit and 64-bit
immediates, a subtrahend-aliased `subs w8, w0, w8`, `negs`, and `b.vs`
overflow-flag inputs. Fails on `development` for every aliased case; the
non-aliased `subs w8, w0, #k` and `cmp` controls pass on both.

## Milestone

Castle-scope sites in `CastleMaker`: `Build` (`subs w8, w8, #1; b.lt` at
`0x3e5d930` — one `ldloc` operand differs, `(w8-1) < 1` → `w8 < 1`),
`CanPlaceRoof` (`subs w22, w22, #1; b.mi` at `0x3e6c0cc`), `InitRefs`
(`subs w19, w26, w19; b.le` at `0x3e54428`, `subs w23, w23, #1; b.gt` at
`0x3e54efc`). The named milestone methods `GetCastleChunks` and
`CheckAndFixCastle` carry no in-place `subs` and were already recovered
correctly — identical IL on both builds.
