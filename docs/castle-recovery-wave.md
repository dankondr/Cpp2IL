# Castle Busters semantic-recovery wave

## Shared contract

- Base every branch on `codex/castle-recovery-r241`.
- Open the PR against `codex/castle-recovery-r241`, not `development`.
- Fix a general ARM64/IL2CPP pattern. Assembly names, metadata tokens, native
  addresses, and method names must not appear in production recovery logic.
- Add the smallest raw-instruction or ISIL regression test that fails before the
  fix and proves the recovered behavior after it.
- Do not make a failing method "pass" by stubbing it, suppressing diagnostics,
  weakening verification, or replacing a value with `default`.
- Keep to the files owned by the task. If the real fix requires another task's
  files, report the required seam instead of implementing both sides.
- Run the targeted test fixture and build `Cpp2IL/Cpp2IL.csproj` for `net10.0`.

The r241 Castle corpus has 69,982 emitted method bodies, but "emitted" is not
equivalent to semantically correct. The build-time oracle observed 124
`ArgumentNullException`, 69 `InvalidCastException`, one `InvalidProgramException`,
and repeated explicit decompiler-issue throws. The full recovery manifests contain
142,728 unmanaged-load, 7,979 unrecoverable-operation, 7,800 indirect-call,
3,540 unimplemented-instruction, and 2,878 unrecoverable-integer diagnostics.

The game assemblies themselves are not clean: `CastleClashers.Game` has 3,074
methods with diagnostics (28,677 diagnostics total), and the residual
`Assembly-CSharp` has 1,641 methods with diagnostics (15,659 total). Vendor source
matching is therefore an oracle and a cost optimization, not a substitute for the
decompiler.

## Task 1 — Disarm decoder completeness

Own only `vendor/Disarm/**` and the Disarm submodule pointer. Find ARM64 words that
Disarm currently returns as `UNIMPLEMENTED`/undefined even though LLVM decodes them.
Add table-driven raw-word tests and implement the missing decoder cases, prioritizing
Advanced SIMD scalar/lane operations used in integer hash loops. Do not touch Cpp2IL
mapping. Deliver a Disarm commit plus the parent pointer update.

Acceptance: every added word decodes to the same mnemonic, widths, arrangement,
registers, shift/extend, and immediates as LLVM; existing Disarm tests pass.

## Task 2 — shifted logical instructions

Own `Cpp2IL.Core/InstructionSets/NewArmV8InstructionSet.cs` and a new focused test
file under `Cpp2IL.Core.Tests/Isil/`. Implement `AND/ORR/EOR/EON/BIC/ORN` register
forms with `LSL/LSR/ASR/ROR` shifts for both W and X widths. Model the shifted
operand explicitly so later type recovery sees the real operation.

Concrete failing family: ACTk integer hashes currently report `EOR shift LSR is
not supported`. Preserve 32-bit wraparound for W registers and 64-bit wraparound
for X registers.

Acceptance: raw instruction tests cover zero shift, non-zero shift, W/X widths,
and at least EOR+LSR and ORR+LSL; no `NotImplemented` ISIL remains for them.

## Task 3 — SIMD DUP/scalarization

Add a narrowly scoped vector-to-scalar lowering helper in a new analysis file and
its own tests. Touch `NewArmV8InstructionSet.cs` only for the smallest hook. Recover
`DUP` broadcasts and the following lane-wise integer operations when all consumed
lanes are provably equivalent. Keep a vector value when equivalence is not proven.

Concrete failing family: ACTk `CalculateHash(long/ulong)` reports repeated `DUP
vector broadcast is not supported` followed by undecoded operations.

Acceptance: a broadcast/hash fixture produces the same scalar 64-bit result as the
reference expression for boundary inputs; unsupported non-equivalent lanes remain
diagnosed rather than guessed.

## Task 4 — managed memory projection

Own `Cpp2IL.Core/Analysis/MetadataResolver.cs`, `ArrayRecovery.cs`, and a new focused
test file. Convert native loads/stores rooted at proven managed receivers into
field/array/string operations using IL2CPP layout metadata. Cover object field
offsets, array length/data, element stride, and `char[]` (`ldrh`) access. Reject
ambiguous roots.

Reference native loop for `HashUtils.CalculateHash(char[])`:

```asm
ldr  x9, [x8, #0x18]       // managed array length
add  x8, x8, #0x20         // first UTF-16 element
ldrh w10, [x8], #0x2
add  w11, w0, w0, lsl #5
eor  w0, w11, w10
```

Acceptance: the fixture recovers a managed char-array loop with no unmanaged-load
diagnostic and matches the reference hash on empty, ASCII, and non-ASCII arrays.

## Task 5 — local type lattice and invalid `stloc`

Own `Cpp2IL.Core/Analysis/LocalVariables.cs` plus a new test file. Make local typing
flow-sensitive enough that register reuse does not merge unrelated float, reference,
integer, and value-type lifetimes into one invalid CLR local. Split a local when
definitions have incompatible CLR stack kinds; preserve aliases within one lifetime.

Concrete failure: `ParallaxBackgroundMaterialDriver.UpdateMaterial()` reaches Mono
as `InvalidProgramException ... IL_011f: stloc 14` despite an empty diagnostic list.
Its native body keeps the parallax value in `s8` while reusing X registers for
references and field addresses.

Acceptance: a register-reuse fixture produces distinct valid locals and survives
AsmResolver body build plus runtime JIT preparation.

## Task 6 — numeric bitcasts versus conversions

Own `Cpp2IL.Core/IlGenerator.cs` and a new focused test file. Distinguish ARM64
`FMOV` bit reinterpretation from numeric conversion and prevent integer logical
operations from being emitted directly over CLR `float` locals. Emit a legal
bitcast sequence or keep an integer carrier, then restore float only at a proven
float consumer.

Concrete failures are `Unrecoverable integer operation: Or ... (System.Single)`
and downstream `InvalidCastException` during Unity scene serialization.

Acceptance: float/int round-trip and sign-bit fixtures preserve exact bits including
NaN payloads and negative zero; emitted IL JITs without casts or boxing.

## Task 7 — interface, virtual, and delegate dispatch

Own `InterfaceDispatchRecovery.cs`, `DelegateInvokeRecovery.cs`, and their tests.
Resolve indirect calls from proven IL2CPP vtable/interface slots and delegate
`invoke_impl` layouts into `callvirt`/delegate `Invoke`. Require an exact receiver
type plus slot/signature match; otherwise keep the diagnostic.

Acceptance: class virtual, interface, multicast delegate, and generic-interface
fixtures recover the correct target signature without hardcoded addresses.

## Task 8 — RGCTX/shared generics

Own `RgctxResolver.cs`, `GenericInstanceFieldLayout.cs`, and their tests. Recover
type/method/field operands loaded through RGCTX tables and shared-generic class
metadata. Preserve the concrete generic context through calls and field accesses.

Acceptance: nested generic type, generic value-type field, and shared generic method
fixtures resolve exact constructed descriptors; an open/unavailable context stays
explicitly unresolved.

## Task 9 — key-function/thunk discovery

Own `NewArm64KeyFunctionAddresses.cs`, `BaseKeyFunctionAddresses.cs`, and focused
tests. Replace residual absolute-address misses with structural discovery of IL2CPP
helpers and one-hop/tail-call thunks. The corpus repeatedly misses a small set of
addresses thousands of times; detect them by instruction shape and referenced
metadata, never by Castle addresses.

Acceptance: synthetic relocated binaries discover the same helper at two base
addresses; false-positive near-matches are rejected.

## Task 10 — runtime-JIT validation oracle

Own a new minimal tool/test project only. Build a validator that loads a recovered
assembly with its dependency directory and asks the runtime to JIT/prepare every
concrete method without invoking game behavior. Emit deterministic JSON containing
assembly, token, signature, exception type, and message. A method that cannot be
prepared must make the command fail.

Acceptance: a tiny fixture assembly containing a verifier-valid-looking but runtime-
invalid `stloc` is caught, while a valid control assembly passes. Do not duplicate
ILVerify; this tool exists specifically for failures that ILVerify missed.

