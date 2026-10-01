# #262 — scope stragglers: narrowed call results and stale MethodInfo binds

Cluster: `type: literal operand cannot fill a System.Double slot` and
`call: stale MethodInfo* bound to a mismatched signature` — the two typing
mechanisms behind the castle-building scope's remaining type-inference
diagnostics (castle-recovery#262).

## Rule

Two shared mechanisms produced the same `Double`-slot diagnostic family in
methods whose native code is unambiguously single-precision:

- **A call-defined local took the callee's declared return type, not the
  marked write width.** A native helper bridged onto a `Double`-declared
  method (the libm wrappers) writes only its S register back:
  `fmov s12, #1.0` … `fcmp s0, s12` (`EngineersController::IsInRange`,
  `CheckIfTargetPositionIsTooClose`) and the `fmov s0, #±0.5` … `fadd s0, s9,
  s0` lane of `CastleMaker+<>c__DisplayClass123_0::<DetectStep>b__0`. The
  instruction carries `NativeFloatWidthBits = 32`, but `CallDefinedLocalType`
  returned the declared `Double` and the comparison contract rejected the
  4-byte literal. `MarkedNumericResultType` now folds the declared type down
  to the marked write width (`Double`→`Single` on a 32-bit float mark,
  `Int64`→`Int32` on a 32-bit integer mark, and the symmetric 64-bit
  widenings), matching how `SeedNative*Widths` already types the destination
  local. `ComputeNumericLocalTypes` applies the same rule to union-class
  picks: when every defining instruction proves no more than four bytes
  (`Immediate.ProvenBytes`, `FloatLiteral`), `NarrowNumericPickToProvenWidth`
  narrows `Double`→`Single` / `Int64`→`Int32` / `UInt64`→`UInt32`. A pick
  backed by a wider or unproven definition keeps its width — a type that
  cannot be proven stays diagnosed.

- **`ResolveCallsViaMethodInfo` bound any MethodInfo* operand to its callee,
  whatever the argument slots held.** A shared stub not in `MethodsByAddress`
  falls back to the MethodInfo* local at the hidden-argument slot — but
  register reuse leaves the previous call's MethodInfo* in place, so a
  `bl 0x32E0B50` whose slots hold `List<ESP>`/`Boolean`/`Il2CppMethodInfo`
  was bound to `Dictionary<Vector2Int, Transform>.TryGetValue(dict, key, out
  Transform&)` anyway (`CastleMaker::SpawnShieldsFromPlacements` at
  `0x32E0B50`/`0x32E0C10`/`0x38E44AC`, `MoveNext` on a methodinfo receiver).
  The wrong signature then seeded the shared register-version locals to its
  parameter types, which manufactured `Boolean→Transform&`/`IntPtr→V2I`
  conversions and hid the real conversions behind them — the "TValue is not
  inferred" symptom. `CallShapeConsistentWithMethodInfo` now rejects a bind
  whose operand shape cannot fill the represented signature: a value-type
  parameter refuses a proven reference-type/non-pointer slot, a reference
  parameter refuses a mismatched `&` cell or a value-type payload, a byref
  parameter accepts only address-shaped operands (`&x`, pointers, handles,
  untyped locals whose definitions produced an address), and the receiver
  slot refuses a runtime handle unless the callee is itself the reflection
  surface the handle represents (`IsReflectionReceiverFamily`). A refused
  bind leaves the unresolved-target diagnostic in place rather than
  inventing a callee.

Refusing the stale binds unmasks the operand clutter the wrong signatures
were absorbing: an unresolved call keeps its full lifted argument list, so
the erased register-version locals rejoin the SSA union classes — the
`type: no legal conversion` and `dataflow: zero on phi edge` growth is the
same content honestly diagnosed, and each new `call: unresolved target` is
a stub address that was previously bound to a callee it could not have
reached.

## Tests

`Cpp2IL.Core.Tests/Regression/`:

- `ProvenWidthLiteralTests.MarkedSinglePrecisionCallResultFillsFloatSlot` —
  a `NativeFloatWidthBits = 32` call on a `Double`-declared callee feeding a
  `CheckLess` against a 4-byte literal emits `ldc.r4`, not the Double-slot
  diagnostic.
- `GenericDictionaryReadTests.StaleMethodInfoArgumentTypeMismatchStaysUnresolved`
  — a `TryGetValue(dict, valuetype-key, out ref&)` shape whose key slot
  carries a proven string stays an immediate target.
- `GenericDictionaryReadTests.GenericDictionaryOutValueSeedsTheAddressedCell`
  — the matching shape binds and the concrete instantiation's `TValue`
  seeds the out cell for the typed consumer.
