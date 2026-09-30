# #205 — aggregate result lanes

Cluster: `dataflow: undefined local, float lane V1-V7` from
`docs/P1_ROOT_CAUSES.md` mechanism 2 — 495 game-owned methods read a float
register `V1`–`V7` that nothing stores; 159 have no other diagnostic.

## Rule

AAPCS64 returns a homogeneous float aggregate (`Vector2/3/4`, `Quaternion`,
`Color`, any 1–4 same-width-float struct) one lane per `V` register, and a
9–16 byte non-float composite in `X0:X1`. Cpp2IL already detects these shapes
(`Arm64CallingConventionResolver.TryGetHomogeneousFloatAggregate`) but modeled
the whole result as a single operand in lane 0, leaving reads of `V1`+/`X1`
undefined.

`BaseCallingConventionResolver.ExtraLanes(type, firstLane)` names the
registers a multi-register value occupies besides the first. On ARM64 it
yields `[V(first+i) : offset i*w, width w]` for an `n`-float HFA and
`[X(first+1) : offset 8, size-8]` for a 9–16 byte composite. Call sites get
those registers as `Instruction.ImplicitDefinitions` (pre-SSA in
`NewArmV8InstructionSet.AddCallAt` for directly-known callees, and at
`MetadataResolver.ResolveAll` in `AttachResultLanes` for callees resolved
later), so SSA versions lane reads against the producing call instead of the
entry value.

`AggregateResultLanes` (run inside the `LocalVariables` fixpoint) projects
each lane local onto the field its bytes hold — `FindInstanceFieldPathAtOffset`
must find a field of exactly the lane's width at the lane's offset — so a lane
store spells `result.y`, not an undefined register. For defs attached after
SSA (unversioned), the pass resolves the reaching lane call per use through
immediate dominators. Aggregate parameters project entry-version lane reads
onto the parameter the same way, materializing the parameter's lane-0 local
only when a lane read exists. A lane that no callee return type or declared
parameter type proves, or whose bytes no matching field covers, keeps its
diagnostic — nothing is guessed.

`Arm64CallingConventionResolver.AddParameter` also now consumes
`IntegerRegisterCount` slots for a composite parameter (2 for 9–16 bytes, 0
for >16, else 1), spills a composite to the stack whole when it does not fit
the remaining register file, and only exhausts the register file when a
register-passed composite is the one that cannot fit — per AAPCS C.3/C.4.

The method's own aggregate return is the mirror image: the lifter puts each
lane register on the `Return`'s operands (`AttachReturnLanes`), and
`RebuildAggregateReturns` stores every lane into the field its bytes hold of a
local of the declared return type — `SCVTF S0,W19; SCVTF S1,W0; RET` of a
`Vector2` method returns `new Vector2(x, y)` rather than one `Int32` lane.
A `Return` whose lanes cannot all be proven keeps its extra operands for the
default-fill note.

## Test

`Cpp2IL.Core.Tests/Regression/AggregateResultLaneTests.cs` drives synthetic
ISIL through the real pipeline (`SsaForm`, `CreateAll`,
`ResolveTypesAndFields`, `GenerateIl`):

- `Vector3ReturnStoresIntoConsecutiveFields` — `BL get_position; STP S0,S1;
  STR S2` emits `stfld x/y/z` of one result local, zero undefined locals.
- `QuaternionReturnProjectsAllFourLanes` — V1–V3 spell `y`, `z`, `w`.
- `ScalarFloatReturnLeavesLaneOneDiagnosed` — a `System.Single` return leaves
  a V1 read an undefined local; no lane is invented.
- `SixteenByteStructReturnDefinesBothXRegisters` — X1 spells `hi` at offset 8.
- `AggregateParameterLanesReadAsFields` — an entry `Vector3` parameter's V1
  read spells `p.y`.
- `Vector2ReturnRebuildsStructFromLanes` — `Return(V0,V1)` of a `Vector2`
  method returns a local whose `x`/`y` stores the lanes, no diagnostic.
