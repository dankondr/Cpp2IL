# An inaccessible member access is the inlined member called in place (castle-recovery#217)

The C++ compiler inlines small constructors, accessors and factories across
assemblies. What remains in the caller is a field store or read it cannot
legally express - `x.hiddenValue = v`, `awaiter.task = task`,
`statics.zeroVector.x` - which emission drops as "Inaccessible field store" (or
an access-family sibling).

`Analysis/InlinedMemberRecovery` maps the access back to the member that was
inlined: the accessible member of the accessed type whose own lifted body is
exactly that access.

Rules:

- The accessed type's accessible members are candidate matches: constructors,
  methods, setters, and factories - a static member returning the type is a
  factory. A member qualifies only when its own body is exactly the access:
  stores writing fields of the produced object (`this` for a ctor or void
  writer, the returned local for a producer), or a `return` of a field. A
  getter that returns the same inaccessible field - a private static readonly
  behind `get_Zero`-style members - is a match even though the getter itself
  is the only accessor: `VectorN.zero` reading `zeroVector` is the getter call.
- One match emits the call: `CallVoid` for a writer, `newobj` (or `CallVoid
  .ctor` on a bare value-type local) for a constructor, `Call` plus a `Move`
  into the accessed slot for a producer. Zero or several matches keeps the
  access diagnosed.
- Stores on one object group while consecutive and on the same path. The whole
  set is tried first; when it fails, single leaves fall back to a setter or
  producer match. A group covering a ctor's parameter-written fields in any
  order maps to that ctor with the stored values bound to parameters by name.
- An all-zero group covering the field set can be a `Move dest <- 0` collapse
  instead of a member call, when the member match finds nothing.
- Some receivers cannot be spelled. A local the method uses through a raw
  pointer shape - typed `T&`/`T*`, a `MemoryOperand` base or index, a block-op
  (`MemorySet`/`MemoryCopy`/`MemoryMove`) destination, or an argument to a call
  with no managed target (a native import such as memset) - is an address slot:
  writing `Move local <- struct` binds the slot's emitted type and breaks the
  pointer op that follows (`initblk` on a generic instantiation, `conv.u` on a
  struct, `ret` of a stack pointer). Those accesses stay diagnosed.
- A candidate member's body is read through `Analyze()` under a done-flag +
  lock: emission is parallel and a recovery pass may trigger a nested analysis
  while the member's own decompile runs (`MethodAnalysisContext._analysisDone`).

`Cpp2IL.Core.Tests/Analysis/InlinedMemberRecoveryTests.cs` covers the
synthetic shapes: a read-only struct built through a return buffer, an awaiter
built from a task, a private field behind a public setter, a private static
field behind a public getter, ambiguous members staying diagnosed, and a byref
buffer slot whose rewrite would not verify.
