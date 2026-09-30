# The bytes an access covers decide which fields it names (castle-recovery#211)

Native code moves bytes. One store can cover a whole struct, several fields, or
the end of one field and the start of the next, and the register a constant
travels in says nothing about what its bytes are.

Rules, in `MetadataResolver.ResolveFieldOffsets`:

- A primitive or an enum is a leaf whatever the access width. Its private
  `m_value`/`value__` is never a field of the access; through `ref T` a
  whole-value access stays a dereference (`ldobj`/`stobj`).
- `CoveredFields(owner, offset, size)` lists the fields a byte range covers. A
  field cut in half has no answer; a struct field wholly inside a zeroed range is
  one part.
- A store whose source bits are known is one store per covered field, each taking
  its own bytes, typed by the field (`SplitConstantStore`). Known bits are an
  immediate, a float, double or vector literal, or a register whose single
  definition moves or shifts one (`ConstantBits`). `LDR Q0` of a literal stored
  over four `int` fields is four integers; `LDR D0` stored over two `float` fields
  is two floats, not one double converted to float.
- Adjacent zero stores (`STP XZR, XZR`) are one zeroed range. A zeroed struct
  field is `default(T)`: the recorded width proves every byte
  (`FieldReference.AccessSize`, read by the generator).
- Static storage is split over the type's own static fields the same way. A generic
  base class is passed over when the range touches none of its fields; a generic
  owner or a generic struct cut by the range has no answer yet.
- Fields the method may not name (another assembly's private members) are not
  split into; the store keeps its diagnostic.

Float and vector stores keep `AccessSize` 0 on the memory operand, a convention
other passes read. Their real width is `Instruction.NativeStoreWidthBytes`.

One defect found on the way, in `Arm64VectorScalarizer`: the cache of shifted
lane temporaries named its source by register. After the register was reloaded,
the second store's high lane reused the first value's temporary, with no
diagnostic. The cache now lives for one instruction.

The ISIL dump prints the control-flow graph, which is what the generator emits
from; instructions a pass inserts were invisible in the converted list.

Tests: `Cpp2IL.Core.Tests/Regression/AccessWidthTests.cs`,
`Arm64VectorScalarizerTests.HighLaneOfAReloadedRegisterIsShiftedAgain`.
