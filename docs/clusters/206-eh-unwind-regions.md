# castle-recovery#206 — unwind-table method extents and landing-pad partitioning

Cluster: `lane:eh`. This is the first of two slices: unwind-table readers,
FDE method extents and handler-code partitioning. Proven `try`/`catch`/
`finally` region emission is the second slice.

## Rule

- `LibCpp2IL` reads `.eh_frame_hdr` + `.eh_frame` + `.gcc_except_table` from
  ELF binaries (`ElfEhTables`): function start -> size, and call-site ranges
  -> (landing pad, action). Binaries without the sections report no unwind
  info and lift exactly as before (`EhFunctions` is `null` on `Il2CppBinary`).
- A method body ends at `min(next function start, FDE end)`
  (`ApplicationAnalysisContext.GetFunctionEnd`), not at the next metadata
  entry alone.
- `EhRegionPartition` runs on the converted ISIL stream before the CFG. The
  normal path is walked from the entry with landing-pad entries as
  fallthrough barriers (jump targets onto pad addresses stay normal). Each
  pad claims the code only it can reach; claimed code that is not
  normal-reachable moves to a `LandingPadRegion` instead of being lifted as
  ordinary instructions. Every unproven region leaves exactly one diagnostic
  naming the pad address.

## Tests

- `LibCpp2ILTests/ElfEhTablesTests.cs` — synthetic ELF bytes: function sizes,
  call sites with landing pads and actions, missing-section and
  unsupported-encoding fallbacks.
- `Cpp2IL.Core.Tests/Regression/EhRegionPartitionTests.cs` — synthetic ISIL:
  pad-only code moves to a region and is diagnosed, a handler that falls back
  into the method keeps the merge point, a normal jump onto a pad address
  keeps the code, a pad with no lifted code still diagnoses, and no unwind
  info leaves the stream alone.

## r241 numbers

Measured in the pull request against control `development` `c9056629`:
`diag_families`, the game-owned table in reference mode and ILVerify
per-method status transitions live there. The remaining slice-2 work
(proven-region emission, `catch`/`finally` typed locals, filters/faults)
is listed under `Gaps` in the PR.
