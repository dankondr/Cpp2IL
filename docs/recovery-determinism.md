# Recovery output determinism

The exception-helper cache stores only completed, full-budget root searches.
Recursive answers depend on the current path and remaining depth, so they are
never read from or published to the address-only shared cache. Cycle detection
is local to each search. Concurrent callers may compute the same root twice;
they publish the same completed answer without observing an in-progress null.
This preserves parallel method recovery and the existing search budget/order.

Only `dll_il_recovery` assigns deterministic module IDs. The identity includes
the consumed binary and metadata snapshots taken before processing layers,
Unity version, producer/core/library/instruction-set/writer build identities,
output-format identity, ordered processing layers and their build identities,
sorted processing configuration, low-memory option, optional WASM framework
content, and assembly/module names. Strings are length-prefixed and the SHA-256
digest is domain-separated. Build identity uses producer module IDs, not just
a release label, so a different producer build invalidates the generated ID.
The output path and emitted file bytes are not inputs to the module ID.

This covers the configured built-in CLI workflow. Arbitrary external mutation
of an application model is not a reproducibility contract. The consumed input
snapshot can include loader fixups; original distribution hashes remain separate
recovery provenance. Assembly SHA-256 remains the evidence/cache binding and is
never replaced with a normalized hash. No methods are promoted by this change.

Regression coverage includes a warmed depth-boundary search, a gated concurrent
in-progress search, a cycle with an alternate branch, complete minimal PE byte
equality, and module-ID separation for changed binary, metadata and assembly.
