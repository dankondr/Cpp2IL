# IL recovery sidecar schema 1

`dll_il_recovery` writes `Assembly.dll.recovery.json` next to each DLL after
serialization. No additional instructions/diagnostics are inserted into method bodies.
Other output formats are unchanged. Existing diagnostic helper behavior is retained.

The manifest is bound to the exact assembly SHA-256 and records emitted method tokens,
signatures, existing diagnostic strings, direct call/function-pointer edges, declared
and computed MaxStack, computation failure, and unverified status. Native context adds
VA and SHA-256 of available method bytes, with explicit lifted-unverified,
intentional-stub, unresolved, external-or-abstract, or analysis-failed output status.
Unavailable native bytes are null, not inferred from managed RVA. Native pointer
information is separate from the output method token; injected/renumbered tokens must
not be mistaken for original metadata tokens. Calls include call/callvirt/newobj,
ldftn/ldvirtftn and jmp, not field operands.

Rows are sorted by emitted token; calls use ordinal ordering, no timestamps or absolute
paths are embedded. Repeat serialization of an unchanged DLL/context is deterministic.
Different complete Cpp2IL runs may produce different DLL hashes/MVIDs; consumers bind
each manifest to its own DLL rather than assuming byte-deterministic DLL emission.

The fixture verifies deterministic serialization, native association, stack bound,
unverified status and unchanged DLL bytes. Castle Busters full pilot produces 183
sidecars; the independent recovery-audit v2 reads emitted DLLs and checks tokens,
signatures, call edges, diagnostics and stack bounds against them. Native fingerprints
are provenance, not an independent runtime oracle. No sidecar status certifies
behavioral equivalence or authorizes automatic transplant.
