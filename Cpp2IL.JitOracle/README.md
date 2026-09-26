# Cpp2IL.JitOracle

Minimal runtime validation oracle for recovered .NET assemblies. It exists to
catch IL that is structurally well-formed (correct tokens, MaxStack, EH regions)
yet invalid at JIT time — the class of error Unity/Mono reported as

```
InvalidProgramException: Invalid IL code in <Type>:<Method> (): IL_xxxx: stloc N
```

that slipped past purely structural recovery checks.

The tool asks the runtime JIT to prepare every concrete method body without
executing any user code, and writes deterministic JSONL records.

## Usage

```
jitoracle --assembly <dll> [--deps <dir>] [--vectors <json>] [--out <file>]
```

- `--assembly` — managed assembly to inspect (required).
- `--deps` — directory with dependency assemblies; defaults to the target's own
  directory. Framework/facade references (`mscorlib`, `System.*`, `netstandard`,
  `Microsoft.*`) resolve against the host runtime instead, so recovered BCL
  stubs never shadow the real runtime.
- `--vectors` — explicit opt-in execution mode. Invokes only the allowlisted
  public static methods listed in the JSON file, only with supported
  primitive/string arguments, and compares the exact result. No searching for
  similar methods, no constructors, no arbitrary game logic.
- `--out` — write JSONL to a file instead of stdout.

Exit codes: `0` all prepared and all vectors pass, `1` any preparation or
vector failure, `2` usage/IO error.

## Prepare-only (default)

Every method is emitted as exactly one record, ordered by metadata token:

```json
{"record":"method","assembly":"RecoveryReference","token":"0x06000005","signature":"System.Int32 RecoveryReference.BitcastCases::FloatCarrierOr(System.Single, System.Int32)","outcome":"prepared"}
{"record":"method","assembly":"RecoveryReference","token":"0x06000008","signature":"System.Int32 RecoveryReference.IOperation::Apply(System.Int32)","outcome":"skipped","reason":"abstract"}
{"record":"method","assembly":"RecoveryReference","token":"0x0600001C","signature":"System.Int32 RecoveryReference.GenericCases::EchoInt(System.Int32)","outcome":"failed","exception":"System.InvalidProgramException","message":"Common Language Runtime detected an invalid program."}
```

Skip reasons: `abstract`, `pinvoke`, `internal-call`, `open-generic`,
`no-il-body`. Constructors are enumerated but only *prepared* — never invoked.

## Vectors mode

The vectors file mirrors `reference-vectors.json` schema 1:
`{"cases":[{"method":"Ns.Type::Name","args":[...],"result":...}]}`. Each case is
resolved by exact name among public static methods of the named type, invoked
once, and recorded as `pass`, `mismatch`, `exception`, or `resolution-error`.

## Runtime identity

The first record always identifies the host runtime:

```json
{"record":"runtime","runtime":"CoreCLR","framework":".NET 10.0.12","os":"Ubuntu 22.04.5 LTS","arch":"X64","jit":"RyuJIT"}
```

CoreCLR's RyuJIT and Unity's Mono JIT do not verify the same IL classes.
`RuntimeHelpers.PrepareMethod` on CoreCLR catches structural defects
(stack-depth violations, out-of-range local indices, bad branch targets) but
does **not** verify primitive type-mismatch stores (e.g. `stloc` of an
`int32` value into a `float32` local compiles to a bit-store). Outcomes
therefore carry the runtime identity explicitly; a `prepared` verdict means
"this runtime's JIT accepted the body", not "every runtime will". Concrete
example: the r241 `ParallaxBackgroundMaterialDriver::UpdateMaterial` body that
Unity Mono rejected with `InvalidProgramException ... stloc` prepares cleanly
on CoreCLR.

Malformed IL can also crash the native JIT itself (observed on RyuJIT with
GC-hole-style bodies): the process then dies with a hard fault that no
in-process catch can intercept. Records are flushed line-by-line (`AutoFlush`),
so the JSONL stream preserves every verdict up to the crash — run one process
per assembly when sweeping many files.

## Tests

`Cpp2IL.JitOracle.Tests` builds two fixture assemblies: a valid control
(`Cpp2IL.JitOracle.Fixtures.Valid`) and an intentionally runtime-invalid body
emitted via `PersistedAssemblyBuilder` with an out-of-range `stloc` — the same
`IL_xxxx: stloc N` failure class — proving the oracle catches it without the
process dying.
