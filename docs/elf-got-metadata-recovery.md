# ELF GOT metadata loads

ARM64 IL2CPP can load a metadata-slot address through the ELF GOT, then load the
metadata value through that address. The metadata resolver previously recognized
only the latter's absolute form. Consequently string/type/method handles stayed
unresolved, preventing downstream field and call resolution.

The fix recognizes aligned `.got` entries wholly inside GNU RELRO, reads their
already-applied relocation, and requires the target to decode as a valid metadata
usage. In SSA it rewrites only the zero-offset second load to an absolute metadata
load. It retains the address-producing load until existing dead-code elimination
can remove it. No unknown load or call is replaced with a default value by this fix.

## Reproduction

Base: `b5ad444b82267cb1e4b88b8b373c008105bdea52` (upstream development at testing).
SDK: .NET `10.0.100`, macOS ARM64. Build:

```sh
dotnet restore Cpp2IL.slnx -p:NuGetAudit=false
dotnet build Cpp2IL/Cpp2IL.csproj -f net10.0 --no-restore -p:UseSharedCompilation=false
NO_COLOR=1 dotnet Cpp2IL/bin/Debug/net10.0/Cpp2IL.dll \
  --force-binary-path "$binary" --force-metadata-path "$metadata" \
  --force-unity-version 6000.0.72f1 \
  --use-processor attributeanalyzer,attributeinjector \
  --output-as dll_il_recovery --output-to "$new_output_directory"
```

The local pilot used Castle Busters 1.11.1 Android ARM64. Inputs are not distributed:

| Input | SHA-256 before and after |
|---|---|
| `libil2cpp.so` | `a2f8b8416e243e7d7f1423d2d638801f4ca03241aa3b1f85633b2b59f3fd0581` |
| `global-metadata.dat` | `412a4ac68e773822fb232f5e6a29c7b498a0b90731bacc6169b6113a07f7cc79` |

Both executions completed 70,310 analyzed methods. An independent read-only Cecil
audit of nine game assemblies (17,026 method records) reproduced the historical
baseline and measured:

| Metric | Base | Patched |
|---|---:|---:|
| Methods with `NoteDecompilerIssue` | 9,907 | 7,889 |
| Total issue strings | 119,905 | 64,250 |
| Unmanaged memory loads | 79,820 | 38,970 |
| Method not found | 32,375 | 18,340 |
| Indirect calls | 2,381 | 2,202 |
| Not implemented instructions | 1,822 | 1,822 |
| Detected structural IL errors | 261 | 261 |
| `Bootstrap.Awake` issues | 3 | 0 |
| `Bootstrap.Start` issues | 14 | 6 |

`Awake` now exposes the string passed to PlayerPrefs and the static vibration
field assignment. `Start` recovers delegate targets and singleton getter calls.
The auditor's startup graph grows from 1,323 to 1,835 reachable methods because
restored call edges expose previously hidden dependencies. Its runtime gate stays
blocked: the existing runtime was intentionally left unchanged and remains stubbed.

## Checks and limits

```sh
dotnet run --project Cpp2IL.Core.Tests --no-restore -- --filter 'FullyQualifiedName~GotMetadataTests'
dotnet run --project Cpp2IL.Core.Tests --no-build
dotnet test --project LibCpp2ILTests/LibCpp2ILTests.csproj --no-restore
```

Core suite: 77 passed. LibCpp2IL runner: 5 passed; its legacy async-void
network-fixture tests offer limited assurance. Disabling the new rewrite makes
the regression fail (`expected [2000], actual [slot @ x20]`); restoring it passes.
The fixture also checks that the first load, nonzero offsets, and unknown slots
stay unchanged. The native pilot exercises the ELF region checks and real metadata.

This deliberately does not handle missing section headers, writable GOTs, copied
or merged slot-address locals, arbitrary pointer chains, or interface dispatch.
It does not fix existing structural/type-invalid IL and has no runtime oracle;
fewer diagnostics and recovered references do not certify behavioral equivalence.

## Follow-up: ARM64 interface dispatch

The remaining six `Bootstrap.Start` diagnostics came from its interface lookup:
class interface count (`+0x12e`), interface-offset table (`+0xb0`), entry interface,
slow helper, and final indirect call. Three existing gaps prevented recovery:
the ARM64 lifter discarded `SXTW #4` on an extended-register add; the matcher
expected `klass+(scaledIndex+0x138)` instead of ARM64's
`(klass+scaledIndex)+0x138`; and interface calls needed `callvirt` to preserve
runtime dispatch (static interface calls still use `call`).

The fix explicitly lowers signed low-32-bit extension to 64 bits before shifting,
accepts the ARM64 addition order with the existing exact layout/slot checks, and
emits the proper interface call opcode. Existing region escape/side-effect checks
still control lookup removal. No game-specific addresses or names are in the fix.

On the same inputs, compared with the GOT-only result:

| Metric | GOT only | + interface recovery |
|---|---:|---:|
| Methods with issues | 7,889 | 7,844 |
| Total issue strings | 64,250 | 63,128 |
| Unmanaged loads | 38,970 | 38,345 |
| Method not found | 18,340 | 18,232 |
| Indirect calls | 2,202 | 1,857 |
| Structural IL errors | 261 | 217 |
| Bootstrap.Start issues | 6 | 0 |

Core suite: 89 passed, including a native-opcode red-before/green-after test,
five executed synthetic IL signed-boundary cases, four exact scale/slot/layout
checks, and instance/static interface opcode checks. LibCpp2IL runner: 5 passed.
The synthetic arithmetic harness explicitly computed MaxStack; actual generated
Start still declares `.maxstack 0`. That pre-existing header problem is a separate
runtime blocker despite its zero diagnostics. The unchanged runtime gate remains
blocked, with 1,842 reachable methods now exposed; no runtime oracle was run.
