Ты исправляешь главный кластер Cpp2IL: native memory operations, которые на самом
деле являются managed field/array/string access.

Repo: `https://github.com/dankondr/Cpp2IL.git`.
Base: `codex/castle-recovery-r241`.
Branch: `kimi/r241-managed-memory`.
PR target: `codex/castle-recovery-r241`.

В r241 manifests 142,728 diagnostics `Unmanaged memory load`. Один точный пример
из ACTk `CalculateHash(char[])`:

```asm
ldr  x9, [x8, #0x18]       // managed array length
and  x9, x9, #0xffffffff
add  x8, x8, #0x20         // first UTF-16 element
ldrh w10, [x8], #0x2
add  w11, w0, w0, lsl #5
eor  w0, w11, w10
```

Нужно проецировать memory operands с доказанным managed root в CLR operations:
object field load/store, SZArray length/data/element access и UTF-16 char element.
Используй IL2CPP layout metadata, размер элемента и provenance base pointer.
Не превращай произвольный pointer arithmetic в managed access.

Ownership:

- `Cpp2IL.Core/Analysis/MetadataResolver.cs`;
- `Cpp2IL.Core/Analysis/ArrayRecovery.cs`;
- новый focused test file;
- не меняй instruction decoder, local typing, dispatch или output-format hardcodes.

Tests обязаны покрыть reference/value fields, array length, byte/char/int/reference
elements, post-index increment, invalid header offset, wrong stride и ambiguous root.
Добавь поведенческий char-array hash fixture для empty, ASCII и non-ASCII.

Definition of done: positive fixture не содержит unmanaged-load diagnostic и даёт
точный managed loop; отрицательные fixtures остаются unresolved; targeted tests и
net10 build проходят; production code не содержит названий Castle/ACTk, адресов или
tokens; branch запушен и PR открыт в baseline.

Обязательный corpus gate: используй приложенный
`castle-busters-il2cpp-r241-evidence.tar.zst`. После проверки hashes сохрани
baseline summary, затем после фикса запусти весь corpus через `run-cpp2il.sh` в
новый output. В PR укажи before/after `Unmanaged memory load` counts в целом и
отдельно для `ACTk.Runtime`, `CastleClashers.Game`, `Assembly-CSharp`; проверь,
что другие diagnostics не выросли существенно. Raw inputs в git не добавлять.
