Ты исправляешь различие между ARM64 bit reinterpretation и numeric conversion в
Cpp2IL IL generator.

Repo: `https://github.com/dankondr/Cpp2IL.git`.
Base: `codex/castle-recovery-r241`.
Branch: `kimi/r241-numeric-bitcasts`.
PR target: `codex/castle-recovery-r241`.

Castle Unity build многократно падает на diagnostics вида
`Unrecoverable integer operation: Or ... (System.Single)` и затем
`InvalidCastException`. Причина: ARM64 может переносить одинаковые bits между
integer/FP registers через `FMOV`; это не `conv.*` и не разрешение делать CLR
bitwise operation прямо над `float` local.

Ownership:

- `Cpp2IL.Core/IlGenerator.cs`;
- новый focused test file;
- при необходимости один маленький новый helper рядом с generator;
- не меняй local lifetime analysis, ARM decoder, metadata/dispatch/RGCTX.

Введи корректное emission rule: bitwise op выполняется над integer carrier того же
размера; proven bit reinterpretation использует легальный IL sequence/helper without
boxing; обратно float получается только у proven FP consumer. Numeric conversions
должны по-прежнему использовать numeric semantics.

Tests: float/int32 и double/int64 round-trip, sign-bit OR, negative zero, infinities,
NaN payload preservation, real numeric conversion counterexample, invalid mixed
width. Проверяй exact bits и успешный runtime JIT, не только opcode list.

Не заменяй неизвестное значение нулём/default и не hardcode-ь игровые методы.
Definition of done: tests падают до фикса, после сохраняют exact bits; targeted tests
и net10 build проходят; commit запушен, PR открыт в baseline, URL возвращён.

Обязательный semantic-reference gate: вместе с промптом приложен второй архив
`cpp2il-arm64-paired-reference-v1.tar.zst`, SHA-256
`16444de84e8d43ec08a2579bf1bfca4d5383dfa58711189b29c24b585bfb4535`.
Это не просто тестовые ожидания: в нём лежат известный C#, сгенерированный IL2CPP
C++, настоящий ARM64 `libil2cpp.so`,
metadata и vectors, вычисленные исполнением исходного C# до AOT-компиляции. Проверь
hashes из `README.md`, затем до изменения запусти его `run-cpp2il.sh` и
`verify-recovered.sh`. На baseline обязаны падать ровно целевые
`FloatCarrierOr`/`DoubleCarrierXor`; простые round-trip и настоящий numeric convert
уже проходят. После production-фикса оба carrier-case должны возвращать exact
source result, а все ранее проходившие vectors — остаться зелёными. Сопоставь
получившийся IL также с `source/RecoveryCases.cs` и
`generated-cpp/RecoveryReference.cpp`. Уменьшение diagnostics, валидный IL или JIT
сами по себе acceptance не являются. Не меняй reference source/vectors.

Обязательный corpus gate: используй приложенный
`castle-busters-il2cpp-r241-evidence.tar.zst`, сначала проверив hashes из README.
После unit tests перегенерируй полный corpus в новый каталог. В PR приложи
before/after counts `Unrecoverable integer operation` с float operands,
`InvalidCastException`-связанных recovered paths насколько их можно статически
проверить, общий exit code и отсутствие существенных regressions. Evidence не
коммить. В PR приложи оба независимых результата: paired semantic before/after и
Castle corpus before/after. Без любого из них пометь соответствующий gate как не
пройденный; один gate не заменяет другой.
