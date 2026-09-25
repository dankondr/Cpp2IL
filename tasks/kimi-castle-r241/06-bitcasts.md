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

