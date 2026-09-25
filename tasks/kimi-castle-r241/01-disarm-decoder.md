Ты работаешь над форком Cpp2IL для семантически точного восстановления ARM64
IL2CPP-игр.

Репозиторий: `https://github.com/dankondr/Cpp2IL.git`.
Начальная ветка: `codex/castle-recovery-r241`.
Создай ветку: `kimi/r241-disarm-decoder`.
PR открывай обратно в `codex/castle-recovery-r241`, не в `development`.

Задача: улучшить декодер Disarm, лежащий в `vendor/Disarm`, для ARM64 words,
которые LLVM корректно декодирует, а Disarm возвращает как undefined или
`UNIMPLEMENTED`. Приоритет — Advanced SIMD scalar/lane инструкции, встречающиеся
в оптимизированных integer hash loops. Cpp2IL уже использует vendored Disarm,
поэтому никакие NuGet-подмены не нужны.

Жёсткий scope:

- меняй только `vendor/Disarm/**` и затем submodule pointer в родительском repo;
- не меняй Cpp2IL instruction mapping;
- не добавляй Castle-specific адреса, токены или имена методов;
- не маскируй неизвестные инструкции как `NOP`.

Сначала найди реально отсутствующие decoder cases сравнением с LLVM либо по
существующим TODO/undefined paths. Для каждого исправленного encoding добавь
table-driven тест с raw 32-bit word. Проверяй mnemonic, W/X или vector width,
arrangement, registers, lane, immediate, shift/extend. Negative near-match тоже
должен остаться undefined, если encoding reserved.

Definition of done:

1. Новые raw-word тесты падают до исправления и проходят после.
2. Результат Disarm совпадает с `llvm-objdump` по всем полям, не только mnemonic.
3. Все существующие Disarm tests проходят.
4. В `vendor/Disarm` есть отдельный commit, запушенный в `dankondr/Disarm`.
5. Родительский Cpp2IL commit обновляет только submodule pointer.
6. Открыт PR в `codex/castle-recovery-r241`; в описании перечислены поддержанные
   encoding families и команды проверки.

Не заявляй, что Castle corpus исправлен: в облаке его нет. Твоя единица истины —
raw instruction fixture и ARM64 specification/LLVM decoding.
