Ты работаешь над общим восстановлением оптимизированного ARM64 SIMD в Cpp2IL.

Repo: `https://github.com/dankondr/Cpp2IL.git`.
Base: `codex/castle-recovery-r241`.
Branch: `kimi/r241-simd-scalarization`.
PR target: `codex/castle-recovery-r241`.

Симптом Castle corpus: методы наподобие ACTk `CalculateHash(long/ulong)` получают
`DUP vector broadcast is not supported`, затем цепочку `UNIMPLEMENTED`, хотя
оптимизатор просто векторизовал scalar integer hash. Нужен общий и доказуемый
lowering, не ручное тело метода.

Сделай узкий helper/pass в новом файле, который:

- моделирует `DUP` broadcast;
- сворачивает последующие lane-wise integer ops в scalar expression только когда
  все реально потребляемые lanes доказанно эквивалентны;
- сохраняет width/signedness и wraparound;
- не scalarize-ит shuffle, unequal lanes или неизвестную lane provenance;
- в неоднозначном случае оставляет явный diagnostic.

Ownership: новый analysis/helper file, новый focused test file. Допускается
минимальный hook в `NewArmV8InstructionSet.cs`; не переписывай сам decoder Disarm,
local typing, IL generator, RGCTX или output format. Если нужного mnemonic нет в
Disarm, зафиксируй зависимость от Task 1 и тестируй pass на ручном ISIL fixture.

Tests: broadcast 32/64-bit, add/xor/multiply hash sequence, boundary values,
negative case с разными lanes. Reference result вычисляй обычным C# unchecked
scalar expression.

Definition of done: до фикса positive fixture остаётся unsupported, после выдаёт
точный scalar result без `NoteDecompilerIssue`; negative fixture не угадывается;
targeted tests и net10 build проходят; нет Castle-specific идентификаторов;
commit запушен и PR открыт в baseline.

Обязательный corpus gate: вместе с промптом приложен архив
`castle-busters-il2cpp-r241-evidence.tar.zst`. Прочитай его `README.md`, проверь
SHA-256, не коммить evidence. После фикса перегенерируй весь corpus отдельным
`run-cpp2il.sh` output и сравни `DUP vector broadcast`, `UNIMPLEMENTED` и
unrecoverable-operation counts с baseline manifests. В PR приложи exact counts и
exit code. Без corpus run не утверждай, что Castle исправлен.
