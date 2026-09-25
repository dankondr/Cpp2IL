Ты исправляешь общий ARM64→ISIL слой Cpp2IL, а не отдельный метод игры.

Репозиторий: `https://github.com/dankondr/Cpp2IL.git`.
Base: `codex/castle-recovery-r241`.
Ветка: `kimi/r241-shifted-logical`.
PR target: `codex/castle-recovery-r241`.

Castle corpus обнаружил семейство diagnostics `EOR shift LSR is not supported`
в CodeStage ACTk integer hashes. Нужно полноценно реализовать ARM64 logical
shifted-register forms: `AND`, `ANDS`, `ORR`, `EOR`, а также инвертирующие aliases/
forms `BIC`, `BICS`, `ORN`, `EON` для `LSL`, `LSR`, `ASR`, `ROR`, W и X widths.

Ownership:

- `Cpp2IL.Core/InstructionSets/NewArmV8InstructionSet.cs`;
- новый отдельный test file в `Cpp2IL.Core.Tests/Isil/`;
- не трогай Disarm, IL generator, metadata passes и output format.

Требования:

- shifted operand должен быть представлен семантически, а не потерян;
- W operations обязаны иметь 32-bit truncation/zero-extension semantics;
- X operations обязаны сохранять 64-bit semantics;
- zero shift не должен создавать мусорную временную операцию;
- flags у `ANDS/BICS` должны остаться доступны последующим branch recovery;
- invalid/reserved encodings не угадывать.

Добавь raw instruction tests минимум для EOR+LSR, ORR+LSL, ANDS+ASR,
EON/ROR, нулевого и ненулевого shift, W и X. Проверяй получившийся ISIL, operand
width и отсутствие `NotImplemented`.

Definition of done:

1. Tests воспроизводят старый diagnostic и проходят после фикса.
2. Reference evaluator подтверждает wraparound на граничных значениях.
3. `dotnet build Cpp2IL/Cpp2IL.csproj -c Release -f net10.0 --no-restore -m:1`
   проходит.
4. Targeted tests проходят.
5. Нет assembly/method/address/token hardcodes.
6. Commit запушен, PR открыт в baseline-ветку, URL возвращён в финальном ответе.

