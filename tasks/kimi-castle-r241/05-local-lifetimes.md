Ты исправляешь flow-sensitive local typing Cpp2IL.

Repo: `https://github.com/dankondr/Cpp2IL.git`.
Base: `codex/castle-recovery-r241`.
Branch: `kimi/r241-local-lifetimes`.
PR target: `codex/castle-recovery-r241`.

Runtime oracle поймал `InvalidProgramException` в игровом
`ParallaxBackgroundMaterialDriver.UpdateMaterial(): IL_011f stloc 14`, хотя recovery
manifest не содержал diagnostics, MaxStack совпал и обычный verifier пропустил тело.
Native method хранит float parallax value в `s8`, одновременно переиспользуя X
registers для references и field addresses. Текущий local inference сливает
несовместимые CLR stack kinds в один local.

Ownership:

- `Cpp2IL.Core/Analysis/LocalVariables.cs`;
- новый focused tests file;
- не меняй `IlGenerator.cs`, ARM decoder, metadata resolver или output format.

Сделай минимальную flow/lifetime корректировку: definitions одного physical
register должны оставаться одним local только внутри совместимой live range.
При несовместимых stack kinds (`I4/I8/F/native-int/O/&/value-type`) разделяй local
по SSA/liveness boundary. Настоящие aliases внутри одной lifetime сохраняй.
Не лечи проблему заменой значения на `default`, `object` или `pop`.

Tests: X/S register reuse across branches, float затем reference, int затем struct,
phi с совместимыми integer widths, alias within one range, loop-carried compatible
local. Проверяй не только объявленные types, но и generated body/JIT preparation.

Definition of done: regression fixture раньше генерирует invalid `stloc`, после —
разные корректные locals; JIT prepare проходит; targeted tests и net10 build
проходят; нет method-specific repair; commit запушен и PR открыт в baseline.

Обязательный corpus gate: приложен архив
`castle-busters-il2cpp-r241-evidence.tar.zst`. Распакуй и проверь его по README,
не коммить raw inputs. После фикса перегенерируй весь corpus. Помимо diagnostic
counts, проверь recovered token `0x0600152d` в `CastleClashers.Game.dll`: его тело
должно JIT/prepare без incompatible `stloc`. В PR приложи before/after evidence и
exit code. Unit test без corpus run не считается Castle validation.
