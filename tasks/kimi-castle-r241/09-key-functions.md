Ты исправляешь structural discovery IL2CPP runtime helpers и thunks в Cpp2IL.

Repo: `https://github.com/dankondr/Cpp2IL.git`.
Base: `codex/castle-recovery-r241`.
Branch: `kimi/r241-key-functions`.
PR target: `codex/castle-recovery-r241`.

Castle manifests тысячи раз повторяют небольшой набор `Method not found @...`.
Абсолютные адреса меняются между играми/builds; правильное решение — распознать
IL2CPP helper либо one-hop/tail-call thunk по instruction shape, calling convention
и metadata usage.

Ownership:

- `Cpp2IL.Core/Il2CppApiFunctions/NewArm64KeyFunctionAddresses.cs`;
- `Cpp2IL.Core/Il2CppApiFunctions/BaseKeyFunctionAddresses.cs`;
- focused tests;
- не меняй decoder, managed dispatch, metadata resolver или output format.

Сначала инвентаризируй уже известные helper signatures и существующий discovery.
Добавь только высокоуверенные недостающие shapes: relocated direct branch, ADRP+
ADD/LDR materialization, one-hop veneer, tail-call thunk. Любая signature должна
проверять достаточный surrounding pattern и reject near-match. Никаких Castle
addresses и эвристики “ближайшая функция”.

Tests создают синтетические relocated ARM64 blobs: один helper на двух image bases,
direct и thunk forms, несколько похожих ложных совпадений. Результат обязан быть
одинаковым после relocation.

Definition of done: discovery детерминирован и position-independent; negatives
отклоняются; targeted tests и net10 build проходят; commit запушен и PR открыт в
baseline с перечислением новых structural patterns.

Обязательный corpus gate: приложен
`castle-busters-il2cpp-r241-evidence.tar.zst`. После SHA-256 verification запусти
полный corpus новым `run-cpp2il.sh` output. В PR приложи before/after frequency
table для всех `Method not found @...`, число полностью устранённых повторяющихся
targets, общий exit code и false-positive/regression audit. Нельзя добавлять сами
Castle addresses в production logic или tests. Raw evidence не коммить.
