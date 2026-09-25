Ты восстанавливаешь indirect managed dispatch в Cpp2IL.

Repo: `https://github.com/dankondr/Cpp2IL.git`.
Base: `codex/castle-recovery-r241`.
Branch: `kimi/r241-managed-dispatch`.
PR target: `codex/castle-recovery-r241`.

В Castle manifests 7,800 `Indirect call`, 1,176 `Indirect jump` и много обращений к
delegate `invoke_impl`/interface slots. Нужен общий resolution, не адресная таблица.

Ownership:

- `Cpp2IL.Core/Analysis/InterfaceDispatchRecovery.cs`;
- `Cpp2IL.Core/Analysis/DelegateInvokeRecovery.cs`;
- отдельные tests этих passes;
- не меняй decoder, local typing, RGCTX resolver, key-function discovery или
  output-format semantic hardcodes.

Восстанавливай `callvirt`/delegate `Invoke` только если доказаны receiver type,
slot/interface map и полная signature включая generic context/byref. Поддержи class
virtual call, interface call, delegate invoke/tail invoke и multicast delegate
contract. При неоднозначности сохраняй diagnostic — неправильный target хуже
неполного восстановления.

Tests: overridden virtual, explicit interface implementation, inherited interface,
generic interface, closed delegate, multicast delegate, signature mismatch and
ambiguous slot negative cases. Проверяй target descriptor и generated executable IL.

Definition of done: positive fixtures больше не indirect; negatives не угадываются;
targeted tests и net10 build проходят; нет Castle names/addresses/tokens; commit
запушен и PR открыт в baseline.

Обязательный semantic-reference gate: используй приложенный
`cpp2il-arm64-paired-reference-v1.tar.zst`, SHA-256
`16444de84e8d43ec08a2579bf1bfca4d5383dfa58711189b29c24b585bfb4535`.
Он содержит source → generated IL2CPP C++ → ARM64 binary/metadata и
source-generated result vectors. На baseline
`DispatchCases.Virtual` и `DispatchCases.Delegate` должны воспроизводимо падать,
а `DispatchCases.Interface` уже проходит и является non-regression control. Запусти
`run-cpp2il.sh` и `verify-recovered.sh` до/после. После фикса все dispatch vectors
обязаны совпасть с исходным C#, а recovered target/call kind — с generated C++ и
metadata slot/interface map. Валидный `callvirt`, исчезнувший diagnostic или JIT
без совпадения результатов не считается успехом. Reference files не изменяй и
fixture-specific names/addresses в production code не добавляй.

Обязательный corpus gate: приложен
`castle-busters-il2cpp-r241-evidence.tar.zst`. Проверь SHA-256, прочитай README и
не добавляй raw в git. После фикса запусти весь corpus через `run-cpp2il.sh`.
В PR укажи before/after counts `Indirect call`, `Indirect jump`, unknown call target
и unverifiable delegate construction, плюс exit code и regression summary. Приложи
отдельно paired semantic before/after. Без любого evidence не заявляй semantic или
Castle improvement соответственно.
