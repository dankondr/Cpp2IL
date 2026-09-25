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

