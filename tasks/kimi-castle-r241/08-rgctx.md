Ты исправляешь RGCTX и shared-generic recovery Cpp2IL.

Repo: `https://github.com/dankondr/Cpp2IL.git`.
Base: `codex/castle-recovery-r241`.
Branch: `kimi/r241-rgctx-generics`.
PR target: `codex/castle-recovery-r241`.

Большая часть residual unmanaged loads/indirect calls идёт через IL2CPP RGCTX и
shared generic metadata. Нужно донести concrete generic context до field/method/type
descriptors, не подставляя `object` и не угадывая open parameters.

Ownership:

- `Cpp2IL.Core/Analysis/RgctxResolver.cs`;
- `Cpp2IL.Core/Analysis/GenericInstanceFieldLayout.cs`;
- focused tests;
- не меняй ARM decoder, general memory projection, IL generator или dispatch passes.

Покрой RGCTX entries типа, метода и поля; nested constructed generics; shared
reference generic; value-type generic с layout; method generic inside type generic;
byref/pointer/array wrappers. Concrete context должен сохраняться через load, call и
field access. Если контекст действительно open или table entry недоступна, оставляй
явный unresolved diagnostic.

Tests должны доказать exact constructed descriptors и layout offsets, плюс negative
open/ambiguous context. Не используй Castle-specific address/token/name.

Definition of done: positive fixtures разрешаются без erased-object fallback;
negative fixtures остаются unresolved; targeted tests и net10 build проходят;
commit запушен, PR открыт в baseline, в описании указано какие RGCTX kinds покрыты.

Обязательный corpus gate: приложен архив
`castle-busters-il2cpp-r241-evidence.tar.zst`. Распакуй, проверь hashes, не коммить
raw. После фикса выполни полный replay через `run-cpp2il.sh` в новый каталог и
сравни RGCTX-related unmanaged loads, unresolved generics, field-layout и indirect
call diagnostics с baseline. В PR приложи exact before/after counts, exit code и
список регрессий. Без архива результат только unit-validated.
