Ты строишь минимальный runtime validation oracle для recovered .NET assemblies.

Repo: `https://github.com/dankondr/Cpp2IL.git`.
Base: `codex/castle-recovery-r241`.
Branch: `kimi/r241-runtime-jit-oracle`.
PR target: `codex/castle-recovery-r241`.

Контекст: Castle r241 имел формально построенные bodies и совпадающий MaxStack, но
Unity/Mono поймал `InvalidProgramException ... stloc`, которого текущая проверка не
нашла. Нужен отдельный oracle, который ловит runtime-invalid IL до Unity build, не
исполняя игровую бизнес-логику.

Ownership: только новый минимальный tool/test project и, если необходимо, одна
строка подключения в solution. Не меняй decompiler/recovery production code.

Инструмент принимает assembly path и dependency directory, детерминированно
перечисляет concrete methods, загружает зависимости и просит runtime JIT/prepare
каждое тело без вызова метода. Он пишет JSON records: assembly, metadata token,
signature, outcome, exception type/message. Любая ошибка preparation даёт non-zero
exit. Abstract/PInvoke/runtime/internal-call методы классифицируются как skipped с
причиной. Порядок output стабильный.

Добавь отдельный явно включаемый режим `--vectors FILE`: он вызывает только
allowlisted public static методы, перечисленные в JSON, только с поддержанными
primitive/string arguments, и сравнивает exact result. Никакого поиска и исполнения
«похожих» методов, constructors или произвольной игровой логики. JSON record также
содержит expected/actual либо exception. Prepare-only остаётся default.

Сделай две крошечные fixture assemblies: valid control и намеренно runtime-invalid
body с несовместимым `stloc`, максимально похожий на обнаруженный класс ошибки.
Тест доказывает, что valid проходит, invalid ловится и процесс не падает целиком.
Не дублируй ILVerify и не выполняй constructors/method bodies ради проверки.

Учти, что CoreCLR и Unity Mono могут различаться: явно запиши runtime identity в
JSON. Если `PrepareMethod` на выбранном runtime не ловит fixture, исследуй и выбери
минимальный безопасный механизм JIT compilation; не переходи к вызову произвольного
кода.

Definition of done: CLI имеет `--help`, deterministic JSON и exit codes; tests и
net10 build проходят; нет зависимости от Castle binaries; commit запушен, PR открыт
в baseline, URL возвращён.

Обязательный integration gate: приложен
`cpp2il-arm64-paired-reference-v1.tar.zst`, SHA-256
`16444de84e8d43ec08a2579bf1bfca4d5383dfa58711189b29c24b585bfb4535`.
Сначала проверь его hashes. Его standalone `verify-recovered.sh` — независимый
контроль ожидаемых результатов.
Новый tool в `--vectors` mode должен дать те же per-method outcomes на baseline
recovered `RecoveryReference.dll`: обнаружить FP-carrier, virtual/delegate и
generic semantic failures, которые prepare-only не обязан видеть. На исходной
managed fixture assembly все vectors должны проходить; на намеренно испорченной —
детерминированно падать. Не меняй vectors ради зелёного результата.

Castle archive для этой задачи используется только в prepare-only mode после
merge: нельзя исполнять arbitrary Castle methods. Если он доступен, приложи число
prepared/failed/skipped assemblies/methods; его отсутствие не блокирует PR, но
paired reference gate обязателен.
