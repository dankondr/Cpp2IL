# Guard, allocation, diagnostic-tail and native-SP recovery

Four independent conservative corrections, with no game names or addresses in production:

1. A Boolean NOT result keeps Boolean type only when every use is a direct conditional guard. General propagation through mixed pointer/zero phi nodes is deliberately not enabled.
2. AllocateObject/newobj fusion can recover the allocated concrete type's constructor only for a direct, non-abstract, non-generic reference subclass of Object with one parameterless constructor whose complete A64 body is `MOV X1,XZR; B Object::.ctor`. Unknown, value, generic, arbitrary derived and ordinary base-constructor cases remain untouched.
3. Tool-owned diagnostic trailers terminate with `ldnull; throw`, including invalid-stack trailers. This retains diagnostics and malformed original bodies; it does not invent a return. Serialized CLR execution is tested, not only ILVerify.
4. Native SP analysis ignores a proven non-returning helper's synthetic return successor. Proof is ARM64/ELF-only: exact exported il2cpp_raise_exception size and whole wrapper anchor a raise target; bounded straight-line helper traversal rejects conditional, indirect, return, unknown and cyclic paths. It examines at most 24 instructions per helper and depth below five. Only terminal call blocks with a sole one-instruction Return successor and sole predecessor qualify. The shared CFG is not mutated; interior no-return edges remain unsupported.

Castle Busters 1.11.1 exact-input audit (17,026 selected methods): ILVerify-valid 7,703 → 8,011; invalid 9,069 → 8,761; structural errors 75 → 75; diagnostic methods 5,562 → 5,047; diagnostic strings 53,643 → 52,156. Zero valid-to-invalid regressions; zero methods with increased diagnostics. These counts are not semantic equivalence claims.

LoadingUI.StartDots has no diagnostics, declared/computed MaxStack 2/2, and passes ILVerify. Exact A64 StartDots and KillDots execution compared against emitted IL passes 72 bounded cases: null/destroyed/live text, null/inactive/active prior tween, repeated calls, callback-registration boundary mutation, dotMax and sequence reloads. Only warm initialized state, successful allocation and intercepted external boundary contracts are covered. Callback bodies, cold initialization, real Unity/DOTween scheduling, collector semantics and full boot are not verified.

Remaining closure blockers include KillDots' reference-versus-integer-zero comparison (ILVerify StackUnexpected IL000b) and the callback's private String.CreateString call (MethodAccess IL001b, decimal offset 27). CLR acceptance of a tested helper does not override ILVerify. No runtime transplant or asset mutation is authorized by these results.

Rejected broad Boolean propagation and early CFG-pruning trials are retained in the immutable dataset report. The latter changed downstream SSA/cache behavior; final SP-only analysis avoids those changes.
