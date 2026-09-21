# Reference/null comparisons and exact String allocation shims

Two independent general fixes, with no game-specific identifiers in production:

* Equality/inequality with a literal integer zero emits `ldnull` only when the other operand is a proven managed reference (class/object/string/array/non-value generic instance). Numeric, Boolean, unmanaged/byref pointer, unconstrained generic, nonzero and mixed-local comparisons are unchanged. Both operand orders and eq/ne are tested.
* An ARM64 System.String.CreateString(Char,Int32) private instance factory with exact null pseudo-this can become public `newobj String::.ctor(Char,Int32)` only if its whole body is the known two W-register argument moves and a direct tail branch to the matching static System.String.Ctor. Signature/identity/access/count/virtual-dispatch guards and a unique public constructor are required. This is not an arbitrary factory rewrite. Serialized CLR tests cover zero, positive and negative counts; malformed patterns remain unchanged.

Castle Busters exact-input independent stages (17,026 audited methods): baseline valid 8,011; null-only valid 8,343; combined valid 8,345. Structural failures 75 and diagnostic strings 52,156 unchanged; zero valid-to-invalid regressions or diagnostic-increase methods.

The callback is now ILVerify-valid but NOT behaviorally verified. An independent native oracle executes actual callback, CreateString/Ctor, Concat and FillStringChecked machine code; only allocation, Buffer.Memmove, exception plumbing and TMP are exact external boundaries. Real CLR String operations in the emitted-IL adapter produce only 60/72 matches: 12 owner-null/negative-count cases disagree in exception order. The existing simplifier postpones field reads across string construction. A rejected snapshot experiment achieved 72/72 but introduced two delegate-verification regressions and diagnostic increases in 93 methods. It is not included in this PR; its diff and evidence are retained in the immutable dataset report. No callback promotion or runtime transplant.

KillDots can be independently case-verified after ILVerify and native-vs-emitted-IL revalidation of its null/inactive/active prior tween behavior. This does not verify actual DOTween internals or lifecycle. All assets and canonical staging remain unchanged; startup remains gated.
