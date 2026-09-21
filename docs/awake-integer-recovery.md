# Integer comparison temporaries and I4 call constants

Two independent, general recovery defects made Castle Busters 1.11.1
`Bootstrap.Awake` fail ILVerify despite having no decompiler diagnostics:

* `cmp w19, #1` became a subtract temporary followed by equality, but integer
  arithmetic did not propagate a result type. The temporary serialized as object.
* `mov w0, #-1` was represented as the unsigned low word 4294967295. The IL
  generator chose `ldc.i8` even for an explicitly Int32 call argument.

The fix types integer arithmetic results only when **all uses are direct
comparisons**. Operands must have the same normalized I4/I8 type, or be a
compatible immediate; references, pointers, mixed widths and oversized I4
immediates remain unresolved. The original float inference is unchanged.
I4 argument literals in the signed-I4/unsigned-I4 range are emitted with their
exact low-word bit pattern, but only for an explicit Int32/UInt32 expected type.

A broader arithmetic inference was rejected: two previously unresolved pointer
locals acquired Int32 too early in the monotonic metadata fixpoint. The final
comparison-only scope does not change any diagnostic categories/counts.

## Validation

* Initial regression: five failing cases before the fix.
* Final core suite: 104 passed, including Int32 and UInt32 -1/0xffffffff,
  0x80000000, I8 preservation, oversized literals, mixed types and address use.
* LibCpp2IL suite: 5 passed. All four Core target frameworks build.
* Exact-input recovery: 70,310 emitted methods; audited game subset 17,026.
* Official ILVerify valid: 6,739 -> 6,814; invalid: 10,033 -> 9,958.
  No previously valid method becomes invalid. Structural failures remain 217;
  diagnostics remain 63,345. Ten existing stack diagnostics merely move their
  reported IL offset from 0x135 to 0x131 because ldc.i4 is shorter than ldc.i8.
* Awake: three ILVerify errors -> zero; MaxStack 2, zero diagnostics.
* Actual 248-byte A64 function executed in Unicorn 2.1.4 and compared with the
  actual emitted CIL body: 24/24 warm initialized-path boundary-contract cases.
  Vibration returns false/true; prefs returns Int32 min/-1/0/1/2/max; each repeated
  twice. This does **not** establish cold initialization or engine equivalence.

Binary SHA256: `a2f8b8416e243e7d7f1423d2d638801f4ca03241aa3b1f85633b2b59f3fd0581`.
Metadata SHA256: `412a4ac68e773822fb232f5e6a29c7b498a0b90731bacc6169b6113a07f7cc79`.
Unity 6000.0.72f1, metadata31.1, Android AAPCS64. Awake native VA 0x3c7d9f4,
raw offset 0x3c799f4, length248, SHA256
`94c1921090bc8e66fb5dd4b4077a56cc44471acc913238e26147f558cfbf478c`.
Injected RVA is the raw offset, not the native virtual address.

The user's local evidence package is `recovery/1.11.1/awake-integer-recovery-20260921`
in the Castle Busters history dataset. Raw game artifacts are not published here.
Startup remains blocked (one case-verified method, 29 blocked of 30 reachable;
44 unresolved targets). No runtime DLLs or assets were replaced, and no standalone
boot claim is made.
