# ARM64/IL2CPP recovery clusters → fixes → regression tests

Every recovery fix merged into `development` since the fork's upstream base
(`b5ad444b`, upstream PR SamboyCoding/Cpp2IL#611) is listed once. For each: the
taxonomy stage it belongs to, the PR/commit that fixed it, and the test(s) that
reproduce it — or `none` with a reason.

Rules for this table: a cluster may only be listed with `none` when it cannot
be reproduced in a unit test (e.g. compile-only fixes). New regression tests
live in `Cpp2IL.Core.Tests/Regression/` and use synthetic instruction bytes or
tiny injected fixtures only — no game binaries, names, tokens or addresses.

| Cluster / PR | Stage | Fix | Reproducing test(s) |
|---|---|---|---|
| #1 castle-busters-il-recovery | runtime helper | e699b7b0 | `GotMetadataTests.ResolvesOnlyTheSecondLoadThroughAKnownGotSlot` |
| #2 castle-busters-il-recovery | IL emission | 136f727d | `Arm64ExtendedAddTests.*`, `IlGeneratorTests.SignedWordExtensionExecutesWithCorrectLowWordAndScale`, `InterfaceCallPreservesRuntimeDispatch`, `InvalidStackRemainsExplicitlyDiagnosedAndBodyIsPreserved` |
| #3 recovery-evidence-sidecar | infra (manifest) | 42f16eed | `RecoveryManifestTests.ManifestIsDeterministicBoundToBytesAndDoesNotRewriteIl` |
| #4 awake-integer-recovery | dataflow | 00460ad1 | `IntegerArithmeticTypeTests.*`, `IlGeneratorTests` additions |
| #5 status-base-recovery | dataflow | 1d663b9b | `StatusBaseRecoveryTests.*`, `IlGeneratorTests.AddressAliasResolvesNegativeDisplacementBackToObjectField` |
| #6 start-dots-recovery | IL emission | 9b0ee460 | `AllocationConstructorTests.*`, `NonReturningHelperTests.*`, `IntegerArithmeticTypeTests.*` |
| #7 tryparse-version-byref | dataflow | 5c6600ff | `ByRefStoreTests.OnlyExactReferenceByrefStoreDereferencesDestination`, `NativeStoreRetainsWidth` |
| #8 killdots-callback-recovery | IL emission | ac81836e | `IlGeneratorTests.OnlyReferenceEqualityWithLiteralZeroEmitsNull`, `StringConstructionTests.ProvenStringFactorySerializesAndExecutesPublicConstructor` |
| #9 trustedtime-events | runtime helper | c3c0e7da | `ReferenceCompareExchangeTests.*` |
| #10 localization-guard-recovery | dataflow | 0def3fd2 | `IntegerArithmeticTypeTests.BooleanNotChainRequiresGuardOnlyUses` |
| #11 recovery-determinism | verifier / infra | 53413d29 | `ThrowHelperDeterminismTests.*`, `RecoveryModuleIdentityTests.*` |
| #12 sol-snapshot-residual | dataflow | b7706c5b | `SimplifierTests.*` |
| #13 sol-delegate-dispatch | runtime helper | fa600a2f | `DelegateInvokeRecoveryTests.*`, `ReferenceCompareExchangeTests.*` |
| #14 sol-exception-byref | runtime helper | b24d9e8f | `InjectedExceptionGuardTests.*` |
| #15 sol-exception-netstandard | compiler (netstandard2.0) | 99855ab0 / 99448877 | none — compile-only API fix (`IReadOnlySet` → `ISet`); no behavior to reproduce |
| #16 pin-patched-disarm | parser | 943ae504 → Disarm `c3cb7167` | `Regression/Arm64DecoderCoverageTests.DecoderResolvesPatchedEncodings` (LD1R, SSHLL cases predate #47 and pin this patch set; unpatched upstream Disarm cannot even compile `Cpp2IL.Core`) |
| #17 luna-arm64-lowering | lifter | d413d7a9 | `Arm64MissingOpsTests.FloatingAndDupWitnessesAreLowered`, `BicKeepsShiftedRegisterOperand` |
| #18 luna-eh-exception-return | IL emission | 735640cc | `IlGeneratorTests.ExceptionValueReturnedFromNonExceptionMethodIsThrown` |
| #19 luna-invalid-p09-int-producer | dataflow | f44f5afb | `IntegerArithmeticTypeTests.IntegerProducerStaysTypedThroughBitwiseConsumer` |
| #20 luna-arm64-lowering-hotfix | lifter | 0e18a40d / 03d8a481 | none — compile-time signature fix (`AddOperands([source])`); the path is exercised by `Arm64LibcMathImportTests.*` (#74) |
| #21 castle-visibility-rootcause | IL emission | 3fc37db6 | `IlGeneratorTests.RecoveredPrivateFieldAccessRelaxesOnlyReferencedMember` |
| #22 luna-numeric-abi | dataflow | 8b321c94 | `IntegerArithmeticTypeTests.BitwiseResultPrefersWideImmediateOverInt32Producer` |
| #23 luna-memory-operand-wave3 | lifter | c0e556cf | `IlGeneratorTests.TypedPointerMemoryLoadUsesThePointerElementType`, `UnknownMemoryLoadRemainsExplicitlyUnresolved` |
| #24 luna-ctor-delegate-wave3 | IL emission | 9c7ad0e7 | `AllocationConstructorTests.ConstructorCallBeforeAllocationIsFusedForTheSameLocal` et al. |
| #25 luna-ctor-delegate-wave3 | CFG | f656556c | `AllocationConstructorTests.BranchTargetingFusedConstructorCallRemainsAddressable` |
| #26 luna-aapcs64-hfa-wave3b | IL emission | 01fcac8d | none — reverted by #27 (737b64d5); no live fix to reproduce |
| #27 revert of #26 | — | 786f6396 | `IntegerArithmeticTypeTests.*`, `IlGeneratorTests.*` (HFA tests removed with the revert) |
| #28 integer-producer-wave5 | dataflow | d432901f | `IntegerArithmeticTypeTests.ProvenIntegerArithmeticStaysTypedWhenAlsoUsedAsAddress` |
| #29 arm64-w-width-wave6 | lifter | efc80396 | `IntegerArithmeticTypeTests.*`, `Arm64MissingOpsTests.*` |
| #30 null-literal comparison | IL emission | 24d3b50a | `IlGeneratorTests.OnlyReferenceEqualityWithLiteralZeroEmitsNull` (extended with new cases) |
| #31 type-token runtime representation | IL emission | a54aec7c | `IlGeneratorTests.TypeTokenMatchesExpectedRuntimeRepresentation` |
| #32 runtime-class operand | IL emission | 70d6a353 | `IlGeneratorTests.TypeTokenMatchesExpectedRuntimeRepresentation` (`"runtime-class"` case) |
| #33 masked-boolean/array recovery | IL emission | bc08efd7 | `IlGeneratorTests.BooleanNotCanFlowThroughMaskedBooleanToKnownResult`, `LateArrayRecoveryTypesLengthAndIndex`, `UntypedLocalZeroUsesItsEmittedObjectContract` |
| #34 untyped boolean temporaries | IL emission | b15cb281 | `IlGeneratorTests.UntypedBooleanNotResultUsesBooleanLocal` |
| #35 boolean-local inference | IL emission | fba7ef0b | `IlGeneratorTests.UntypedBooleanNotResultUsesBooleanLocal` (strengthened) |
| #36 native pointer immediates | IL emission | 6d4aaaae | `IlGeneratorTests.NativePointerImmediateEmitsConversion`, `AddressInstructionsRetainPointerWidth`, `Arm64MissingOpsTests.*` |
| #37 inlined ancestor ctor re-anchor | IL emission | 7faede78 | `AllocationConstructorTests.Distant*Constructor*` (5 tests) |
| #38 object-address alias folding | dataflow | 96f704ae / 95fb169d | `Regression/AddressAliasRecoveryTests.ArrayLengthLoadThroughAddressAlias`, `TypedAddressAliasStillFoldsToField`, `IndexedArrayLoadThroughAddressAlias` (indexed shape is additionally resolved by `ArrayRecovery` itself, so it does not isolate the fix alone) |
| #39 literal widening/narrowing | IL emission | 3235b4be | `IlGeneratorTests.LongDestinationReceivesWidenedSmallLiteral` et al. (6 tests) |
| #40 handle-typed destinations + ldftn off .ctor | IL emission | b3c7aeb9 / 5b117115 | `Regression/RuntimeHandleEmissionTests.ConstructorMethodInfoDoesNotEmitLdftn`, `HandleTypedLocalReportsIntPtrContract` |
| #41 shared-generic newobj retarget | IL emission | 6d877491 / fcd1aaac | `Regression/SharedGenericNewobjTests.FusedNewobjRetargetsConstructorToDestinationInstantiation` |
| #42 missing/hidden generic args | IL emission | 8fa504d5 | `IlGeneratorTests.MissingStructArgumentEmitsParameterlessConstructor` et al. |
| #43 struct argument defaults | IL emission | edd435e2 | `IlGeneratorTests.ImmediateInStructArgumentSlotEmitsDefaultOfStruct` |
| #44 abstract/erased ctor & delegate sharpening | IL emission | fb7fe93e | `AllocationConstructorTests.*`, `DelegateConstructorTests.*` (14 tests) |
| #45 shifted logical lowering | lifter | 8c994d7a | `Arm64ShiftedLogicalTests.*`, `Arm64MissingOpsTests.*` |
| #46 local lifetimes / aggregate lanes | dataflow | b59f1343 | `LocalLifetimeSplitTests.*` |
| #47 Disarm decoder bump | parser | d373110e → Disarm `e872281d` | `Regression/Arm64DecoderCoverageTests.DecoderResolvesPatchedEncodings` (SSHR, ADDV, TBL, ST1, CAS, LDADDB cases) |
| #48 managed memory recovery | dataflow | 73276a17 | `ManagedMemoryRecoveryTests.*` |
| #49 SIMD scalarizer | lifter | 8a751e57 | `Arm64VectorScalarizerTests.*`, `Arm64SimdSemanticFixtureTests.*`, `Arm64MissingOpsTests.*` |
| #50 runtime JIT oracle | verifier / infra | a38eefa8 | `Cpp2IL.JitOracle.Tests/OracleTests.*` |
| #51 helper veneer discovery | runtime helper | 5cd172ec | `Arm64VeneerAliasTests.*` |
| #52 numeric bitcasts | IL emission | f0f685e4 | `FloatCarrierIntegerOperationTests.*` |
| #53 rgctx generics / field layout | dataflow | e65f2ebb | `GenericInstanceFieldLayoutTests.*`, `InaccessibleFieldAccessorTests.*`, `RgctxResolverTests.*`, `WriteBarrierStoreTests.*` |
| #54 managed dispatch | runtime helper | fc37e743 | `DelegateInvokeRecoveryTests.*`, `ManagedDispatchRecoveryTests.*` |
| #55 isinst element class | runtime helper | 4a78199c | `KeyFunctionRecoveryTests.IsInstArrayElementClassBecomesManagedReferenceCast` |
| #56 signed-word extension | lifter / IL emission | 899463f1 | `IlGeneratorTests.SignedWordExtensionExecutesWithCorrectLowWordAndScale` (strengthened: MaxStack assert) |
| #57 shared-generic result contract | IL emission | 4654985e / 69b7bc0c | `Regression/SharedGenericResultContractTests.ErasedGenericCallResultDoesNotFabricateInt32Instantiation` |
| #58 type tokens into native handle slots | IL emission | fff27d63 / 4bc19667 | `Regression/TypeTokenContractTests.BareTypeOperandIntoIntPtrSlotEmitsRealToken` |
| #59 isinst tail | runtime helper | eb26cb80 | `KeyFunctionRecoveryTests.IsInstArrayObjectClassBecomesManagedReferenceCast` |
| #60 isinst operands | runtime helper | 390629dc | `KeyFunctionRecoveryTests.IsInstRuntimeClassBecomesCastToRepresentedType` |
| #61 resolved field type over width guess | dataflow | 5d97b373 | `IntegerArithmeticTypeTests.ResolvedFieldLoadOverridesNativeWidthGuessWithoutEquivalentTypeChurn` |
| #62 runtime element class loads | runtime helper | e9613628 | `KeyFunctionRecoveryTests.ArrayElementClassLoadBecomesRuntimeClassOperand` |
| #63 runtime element class (general) | runtime helper | a305db98 | `KeyFunctionRecoveryTests.OrdinaryClassElementLoadPreservesRepresentedType` |
| #64 generic interface dispatch | runtime helper | 13d99117 | `ManagedDispatchRecoveryTests.GenericVirtualHelperDispatchResolvesConcreteInterfaceMethod` |
| #65 isinst null semantics | semantic mismatch | 65830fb0 | `KeyFunctionRecoveryTests.NullReturningReferenceCastEmitsIsInst` |
| #66 inlined class isinst | runtime helper | 40e85347 | `KeyFunctionRecoveryTests.InlinedClassHierarchyCheckBecomesNullableIsInst` |
| #67 isinst depth guard | runtime helper | aaa1e4ed | `KeyFunctionRecoveryTests.InlinedClassHierarchyCheckBecomesNullableIsInst` (depth-guard asserts added) |
| #68 interface lookup cleanup | runtime helper | 20642f1a | `ManagedDispatchRecoveryTests.InterfaceDispatchExcisesLookupAfterDeadCopyChain` |
| #69 arm64 scalar math | lifter | 7081d064 | `Arm64MissingOpsTests.*`, `IntegerArithmeticTypeTests.*` |
| #70 vector scalar literals | lifter | febe5fbb | `IlGeneratorTests.ScalarViewOfVectorLiteralKeepsLowLaneBits` |
| #71 arm64 scalar min/max | lifter | 70713882 | `Arm64MissingOpsTests.ScalarMaximumNumberLowersToMathCall` |
| #72 unused this warning | dataflow | 6f57da7e | `LocalVariablesTests.UnusedThisParameterDoesNotProduceWarning` |
| #73 ELF end-catch veneers | runtime helper | a3a4f683 | `KeyFunctionRecoveryTests.NativeEndCatchBookkeepingIsRemoved` |
| #74 libc math imports | lifter | 10103e80 | `Arm64LibcMathImportTests.*` (14 tests) |
| #75 native exception throw | runtime helper | 5abb44f1 | `KeyFunctionRecoveryTests.NativeExceptionWrapperThrowBecomesManagedThrow` et al. |
| #76 interface slow lookup / folded slots | runtime helper | 3a244dda | `ManagedDispatchRecoveryTests.FoldedSlot*` et al. (9 tests) |
| #77 ELF block memory | lifter | 372d774c | `BlockMemoryImportRecoveryTests.*` (14 tests) |
| #78 SIMD leftovers | lifter | 22df1563 | `Arm64SimdLeftoverOpsTests.*` (14 tests) |
| #79 indirect tail calls | CFG | 13dc27d6 | `TailCallRecoveryTests.*` (14 tests) |
| #81 lazy RGCTX guards | CFG | 4fa07049 | `MetadataInitGuardRemoverTests.RgctxGuard*` (8 tests) |
| #82 chained RGCTX guards | CFG | 825f8854 | `MetadataInitGuardRemoverTests.RgctxGuardWhoseArmIsAnotherRgctxGuardIsExcised` et al. |
| #83 runtime-class boxing | semantic mismatch | 0ec7a757 | `KeyFunctionRecoveryTests.BoxRuntimeClassUsesRepresentedValueType` |
| #84 Castle recovery baseline (roll-up) | all | d0d6c32f | full `Cpp2IL.Core.Tests` + `Cpp2IL.JitOracle.Tests` baseline suites |
| #85 CI workflow (`fork-tests`) | infra | c9a30c51 | none — CI plumbing only, not a recovery fix |
| #88 `type-absent-from-recovered-metadata` (compile bucket) | metadata emission | `FrameworkSurfaceTypes.EmitMissing` materializes TypeDefs for framework types referenced only via implflags/attribute surfaces | `Regression/FrameworkSurfaceTypesTests.FlagSurfacesMaterializeMissingCorlibTypeDefs`, `InjectedImplFlagsMaterializeMethodImplSurface` |
| castle-recovery#53 stray `NestedClass` row | metadata emission | c9ede488 | `Regression/NestedClassTableTests.EmittedNestedClassRowsAreInRangeAndUnique`, `NestedTypeListedUnderAnotherParentIsEmittedOnlyUnderItsDeclaringType` |
| #90 `invalid-attribute-named-argument` (compile bucket) | metadata emission | `AsmResolverAssemblyPopulator` restores the accessor il2cpp stripped on setter-only named-argument properties via their `<Name>k__BackingField` | `Regression/AttributeNamedArgumentTests.NamedArgumentSetOnlyPropertyGetsGetterBack`, `SetOnlyPropertyWithoutBackingFieldStaysAsIs` |
| #91 `override-accessibility-mismatch` (compile bucket, castle-recovery#62) | metadata emission | `MemberAccessibility` now normalizes a method's whole override chain (ancestors + all overriders) instead of widening single members, so emitted flags satisfy C#'s override-access rule (CS0507); populate-time pass keeps unreferenced roots at declared access | `Regression/OverrideChainAccessibilityTests.*` (7 tests) |
| castle-recovery#70 `missing-reference-assembly` (compile bucket) | metadata emission | `AssemblyReferenceClosure.Ensure` sweeps attribute-blob type arguments and declares every emitted assembly they name (`TokenAllocator` token so serialization emits a real AssemblyRef row); `DoOutput` builds PE images with `PreserveAssemblyReferenceIndices` | `Regression/AssemblyReferenceClosureTests.BlobOnlyForeignTypeArgumentsDeclareTheirAssembly` |
| castle-recovery#76 `lifter:no-evidence` on emitted-but-never-lifted members (compile `missing`) | infra (manifest) | `RecoveryManifest.Inspect` records an explicit `injected-stub` row (null address/sha) for emitted methods with no lifter evidence — bare-allocation ctors, restored attribute accessors, framework-surface/string-blob helpers — instead of `Native: null` | `Regression/SynthesizedMemberEvidenceTests.NestedTypeMethodWithoutLiftEvidenceGetsExplicitReasonRow` |
| castle-recovery#74 `il2cpp_vm_object_unbox` helper call | runtime helper | 3f305d68 — `KeyFunctionRecovery` lifts the call to a new `OpCode.Unbox` (`[result, value type, object]`, emitted as `unbox` → `&T`); the value type comes from the class operand when it resolves and is not a stale copy of the object, else from the wrapper's inlined `element_class` check guarding the call; unresolvable sites keep an explicit diagnostic | `Regression/UnboxEmissionTests.UnboxCallWithResolvedValueTypeEmitsUnbox`, `UnboxCallWithoutResolvableTypeKeepsExplicitDiagnostic` |

## Summary

- **84 fork PRs** merged since `b5ad444b` (#1–#79, #81–#85; no #80).
- **2 are not live recovery fixes**: #26 (reverted by #27) and #85 (CI only).
- **82 recovery-fix clusters.** Before this change, **73** carried reproducing
  tests (tests added or strengthened in the same PR). **7 gained tests here**:
  #16 + #47 (the new decoder test, 8 cases), #38 (3 tests), #40 (2), #41 (1),
  #57 (1), #58 (1).
- **2 remain `none`**, both compile-only fixes: #15 (`IReadOnlySet` on
  netstandard2.0) and #20 (`AddOperands` signature fix, exercised downstream by
  `Arm64LibcMathImportTests`).

## Open clusters (pinned)

Minimal synthetic fixtures for the three largest open r241 clusters whose root
cause is in Cpp2IL recovery or lifting (`decompiler-issue:*` clusters are
excluded by the taxonomy). Counts are baseline method counts from
`baselines/r241/codeverify-summary.json.gz` and `baselines/r241/ilverify/`. Each
test asserts the explicit diagnostic the pipeline emits today; the assertion is
expected to flip when the cluster is fixed.

| Cluster | r241 methods | Pinning test | Suspected root cause |
|---|---|---|---|
| `stub:intentional-stub` | 99,048 | `OpenClusterPinningTests.FrameworkModuleMethodIsMarkedIntentionalStub` | The emitted-module name gate (`UnityEngine.`/`Unity.`/`System`/`mscorlib`) in `AsmResolverDllOutputFormatIlRecovery.FillRecoveryBody` marks every managed framework method an intentional stub before recovery evidence is consulted. |
| `ilverify:StackUnexpected` | 885 | `OpenClusterPinningTests.ReturnValueDroppedByVoidSignatureLeavesStackInvalidDiagnosed` | Emitted bodies whose eval-stack contract the verifier rejects (e.g. a recovered return value under a void signature leaves an unpopped value at `ret`); today they are only marked by the "Invalid reconstructed IL stack" diagnostic. |
| `stub:injected-stub` | 732 | `OpenClusterPinningTests.InjectedMethodIsMarkedInjectedStub` | `InjectedMethodAnalysisContext` members always take the minimal-stub path in `FillRecoveryBody`; nothing separates injectable scaffolding from methods a real body could be recovered for. |

Larger open clusters deliberately not pinned:

- `stub-shape:default-return-candidate` (54,742), `stub-shape:no-op-candidate`
  (30,399), `stub-shape:throw-null-placeholder` (1,528): shape heuristics over
  the same emitted bodies — they overlap `stub:intentional-stub` /
  `stub:injected-stub` rather than being an independent recovery or lifting
  root cause.
- `ilverify:partial-no-managed-body` (7,714): abstract, extern and runtime
  methods are legitimately bodiless — root cause outside Cpp2IL recovery.
- `ilverify:partial-verifier-failure` (2,389): umbrella over verifier crashes;
  its dominant member is `ilverify:NullReferenceException`.
- `ilverify:NullReferenceException` (2,376): already fixed on `development` —
  re-verifying the assemblies rebuilt from `development` produces zero
  `NullReferenceException` verifier crashes. The residual 13
  `ilverify:FileNotFoundException` crashes are the verifier failing to resolve
  the injected `CastleRecovery.Runtime` helper assembly.
- `ilverify:ReturnPtrToStack` (379): emits stack-valid (`ldloca`/`ret`) bodies
  with no Cpp2IL-side diagnostic to assert; smaller than the pinned stub
  cluster. Next in line if a third `ilverify` pin is wanted.
