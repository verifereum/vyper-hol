(* Hand-written tests of the Vyper semantics, frontend and test runner, as one
   build root. Generated replay theories and the coverage report have
   separate CI jobs. *)
Theory vyperTestsHol
Ancestors
  e2eSourceBoundaryCVTest
  vyperConstEvalWitness
  livenessProofIntegrity
  vyperAccountCodehashTest
  vyperAssignmentOrderAudit
  vyperBytesAddressConvertTest
  vyperBytesDecimalConvertTest
  vyperCallOutcomeTest
  vyperCalldataLenTest
  vyperCalldataSliceTest
  vyperCheckContractFrontendLibTest
  vyperCheckContractLibTest
  rawReturnDeclarationTest
  vyperCheckContractTraceLibTest
  vyperCreateSelfdestruct
  vyperCreateStorageTest
  vyperCustomErrorTest
  vyperDecimalConvertTest
  vyperDecimalMulAudit
  vyperDecimalMulTest
  vyperDelegateRawCallTest
  vyperECPrecompileTest
  vyperEventFixtureTest
  vyperEventRegression
  vyperExtCallConsumptionTest
  vyperExtCallCpsCVKernelCheck
  vyperExtCallCpsCVTest
  vyperExtCallCpsEquivalenceTest
  vyperExtCallModesTest
  vyperFixedBytesConvertTest
  vyperForStorageReadsTest
  vyperInStaticArrayTest
  vyperInvertTest
  vyperLoadTimingTest
  vyperMembershipSemanticsTest
  vyperOracleEntryTest
  vyperOracleIntegrationTest
  vyperOracleStateTest
  vyperPopReceiverTest
  vyperRawCallCalldataTest
  vyperSendCpsCVTest
  vyperSendModesTest
  vyperStorageOutcomeTest
  vyperStoragePopTest
  vyperStringScopeTest
  vyperTestEmit
  vyperTestEmitSmoke
  vyperTestLibTest
  vyperTestRunner
  vyperTupleSubscriptTest
  vyperTypeCallOutcomeTest
  vyperUnreachableTest
  vyperUnsafeDivTest
  vyperASTSyntaxTest
  (* creation builtins and constructors *)
  vyperCreateOracleTest createOracleResultTest createSourceSizeBoundaryTest
  vyperCreateTypingTest vyperCtorStorageAliasTest createSemanticAudit
  (* external entries: initial oracle state, defaults, headers, behavior *)
  vyperOracleInitialStateTest vyperExternalDefaultsTest vyperExternalHeadersTest
  vyperExternalEntryBehavior vyperExternalEntrySourceBehavior
  (* places *)
  vyperPlaceProbesTest vyperPlaceSanityTest
  (* events declared in imported modules *)
  vyperImportedEventRegression
  (* typing of raw/system builtins, pop receivers and argument writes *)
  vyperRawSystemTypingTest vyperPopTypingTest vyperArgWriteTypingTest
  (* ABI decode typing, constructor ABI domain *)
  abiDecodeTypingTest ctorAbiDomainWitness
