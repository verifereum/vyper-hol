(* Hand-written tests of the Vyper semantics, frontend and test runner, as one
   build root. Generated replay theories and the coverage report have
   separate CI jobs. *)
Theory vyperTestsHol
Ancestors
  e2eSourceBoundaryCVTest
  jsonConstEvalWitness
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
