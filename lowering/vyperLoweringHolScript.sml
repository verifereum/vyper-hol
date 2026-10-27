(* Rollup theory for Vyper->Venom lowering + e2e correctness *)
Theory vyperLoweringHol
Ancestors
  (* definitions *)
  moduleLowering
  (* property statements and proofs *)
  moduleLoweringProps entryDispatchProps entryDecodeProps
  abiDecodeStaticProps entryDecodeStaticProps entryDecodePlanProps
  loweringSlice
  varsExt exprSim
  exprBopLowering
  exprSimOps exprSimCompare exprSimArith intBits freshWrites
  exprSimMain stmtSim stmtSimIf stmtSimFor stmtSimReturn stmtSimDecl
  stmtSimReason
  valueEncodingProofs
  localPtrsProps
  immutableStagingBridge
  immutableCodeLayout
  immutableLocationProps
  loweringShapeDefs
  loweringShapeProps
  intCallStep intCallLookup intCallCallee
  structFieldsProps
  (* compiler + correctness *)
  vyperCompiler
  allocaBudgetChecks
  vyperLoweringCorrect
  configuredE2ECorrectness
  evalCompilerMemoryStores
  evalCompilerImmutables
  evalCompilerExternalCalls
  evalCompilerNameCollisions
  evalCompilerInternalLabels
  evalCompilerSliceBuffers
  evalCompilerPhiPointers
  evalCompilerInternalFrames
  evalCompilerInternalImmutables
  (* focused internal-frame allocation, cleanup and whitelist regressions *)
  calleeMemoryWitness
  cleanupPromiseWitness
  internalFrameWhitelistDiagnostic
  evalCompilerAllocationLimit
