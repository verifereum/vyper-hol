(* Rollup theory for Vyper->Venom lowering + e2e correctness *)
Theory vyperLoweringHol
Ancestors
  (* definitions *)
  moduleLowering
  (* property statements and proofs *)
  moduleLoweringProps entryDispatchProps entryDecodeProps
  abiDecodeStaticProps entryDecodeStaticProps entryDecodePlanProps
  entryChecksProps
  entryStateRel
  loweringSlice
  varsExt exprSim
  exprBopLowering
  exprSimOps exprSimOperands exprSimCompare exprSimArith intBits freshWrites
  exprSimMain stmtSim stmtSimIf stmtSimFor stmtSimReturn stmtSimDecl
  stmtSimReason stmtSimReasonExpr stmtSimReasonStorage stmtSimForRange
  stmtSimDeclMem exprSimStorageCopy
  valueEncodingProofs
  localPtrsProps
  immutableStagingBridge
  immutableCodeLayout
  immutableLocationProps
  loweringShapeDefs
  loweringShapeProps
  intCallStep extCallOracleStep intCallLookup intCallCallee intCallArgs intCallResult intCallReturnMem intCallFrame intCallReturn valueCopy
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
  evalAssignmentOrder
  (* focused internal-frame allocation, cleanup and whitelist regressions *)
  calleeMemoryWitness
  cleanupPromiseWitness
  internalFrameWhitelistDiagnostic
