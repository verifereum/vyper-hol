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
  exprSimOps exprSimCompare exprSimArith intBits freshWrites
  exprSimMain stmtSim stmtSimIf stmtSimFor stmtSimReturn stmtSimDecl
  stmtSimReason stmtSimReasonExpr stmtSimForRange
  valueEncodingProofs
  localPtrsProps
  loweringShapeProps
  intCallStep intCallLookup intCallCallee
  structFieldsProps
  (* compiler + correctness *)
  vyperCompiler
  allocaBudgetChecks
  vyperLoweringCorrect
  configuredE2ECorrectness
  evalCompilerMemoryStores
  evalCompilerExternalCalls
  evalCompilerNameCollisions
  evalCompilerCtorLocals
  evalCompilerInternalLabels
  evalCompilerSliceBuffers
  evalCompilerPhiPointers
  evalCompilerInternalFrames
  (* focused internal-frame allocation, cleanup and whitelist regressions *)
  calleeMemoryWitness
  cleanupPromiseWitness
  internalFrameWhitelistDiagnostic
  evalCompilerAllocationLimit
