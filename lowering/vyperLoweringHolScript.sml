(* Rollup theory for Vyper->Venom lowering + e2e correctness *)
Theory vyperLoweringHol
Ancestors
  (* definitions *)
  moduleLowering
  (* property statements and proofs *)
  moduleLoweringProps entryDispatchProps entryDecodeProps
  loweringSlice
  varsExt exprSim
  exprBopLowering
  exprSimOps exprSimCompare exprSimArith intBits freshWrites
  exprSimMain
  valueEncodingProofs
  localPtrsProps
  loweringShapeProps
  structFieldsProps
  (* compiler + correctness *)
  vyperCompiler
  allocaBudgetChecks
  vyperLoweringCorrect
  configuredE2ECorrectness
  (* focused internal-frame allocation, cleanup and whitelist regressions *)
  calleeMemoryWitness
  cleanupPromiseWitness
  internalFrameWhitelistDiagnostic
