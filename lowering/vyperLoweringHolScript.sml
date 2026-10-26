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
  allocaBudgetProps allocaFrontierWitness
  vyperLoweringCorrect
  configuredE2ECorrectness
  evalCompilerMemoryStores
  evalCompilerExternalCalls
  evalCompilerNameCollisions
  evalCompilerInternalLabels
  evalCompilerSliceBuffers
  evalCompilerPhiPointers
  evalCompilerInternalFrames
  (* focused internal-frame allocation, cleanup and whitelist regressions *)
  calleeMemoryWitness
  cleanupPromiseWitness
  internalFrameWhitelistDiagnostic
  evalCompilerAllocationLimit
