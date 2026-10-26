(* Rollup theory for Vyper->Venom lowering + e2e correctness *)
Theory vyperLoweringHol
Ancestors
  (* definitions *)
  moduleLowering
  (* property statements and proofs *)
  moduleLoweringProps entryDispatchProps
  loweringSlice
  varsExt exprSim
  exprBopLowering
  exprSimOps exprSimCompare exprSimArith intBits freshWrites
  exprSimMain stmtSim stmtSimReturn
  valueEncodingProofs
  localPtrsProps
  loweringShapeProps
  (* compiler + correctness *)
  vyperCompiler
  vyperLoweringCorrect
  configuredE2ECorrectness
  evalCompilerMemoryStores
  evalCompilerExternalCalls
  evalCompilerNameCollisions
  evalCompilerInternalLabels
  evalCompilerSliceBuffers
  evalCompilerPhiPointers
  evalCompilerAllocationLimit
