(* Rollup theory for Vyper->Venom lowering + e2e correctness *)
Theory vyperLoweringHol
Ancestors
  (* definitions *)
  moduleLowering
  (* property statements and proofs *)
  moduleLoweringProps
  loweringSlice
  varsExt exprSim
  valueEncodingProofs
  localPtrsProps
  loweringShapeProps
  s2LabelClashWitness
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
