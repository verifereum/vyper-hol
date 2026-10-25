(* Rollup theory for Vyper->Venom lowering + e2e correctness *)
Theory vyperLoweringHol
Ancestors
  (* definitions *)
  moduleLowering
  (* property statements and proofs *)
  moduleLoweringProps
  valueEncodingProofs
  localPtrsProps
  immutableStagingBridge
  immutableCodeLayout
  immutableLocationProps
  (* compiler + correctness *)
  vyperCompiler
  vyperLoweringCorrect
  configuredE2ECorrectness
  evalCompilerMemoryStores
  evalCompilerImmutables
  evalCompilerExternalCalls
  evalCompilerNameCollisions
  evalCompilerSliceBuffers
