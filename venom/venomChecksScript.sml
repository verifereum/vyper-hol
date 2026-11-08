(* Concrete checks of Venom execution, the passes and codegen, as one build
   root: regressions of observed bugs and interface checks on small
   programs. The results they check are in vyperHol. *)
Theory venomChecks
Ancestors
  (* codegen: call activation, frames, encoding, oracles, function boundaries *)
  codegenFrameChecks codegenOracleRegression contextReachabilityChecks
  asmEncodingRegression fnBoundaryRegression sourceMemoryRangeChecks
  fnBlockPlanStaticNopWitness fnBlockPlanStaticRetWitness
  (* internal-frame allocation, cleanup and join-spill regressions *)
  calleeMemoryWitness cleanupPromiseWitness joinSpillWitness
  (* the compiler's unit-shape and unit-transform hypotheses *)
  unitShapeChecks unitTransformChecks
  (* passes: effect and abort order in DFT, alloca remapping, FMP aliasing,
     gas reads with duplicate labels *)
  dftEffectOrderTest dftAbortOrderTest allocaRemapRegression fmpAliasProbe
  dftGasFromListDuplicateLabelOracle
  (* execution of INVOKE with no arguments and of STOP after a call *)
  invokeEmptyArgs stopReturndata
