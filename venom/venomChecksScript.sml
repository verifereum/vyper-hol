(* Concrete checks of Venom execution, the passes and codegen, as one build
   root: regressions of observed bugs and interface checks on small
   programs. The results they check are in vyperHol. *)
Theory venomChecks
Ancestors
  (* codegen: call activation, frames, encoding, oracles, function boundaries *)
  asmCallActivationRegression contextReachabilityChecks asmEncodingRegression
  codegenFrameChecks codegenOracleRegression fnBoundaryRegression
  sourceMemoryRangeChecks
  (* the compiler's unit-shape and unit-transform hypotheses *)
  unitShapeChecks unitTransformChecks
  (* passes: call-frame allocation, effect order in the dead-function walk *)
  concretizeCallFrameRegression dftEffectOrderTest
  (* execution of INVOKE with no arguments and of STOP after a call *)
  invokeEmptyArgs stopReturndata
