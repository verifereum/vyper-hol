(* Dummy theory that depends on all targets in the project, for building everything *)
Theory vyperHol
Ancestors
  (* syntax, frontend, semantics *)
  jsonToVyper
  vyperTestRunner
  (* semantics properties *)
  vyperEvalPreservesNameTarget
  (* compiler passes *)
  (* TODO: Make these tree-like instead of flat. Each API-defining directory
  * should have its own roll-up theory (e.g. venomAnalysisHol bundles
  * cfg/fcg/liveness etc, venomHol bundles venomAnalysisHol + passes, then
  * this file just lists top-level roll-ups). *)
  phiFunction
  rtaPassCorrectness
  cfgAnalysis
  fcgAnalysis
  livenessAnalysis
