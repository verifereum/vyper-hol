(* Dummy theory that depends on all targets in the project, for building everything *)
Theory vyperHol
Ancestors
  (* syntax, frontend, semantics *)
  jsonToVyper
  vyperTestRunner
  (* semantics properties *)
  vyperEvalPreservesNameTarget
  (* compiler passes *)
  phiFunction
  rtaPassCorrectness
  cfgAnalysis
