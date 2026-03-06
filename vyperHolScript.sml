(* Dummy theory that depends on all targets in the project, for building everything *)
Theory vyperHol
Ancestors
  (* syntax, frontend, semantics *)
  jsonToVyper
  vyperTestRunner
  (* semantics properties *)
  vyperEvalPreservesNameTarget
  (* venom module execution (INVOKE / cross-function calls) *)
  venomModuleSem
  (* compiler passes *)
  venomPassesHol
  (* analysis roll-up *)
  venomAnalysisHol
