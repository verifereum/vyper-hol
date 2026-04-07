(* Dummy theory that depends on all targets in the project, for building everything *)
Theory vyperHol
Ancestors
  (* syntax, frontend, semantics *)
  jsonToVyper
  vyperTestRunner
  (* semantics properties *)
  vyperSemanticsHol
  (* compiler passes *)
  venomPassesHol
  (* analysis roll-up *)
  venomAnalysisHol
  (* pipeline + codegen *)
  venomPipelineCorrect
  (* lowering + e2e *)
  vyperLoweringHol
  (* codegen *)
  venomToAsmProps asmToBytecodeProps codegenCorrectness
