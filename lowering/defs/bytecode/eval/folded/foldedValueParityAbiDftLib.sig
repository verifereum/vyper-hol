signature foldedValueParityAbiDftLib = sig
  val dominance_compset : computeLib.compset
  val relink_rules : bool -> Term.term list -> computeLib.compset -> computeLib.compset
  val planner_beta_conv : Abbrev.conv
  val head_beta_conv : Abbrev.conv
  val finite_eval : Abbrev.conv
  val eval_finite_call : Term.term -> Abbrev.tactic
  val eval_call_until : Term.term -> Term.term list -> Abbrev.tactic
  val OFFSPRING_OPEN_TAC : Abbrev.tactic
  val OFFSPRING_STEP_TAC : Abbrev.tactic
  val DFT_STEP_TAC : Abbrev.tactic
  val DFT_BLOCK_TAC : Abbrev.tactic
  val EXEC_PASS_TAC : Abbrev.tactic
  val PASS_RESULT_TAC : Abbrev.tactic
  val DFT_GRAPH_TAC : Abbrev.tactic
  val DFT_FINISH_TAC : Abbrev.tactic
  val DFS_CONTEXT_TAC : Abbrev.tactic
  val DFS_CHUNK_TAC : Abbrev.tactic
  val DFS_NORMALIZE_TAC : Abbrev.tactic
  val DFS_FINISH_TAC : Abbrev.tactic
  val READY_OPEN_TAC : Abbrev.tactic
  val DOM_SUBGOAL_TAC : Abbrev.tactic
  val EVERY_GOALS_TAC : Abbrev.tactic
  val ABBREV_EVERY_TAC : Abbrev.tactic
  val DOM_EVAL_TAC : Abbrev.tactic
  val DOM_BRANCH_TAC : Abbrev.tactic
end
