signature foldedValueParityAbiPlanLib = sig
  val PLAN_STEP_TAC : Abbrev.tactic
  val PLAN_NORMALIZE_TAC : Abbrev.tactic
  val PLAN_CONTEXT_TAC : int -> Abbrev.tactic
  val PLAN_FUEL_TAC : Abbrev.tactic
  val eval_codegen_call : Term.term -> Abbrev.tactic
  val eval_codegen_until : Term.term -> Term.term list -> Abbrev.tactic
end
