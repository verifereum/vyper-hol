Theory loweringBudgetResidualArithmetic
Ancestors
  loweringBudgetRecorderOutcomes loweringCallBudgetHistory list

Theorem lower_budget_path_nonempty_outcomes_count:
  !checked D lo explicit ctx p h marks q.
    lower_budget_path checked (D,lo,explicit,ctx) p h marks q /\
    q.bp_state.vs_outcomes <> [] ==>
    lower_history_count h < LENGTH p.bp_state.vs_outcomes
Proof
  rpt strip_tac >>
  drule lower_budget_path_outcomes >> strip_tac >>
  gvs[DROP_EQ_NIL]
QED
