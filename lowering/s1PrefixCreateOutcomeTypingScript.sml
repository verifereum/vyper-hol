Theory s1PrefixCreateOutcomeTyping
Ancestors
  exprSimHypsDefs vyperCallOutcome vyperRuntimeAccounts

Theorem expr_sim_inv_outcomes:
  expr_sim_inv cenv cx env es ==>
  outcomes_accounts_typed es.outcomes /\ IS_SOME es.outcomes
Proof
  simp[expr_sim_inv_def]
QED

Theorem expr_sim_inv_accounts_well_typed:
  expr_sim_inv cenv cx env es ==> accounts_well_typed es.accounts
Proof
  simp[expr_sim_inv_def]
QED
