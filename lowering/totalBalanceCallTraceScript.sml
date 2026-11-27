(* Aggregate balance bound for every source-call oracle outcome. *)
Theory totalBalanceCallTrace
Ancestors
  e2eDefs callTrace frameOutcome vfmTotalBalance vfmWfState

Theorem outcome_of_total_balance_bounded[local]:
  wf_state s /\ balance_bounded (2 ** 256 - 1) s ==>
  total_balance (outcome_of k s n m).co_accounts <= 2 ** 256 - 1
Proof
  strip_tac >>
  simp[outcome_of_def] >>
  drule balance_bounded_rollback >>
  simp[]
QED

Theorem step_total_balance_invariant[local]:
  wf_state s /\ balance_bounded (2 ** 256 - 1) s /\ step s = (r,s') ==>
  wf_state s' /\ balance_bounded (2 ** 256 - 1) s'
Proof
  strip_tac >> drule step_preserves_wf_state >>
  fs[balance_bounded_def] >> drule_all step_total_balance_bounded >>
  simp[]
QED

Theorem call_trace_outcomes_total_balance_bounded:
  wf_state es /\ balance_bounded (2 ** 256 - 1) es ==>
  EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1)
    (MAP SND (call_trace es))
Proof
  strip_tac >> REWRITE_TAC[call_trace_def, frame_obs_def] >>
  Cases_on `step es` >>
  drule_all step_total_balance_invariant >> strip_tac >>
  irule frame_obs_tr_every_outcome >>
  reverse conj_tac >- simp[] >>
  qexists_tac `\t. wf_state t /\ balance_bounded (2 ** 256 - 1) t` >>
  BETA_TAC >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- (rpt strip_tac >> drule_all outcome_of_total_balance_bounded >> simp[]) >>
  rpt strip_tac >> Cases_on `step t` >>
  drule_all step_total_balance_invariant >> simp[]
QED
