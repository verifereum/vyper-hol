(* CURRENT TASK035 primitive/setup/merge contracts, not oracle activation.
 * TASK040 must revisit primitive preservation when CALL consumes outcomes. *)
Theory coreOracleTransport
Ancestors
  coreOracleCoverage oracleExecProps calleeTransport stateEquiv
  stateEquivProps venomExecSemantics venomState

Theorem core_equiv_step_oracle:
  (execution_equiv vars s1 s2 \/ state_equiv vars s1 s2) /\
  step_inst_base i1 s1 = OK t1 /\ step_inst_base i2 s2 = OK t2 ==>
  t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests = t2.vs_requests
Proof
  metis_tac[step_inst_base_oracle, execution_equiv_oracle, state_equiv_oracle]
QED

Theorem valid_state_rel_step_oracle:
  valid_state_rel R_ok R_term /\ (R_ok s1 s2 \/ R_term s1 s2) /\
  step_inst_base i1 s1 = OK t1 /\ step_inst_base i2 s2 = OK t2 ==>
  t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests = t2.vs_requests
Proof
  metis_tac[step_inst_base_oracle, valid_state_rel_oracle]
QED

Theorem core_equiv_callee_oracle:
  (execution_equiv vars s1 s2 \/ state_equiv vars s1 s2) /\
  setup_callee fn1 args1 s1 = SOME c1 /\
  setup_callee fn2 args2 s2 = SOME c2 ==>
  c1.vs_outcomes = c2.vs_outcomes /\ c1.vs_requests = c2.vs_requests /\
  (merge_callee_state caller1 c1).vs_outcomes =
    (merge_callee_state caller2 c2).vs_outcomes /\
  (merge_callee_state caller1 c1).vs_requests =
    (merge_callee_state caller2 c2).vs_requests
Proof
  metis_tac[execution_equiv_oracle, state_equiv_oracle,
    setup_callee_oracle, merge_callee_state_oracle]
QED

Theorem valid_state_rel_callee_oracle:
  valid_state_rel R_ok R_term /\ (R_ok s1 s2 \/ R_term s1 s2) /\
  setup_callee fn1 args1 s1 = SOME c1 /\
  setup_callee fn2 args2 s2 = SOME c2 ==>
  c1.vs_outcomes = c2.vs_outcomes /\ c1.vs_requests = c2.vs_requests /\
  (merge_callee_state caller1 c1).vs_outcomes =
    (merge_callee_state caller2 c2).vs_outcomes /\
  (merge_callee_state caller1 c1).vs_requests =
    (merge_callee_state caller2 c2).vs_requests
Proof
  metis_tac[valid_state_rel_oracle, setup_callee_oracle, merge_callee_state_oracle]
QED

(* Generic contract includes strong abort relation when requested; successful
 * observability still uses revert_equiv on abort and does NOT compare lists. *)
Theorem valid_state_rel_result_oracle:
  valid_state_rel R_ok R_term /\
  lift_result R_ok R_term R_term r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\
              s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\
              s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\
              s1.vs_requests = s2.vs_requests) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[lift_result_def] >> metis_tac[valid_state_rel_oracle]
QED

Theorem core_result_equiv_oracle:
  result_equiv vars r1 r2 ==>
  lift_result
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\
              s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\
              s1.vs_requests = s2.vs_requests)
    (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\
              s1.vs_requests = s2.vs_requests) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[result_equiv_def, lift_result_def] >>
  metis_tac[execution_equiv_oracle, state_equiv_oracle]
QED
