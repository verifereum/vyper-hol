(* TASK038: CURRENT concrete primitive and callee field transport only.
 * TOP-LEVEL: generic transports and every assigned/derived running family.
 * Reuses TASK035 boundaries; review primitive preservation on TASK040
 * activation. No per-relation semantic induction or admitted simulator. *)
Theory remainingOracleTransport
Ancestors
  remainingOracleCoverage oracleExecProps calleeTransport
  venomExecSemantics venomState

Theorem oracle_relation_step:
  (!s1 s2. R s1 s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  R s1 s2 /\ step_inst_base i1 s1 = OK t1 /\ step_inst_base i2 s2 = OK t2 ==>
  t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests = t2.vs_requests
Proof
  metis_tac[step_inst_base_oracle]
QED

Theorem oracle_relation_callee:
  (!s1 s2. R s1 s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  R s1 s2 /\ setup_callee fn1 args1 s1 = SOME c1 /\
  setup_callee fn2 args2 s2 = SOME c2 ==>
  c1.vs_outcomes = c2.vs_outcomes /\ c1.vs_requests = c2.vs_requests /\
  (merge_callee_state caller1 c1).vs_outcomes =
    (merge_callee_state caller2 c2).vs_outcomes /\
  (merge_callee_state caller1 c1).vs_requests =
    (merge_callee_state caller2 c2).vs_requests
Proof
  metis_tac[setup_callee_oracle, merge_callee_state_oracle]
QED

Theorem copy_fwd_rel_step_oracle:
  copyFwdEquiv$copy_fwd_rel dst src sz s1 s2 /\
  step_inst_base i1 s1 = OK t1 /\ step_inst_base i2 s2 = OK t2 ==>
  t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests = t2.vs_requests
Proof
  metis_tac[oracle_relation_step, copy_fwd_rel_oracle]
QED

Theorem icf_equiv_step_oracle:
  invokeCopyFwdCommonDefs$icf_equiv s1 s2 /\
  step_inst_base i1 s1 = OK t1 /\ step_inst_base i2 s2 = OK t2 ==>
  t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests = t2.vs_requests
Proof
  metis_tac[oracle_relation_step, icf_equiv_oracle]
QED

Theorem dse_equiv_step_oracle:
  deadStoreElimDefs$dse_equiv space s1 s2 /\
  step_inst_base i1 s1 = OK t1 /\ step_inst_base i2 s2 = OK t2 ==>
  t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests = t2.vs_requests
Proof
  metis_tac[oracle_relation_step, dse_equiv_oracle]
QED

Theorem dse_all_equiv_step_oracle:
  deadStoreElimDefs$dse_all_equiv s1 s2 /\
  step_inst_base i1 s1 = OK t1 /\ step_inst_base i2 s2 = OK t2 ==>
  t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests = t2.vs_requests
Proof
  metis_tac[oracle_relation_step, dse_all_equiv_oracle]
QED

Theorem m2v_equiv_step_oracle:
  mem2varDefs$m2v_equiv vars s1 s2 /\
  step_inst_base i1 s1 = OK t1 /\ step_inst_base i2 s2 = OK t2 ==>
  t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests = t2.vs_requests
Proof
  metis_tac[oracle_relation_step, m2v_equiv_oracle]
QED

Theorem m2v_inv_noix_step_oracle:
  mem2varBlockSimHelpers$m2v_inv_noix fn s1 s2 /\
  step_inst_base i1 s1 = OK t1 /\ step_inst_base i2 s2 = OK t2 ==>
  t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests = t2.vs_requests
Proof
  metis_tac[oracle_relation_step, m2v_inv_noix_oracle]
QED

Theorem memzero_inv_step_oracle:
  mmCorrectnessProofs$memzero_inv fresh s1 s2 /\
  step_inst_base i1 s1 = OK t1 /\ step_inst_base i2 s2 = OK t2 ==>
  t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests = t2.vs_requests
Proof
  metis_tac[oracle_relation_step, memzero_inv_oracle]
QED

Theorem R_dse_ok_step_oracle:
  deadStoreElimProofs$R_dse_ok space s1 s2 /\
  step_inst_base i1 s1 = OK t1 /\ step_inst_base i2 s2 = OK t2 ==>
  t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests = t2.vs_requests
Proof
  metis_tac[oracle_relation_step, R_dse_ok_oracle]
QED

Theorem m2v_inv_step_oracle:
  mem2varDefs$m2v_inv fn s1 s2 /\
  step_inst_base i1 s1 = OK t1 /\ step_inst_base i2 s2 = OK t2 ==>
  t1.vs_outcomes = t2.vs_outcomes /\ t1.vs_requests = t2.vs_requests
Proof
  metis_tac[oracle_relation_step, m2v_inv_oracle]
QED

Theorem copy_fwd_rel_callee_oracle:
  copyFwdEquiv$copy_fwd_rel dst src sz s1 s2 /\
  setup_callee fn1 args1 s1 = SOME c1 /\ setup_callee fn2 args2 s2 = SOME c2 ==>
  c1.vs_outcomes = c2.vs_outcomes /\ c1.vs_requests = c2.vs_requests /\
  (merge_callee_state caller1 c1).vs_outcomes = (merge_callee_state caller2 c2).vs_outcomes /\
  (merge_callee_state caller1 c1).vs_requests = (merge_callee_state caller2 c2).vs_requests
Proof
  rpt strip_tac >> drule copy_fwd_rel_oracle >> strip_tac >>
  metis_tac[setup_callee_oracle, merge_callee_state_oracle]
QED

Theorem icf_equiv_callee_oracle:
  invokeCopyFwdCommonDefs$icf_equiv s1 s2 /\
  setup_callee fn1 args1 s1 = SOME c1 /\ setup_callee fn2 args2 s2 = SOME c2 ==>
  c1.vs_outcomes = c2.vs_outcomes /\ c1.vs_requests = c2.vs_requests /\
  (merge_callee_state caller1 c1).vs_outcomes = (merge_callee_state caller2 c2).vs_outcomes /\
  (merge_callee_state caller1 c1).vs_requests = (merge_callee_state caller2 c2).vs_requests
Proof
  rpt strip_tac >> drule icf_equiv_oracle >> strip_tac >>
  metis_tac[setup_callee_oracle, merge_callee_state_oracle]
QED

Theorem dse_equiv_callee_oracle:
  deadStoreElimDefs$dse_equiv space s1 s2 /\
  setup_callee fn1 args1 s1 = SOME c1 /\ setup_callee fn2 args2 s2 = SOME c2 ==>
  c1.vs_outcomes = c2.vs_outcomes /\ c1.vs_requests = c2.vs_requests /\
  (merge_callee_state caller1 c1).vs_outcomes = (merge_callee_state caller2 c2).vs_outcomes /\
  (merge_callee_state caller1 c1).vs_requests = (merge_callee_state caller2 c2).vs_requests
Proof
  rpt strip_tac >> drule dse_equiv_oracle >> strip_tac >>
  metis_tac[setup_callee_oracle, merge_callee_state_oracle]
QED

Theorem dse_all_equiv_callee_oracle:
  deadStoreElimDefs$dse_all_equiv s1 s2 /\
  setup_callee fn1 args1 s1 = SOME c1 /\ setup_callee fn2 args2 s2 = SOME c2 ==>
  c1.vs_outcomes = c2.vs_outcomes /\ c1.vs_requests = c2.vs_requests /\
  (merge_callee_state caller1 c1).vs_outcomes = (merge_callee_state caller2 c2).vs_outcomes /\
  (merge_callee_state caller1 c1).vs_requests = (merge_callee_state caller2 c2).vs_requests
Proof
  rpt strip_tac >> drule dse_all_equiv_oracle >> strip_tac >>
  metis_tac[setup_callee_oracle, merge_callee_state_oracle]
QED

Theorem m2v_equiv_callee_oracle:
  mem2varDefs$m2v_equiv vars s1 s2 /\
  setup_callee fn1 args1 s1 = SOME c1 /\ setup_callee fn2 args2 s2 = SOME c2 ==>
  c1.vs_outcomes = c2.vs_outcomes /\ c1.vs_requests = c2.vs_requests /\
  (merge_callee_state caller1 c1).vs_outcomes = (merge_callee_state caller2 c2).vs_outcomes /\
  (merge_callee_state caller1 c1).vs_requests = (merge_callee_state caller2 c2).vs_requests
Proof
  rpt strip_tac >> drule m2v_equiv_oracle >> strip_tac >>
  metis_tac[setup_callee_oracle, merge_callee_state_oracle]
QED

Theorem m2v_inv_noix_callee_oracle:
  mem2varBlockSimHelpers$m2v_inv_noix fn s1 s2 /\
  setup_callee fn1 args1 s1 = SOME c1 /\ setup_callee fn2 args2 s2 = SOME c2 ==>
  c1.vs_outcomes = c2.vs_outcomes /\ c1.vs_requests = c2.vs_requests /\
  (merge_callee_state caller1 c1).vs_outcomes = (merge_callee_state caller2 c2).vs_outcomes /\
  (merge_callee_state caller1 c1).vs_requests = (merge_callee_state caller2 c2).vs_requests
Proof
  rpt strip_tac >> drule m2v_inv_noix_oracle >> strip_tac >>
  metis_tac[setup_callee_oracle, merge_callee_state_oracle]
QED

Theorem memzero_inv_callee_oracle:
  mmCorrectnessProofs$memzero_inv fresh s1 s2 /\
  setup_callee fn1 args1 s1 = SOME c1 /\ setup_callee fn2 args2 s2 = SOME c2 ==>
  c1.vs_outcomes = c2.vs_outcomes /\ c1.vs_requests = c2.vs_requests /\
  (merge_callee_state caller1 c1).vs_outcomes = (merge_callee_state caller2 c2).vs_outcomes /\
  (merge_callee_state caller1 c1).vs_requests = (merge_callee_state caller2 c2).vs_requests
Proof
  rpt strip_tac >> drule memzero_inv_oracle >> strip_tac >>
  metis_tac[setup_callee_oracle, merge_callee_state_oracle]
QED

Theorem R_dse_ok_callee_oracle:
  deadStoreElimProofs$R_dse_ok space s1 s2 /\
  setup_callee fn1 args1 s1 = SOME c1 /\ setup_callee fn2 args2 s2 = SOME c2 ==>
  c1.vs_outcomes = c2.vs_outcomes /\ c1.vs_requests = c2.vs_requests /\
  (merge_callee_state caller1 c1).vs_outcomes = (merge_callee_state caller2 c2).vs_outcomes /\
  (merge_callee_state caller1 c1).vs_requests = (merge_callee_state caller2 c2).vs_requests
Proof
  rpt strip_tac >> drule R_dse_ok_oracle >> strip_tac >>
  metis_tac[setup_callee_oracle, merge_callee_state_oracle]
QED

Theorem m2v_inv_callee_oracle:
  mem2varDefs$m2v_inv fn s1 s2 /\
  setup_callee fn1 args1 s1 = SOME c1 /\ setup_callee fn2 args2 s2 = SOME c2 ==>
  c1.vs_outcomes = c2.vs_outcomes /\ c1.vs_requests = c2.vs_requests /\
  (merge_callee_state caller1 c1).vs_outcomes = (merge_callee_state caller2 c2).vs_outcomes /\
  (merge_callee_state caller1 c1).vs_requests = (merge_callee_state caller2 c2).vs_requests
Proof
  rpt strip_tac >> drule m2v_inv_oracle >> strip_tac >>
  metis_tac[setup_callee_oracle, merge_callee_state_oracle]
QED
