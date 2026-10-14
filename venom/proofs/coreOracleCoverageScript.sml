(* Actual-state coverage: core and generic relations already retain both lists.
 * No residual definition needs an additional selector clause. *)
Theory coreOracleCoverage
Ancestors
  venomState stateFrame stateEquiv oracleStateProps
  execEquivParamDefs execEquivParamBase

(* Shared projection boundary for any canonical mask retaining both lists. *)
Theorem oracle_mask_transport:
  (!s. (mask s).vs_outcomes = s.vs_outcomes /\
       (mask s).vs_requests = s.vs_requests) /\
  mask s1 = mask s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  rpt strip_tac >> metis_tac[]
QED

Theorem vsr_frame_oracle[simp]:
  (vsr_frame s).vs_outcomes = s.vs_outcomes /\
  (vsr_frame s).vs_requests = s.vs_requests /\
  (vsr_term_frame s).vs_outcomes = s.vs_outcomes /\
  (vsr_term_frame s).vs_requests = s.vs_requests
Proof
  simp[vsr_frame_def, vsr_term_frame_def]
QED

Theorem vsr_frame_oracle_transport:
  (vsr_frame s1 = vsr_frame s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (vsr_term_frame s1 = vsr_term_frame s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
Proof
  conj_tac
  >- (strip_tac >> irule oracle_mask_transport >>
      qexists_tac `vsr_frame` >>
      simp_tac bool_ss [vsr_frame_oracle] >> metis_tac[]) >>
  strip_tac >> irule oracle_mask_transport >>
  qexists_tac `vsr_term_frame` >>
  simp_tac bool_ss [vsr_frame_oracle] >> metis_tac[]
QED

Theorem execution_equiv_oracle:
  execution_equiv vars s1 s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  strip_tac >> irule oracle_execution_frame_transport >>
  fs[execution_equiv_def, Excl "core_complete_mask_equality"]
QED

Theorem state_equiv_oracle:
  state_equiv vars s1 s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  simp[state_equiv_def] >> metis_tac[execution_equiv_oracle]
QED

Theorem valid_state_rel_oracle:
  valid_state_rel R_ok R_term ==>
  (!s1 s2. R_ok s1 s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (!s1 s2. R_term s1 s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
Proof
  strip_tac >> conj_tac >> rpt gen_tac >> strip_tac
  >- (irule (cj 1 vsr_frame_oracle_transport) >>
      drule_all vsr_R_ok_frame >> simp[]) >>
  irule (cj 2 vsr_frame_oracle_transport) >>
  drule_all vsr_R_term_frame >> simp[]
QED

Theorem core_relations_oracle_coverage:
  (execution_equiv vars s1 s2 <=> execution_equiv vars s1 s2 /\
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (state_equiv vars s1 s2 <=> state_equiv vars s1 s2 /\
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
Proof
  conj_tac >- metis_tac[execution_equiv_oracle] >>
  metis_tac[state_equiv_oracle]
QED

Theorem valid_state_rel_oracle_coverage:
  valid_state_rel R_ok R_term <=>
  valid_state_rel R_ok R_term /\
  (!s1 s2. R_ok s1 s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (!s1 s2. R_term s1 s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
Proof
  metis_tac[valid_state_rel_oracle]
QED
