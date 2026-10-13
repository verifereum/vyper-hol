(* TASK038: FIRST actual-datatype audit. No relation definition changes.
 * TOP-LEVEL: residual-mask transport and exact running-relation coverage.
 * Every old address-space, FMP, variable and memory contract is retained. *)
Theory remainingOracleCoverage
Ancestors
  passResidualFrame copyFwdEquiv invokeCopyFwdCommonDefs
  deadStoreElimFrame deadStoreElimDefs deadStoreElimProofs
  mem2varFrame mem2varDefs mem2varBlockSimHelpers
  memzeroFrame mmCorrectnessProofs venomState

Theorem remaining_frame_oracle[simp]:
  (copy_fwd_frame s).vs_outcomes = s.vs_outcomes /\
  (copy_fwd_frame s).vs_requests = s.vs_requests /\
  (icf_frame s).vs_outcomes = s.vs_outcomes /\
  (icf_frame s).vs_requests = s.vs_requests /\
  (dse_frame space s).vs_outcomes = s.vs_outcomes /\
  (dse_frame space s).vs_requests = s.vs_requests /\
  (dse_all_frame s).vs_outcomes = s.vs_outcomes /\
  (dse_all_frame s).vs_requests = s.vs_requests /\
  (m2v_frame s).vs_outcomes = s.vs_outcomes /\
  (m2v_frame s).vs_requests = s.vs_requests /\
  (memzero_frame s).vs_outcomes = s.vs_outcomes /\
  (memzero_frame s).vs_requests = s.vs_requests
Proof
  Cases_on `space` >> simp[copy_fwd_frame_def, icf_frame_def,
    dse_frame_def, dse_all_frame_def, m2v_frame_def, memzero_frame_def]
QED

Theorem remaining_frame_oracle_transport:
  (copy_fwd_frame s1 = copy_fwd_frame s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (icf_frame s1 = icf_frame s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (dse_frame space s1 = dse_frame space s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (dse_all_frame s1 = dse_all_frame s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (m2v_frame s1 = m2v_frame s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (memzero_frame s1 = memzero_frame s2 ==>
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
Proof
  conj_tac >- (strip_tac >> conj_tac >> irule copy_fwd_frame_projection >>
    simp_tac bool_ss [remaining_frame_oracle] >> metis_tac[]) >>
  conj_tac >- (strip_tac >> conj_tac >> irule icf_frame_projection >>
    simp_tac bool_ss [remaining_frame_oracle] >> metis_tac[]) >>
  conj_tac >- (strip_tac >> conj_tac >> irule dse_frame_projection >>
    simp_tac bool_ss [remaining_frame_oracle] >> metis_tac[]) >>
  conj_tac >- (strip_tac >> conj_tac >> irule dse_all_frame_projection >>
    simp_tac bool_ss [remaining_frame_oracle] >> metis_tac[]) >>
  conj_tac >- (strip_tac >> conj_tac >> irule m2v_frame_projection >>
    simp_tac bool_ss [remaining_frame_oracle] >> metis_tac[]) >>
  strip_tac >> conj_tac >> irule memzero_frame_projection >>
  simp_tac bool_ss [remaining_frame_oracle] >> metis_tac[]
QED

Theorem copy_fwd_rel_oracle:
  copy_fwd_rel dst src sz s1 s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  strip_tac >> irule (cj 1 remaining_frame_oracle_transport) >>
  fs[copy_fwd_rel_def]
QED

Theorem icf_equiv_oracle:
  icf_equiv s1 s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  strip_tac >> irule (cj 2 remaining_frame_oracle_transport) >> fs[icf_equiv_def]
QED

Theorem dse_equiv_oracle:
  dse_equiv space s1 s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  strip_tac >> irule (cj 3 remaining_frame_oracle_transport) >>
  qexists_tac `space` >> fs[dse_equiv_def]
QED

Theorem dse_all_equiv_oracle:
  dse_all_equiv s1 s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  strip_tac >> irule (cj 4 remaining_frame_oracle_transport) >> fs[dse_all_equiv_def]
QED

Theorem m2v_equiv_oracle:
  m2v_equiv vars s1 s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  strip_tac >> irule (cj 5 remaining_frame_oracle_transport) >> fs[m2v_equiv_def]
QED

Theorem m2v_inv_noix_oracle:
  m2v_inv_noix fn s1 s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  strip_tac >> irule (cj 5 remaining_frame_oracle_transport) >> fs[m2v_inv_noix_def]
QED

Theorem memzero_inv_oracle:
  memzero_inv fresh s1 s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  strip_tac >> irule (cj 6 remaining_frame_oracle_transport) >> fs[memzero_inv_def]
QED

(* Derived running relations found by the full inventory, not new masks. *)
Theorem R_dse_ok_oracle:
  R_dse_ok space s1 s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  simp[R_dse_ok_def] >> metis_tac[dse_equiv_oracle]
QED

Theorem m2v_inv_oracle:
  m2v_inv fn s1 s2 ==>
  s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests
Proof
  simp[m2v_inv_def] >> metis_tac[m2v_equiv_oracle]
QED

Theorem remaining_relations_oracle_coverage:
  (copy_fwd_rel dst src sz s1 s2 <=> copy_fwd_rel dst src sz s1 s2 /\
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (icf_equiv s1 s2 <=> icf_equiv s1 s2 /\
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (dse_equiv space s1 s2 <=> dse_equiv space s1 s2 /\
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (dse_all_equiv s1 s2 <=> dse_all_equiv s1 s2 /\
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (m2v_equiv vars s1 s2 <=> m2v_equiv vars s1 s2 /\
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (m2v_inv_noix fn s1 s2 <=> m2v_inv_noix fn s1 s2 /\
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (memzero_inv fresh s1 s2 <=> memzero_inv fresh s1 s2 /\
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (R_dse_ok space s1 s2 <=> R_dse_ok space s1 s2 /\
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests) /\
  (m2v_inv fn s1 s2 <=> m2v_inv fn s1 s2 /\
    s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
Proof
  conj_tac >- metis_tac[copy_fwd_rel_oracle] >>
  conj_tac >- metis_tac[icf_equiv_oracle] >>
  conj_tac >- metis_tac[dse_equiv_oracle] >>
  conj_tac >- metis_tac[dse_all_equiv_oracle] >>
  conj_tac >- metis_tac[m2v_equiv_oracle] >>
  conj_tac >- metis_tac[m2v_inv_noix_oracle] >>
  conj_tac >- metis_tac[memzero_inv_oracle] >>
  conj_tac >- metis_tac[R_dse_ok_oracle] >>
  metis_tac[m2v_inv_oracle]
QED
