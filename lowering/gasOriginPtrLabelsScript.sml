Theory gasOriginPtrLabels
Ancestors
  fragGasOriginPtr fragGasOrigin venomExecProofs venomExecProps
  venomExecSemantics venomState fragExec
  ptrSafetyTransport fragGasPathPtr ptrDiscipline arithmetic

Theorem gas_origin_edge_preserves_labels[local]:
  gas_origin_edge memory explicit ctx func s marks (OK t) ==>
  t.vs_labels = s.vs_labels
Proof
  rw[gas_origin_edge_def] >> gvs[exit_result_def] >>
  imp_res_tac step_inst_preserves_labels_always >>
  imp_res_tac eval_phis_preserves_labels >>
  gvs[jump_to_def] >> metis_tac[step_inst_preserves_labels_always]
QED

Theorem gas_origin_path_preserves_labels:
  !memory explicit ctx func s marks r.
    gas_origin_path memory explicit ctx func s marks r ==>
    !t. r = OK t ==> t.vs_labels = s.vs_labels
Proof
  ho_match_mp_tac gas_origin_path_ind >> rpt conj_tac >>
  rpt strip_tac >> gvs[]
  >- metis_tac[gas_origin_edge_preserves_labels]
  >> gvs[exit_result_def]
QED

Theorem gas_origin_ptr_path_preserves_labels:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) marks (OK t,G',tn') ==> t.vs_labels = s.vs_labels
Proof
  metis_tac[gas_origin_ptr_path_projections, gas_origin_path_preserves_labels]
QED

Theorem member_path_allocas_from:
  !D lo ctx fn PG G tn s marks H u r.
    gas_path_ptr D lo ctx fn PG G tn s marks H u r ==>
    !lower t.
      r = OK t /\ allocas_from lower s /\ lower <= s.vs_alloca_next /\
      lo <= lower ==>
      allocas_from lower t /\ lower <= t.vs_alloca_next
Proof
  ho_match_mp_tac gas_path_ptr_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> gvs[] >>
      drule_all gas_path_ptr_edge_lower_bound_transport >> strip_tac >>
      res_tac >> first_x_assum irule >> simp[])
  >> rpt strip_tac >> gvs[fragExecTheory.exit_result_def]
QED

Theorem member_origin_allocas_from:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) marks (OK t,G',tn') /\
  allocas_from lower s /\ lower <= s.vs_alloca_next /\ lo <= lower ==>
  allocas_from lower t /\ lower <= t.vs_alloca_next
Proof
  strip_tac >> drule gas_origin_ptr_path_projections >> strip_tac >>
  drule member_path_allocas_from >> simp[]
QED
