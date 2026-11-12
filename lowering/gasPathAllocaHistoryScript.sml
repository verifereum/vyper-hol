(* Allocation history follows counted normal fragment paths, including phi entry. *)
Theory gasPathAllocaHistory
Ancestors
  fragGasPath allocaHistory venomMemProps venomMemDefs venomExecProofs
  venomExecSemantics venomState fragExec

Theorem gas_path_edge_alloca_history[local]:
  gas_path_edge ctx func s n (OK t) /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s ==>
  alloca_history func t /\ alloca_inv t
Proof
  simp[gas_path_edge_def] >> strip_tac >> gvs[exit_result_def]
  >- (drule_all alloca_history_step >> simp[] >> strip_tac >>
      drule_all alloca_inv_step_inst >>
      simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def])
  >- (drule_all alloca_history_step >> simp[] >> strip_tac >>
      drule_all alloca_inv_step_inst >> strip_tac >>
      conj_tac
      >- (irule history_phi_entry >> metis_tac[]) >>
      drule eval_phis_preserves_alloca_fields >> strip_tac >>
      gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
      metis_tac[])
  >- (gvs[jump_to_def, alloca_history_def, alloca_inv_def,
          allocas_non_overlapping_def, alloca_next_valid_def] >> metis_tac[]) >>
  qpat_x_assum `exit_result _` mp_tac >>
  qpat_x_assum `OK t = _` (SUBST1_TAC o SYM) >> simp[exit_result_def]
QED

Theorem gas_path_alloca_history:
  gas_path ctx func s n (OK t) /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s ==>
  alloca_history func t /\ alloca_inv t
Proof
  `!ctx func s n r. gas_path ctx func s n r ==>
    !t. r = OK t ==> fn_inst_ids_distinct func ==>
    alloca_history func s /\ alloca_inv s ==>
    alloca_history func t /\ alloca_inv t` suffices_by metis_tac[] >>
  ho_match_mp_tac gas_path_ind >> rpt strip_tac >> gvs[exit_result_def] >>
  metis_tac[gas_path_edge_alloca_history]
QED
