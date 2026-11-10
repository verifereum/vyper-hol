(* Allocation history follows actual successful counted execution. *)
Theory gasPathAllocaHistory
Ancestors
  fragGasMode fragGasPath allocaHistory venomMemProofs venomMemDefs
  venomExecSemantics venomExecProofs venomInstProofs rangeAnalysisProofs
  venomInst venomState list arithmetic

Theorem gas_path_edge_history[local]:
  gas_path_edge ctx func s n (OK t) /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s ==>
  alloca_history func t /\ alloca_inv t
Proof
  strip_tac >>
  qpat_x_assum `gas_path_edge _ _ _ _ _` mp_tac >>
  simp[gas_path_edge_def, fragExecTheory.exit_result_def] >>
  strip_tac
  >- suspend "advance"
  >- suspend "phis"
  >- suspend "jump" >>
  qpat_x_assum `OK t = _` (assume_tac o SYM) >>
  gvs[fragExecTheory.exit_result_def]
QED

Resume gas_path_edge_history[advance]:
  drule_all alloca_history_step >>
  drule_all alloca_inv_step_inst_proof >>
  rpt strip_tac >>
  gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED

Resume gas_path_edge_history[phis]:
  drule_all alloca_history_step >>
  drule_all alloca_inv_step_inst_proof >>
  drule eval_phis_preserves_alloca_fields >> strip_tac >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  simp[] >> disch_tac >> disch_tac >>
  conj_tac
  >- (gvs[alloca_history_def] >>
      rpt strip_tac >>
      gvs[get_instruction_def] >>
      drule rangeAnalysisProofsTheory.phi_prefix_length_el_phi >>
      simp[]) >>
  gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED

Resume gas_path_edge_history[jump]:
  drule_all alloca_history_step >>
  drule_all alloca_inv_step_inst_proof >>
  rpt strip_tac >>
  gvs[jump_to_def, alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED

Finalise gas_path_edge_history

Theorem gas_path_history[local]:
  !ctx func s n r. gas_path ctx func s n r ==>
    !t. r = OK t ==> fn_inst_ids_distinct func /\
      alloca_history func s /\ alloca_inv s ==>
      alloca_history func t /\ alloca_inv t
Proof
  ho_match_mp_tac gas_path_ind >> rpt conj_tac
  >- simp[]
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      strip_tac >> drule_all gas_path_edge_history >> strip_tac >>
      first_x_assum irule >> simp[]) >>
  rpt strip_tac >> gvs[fragExecTheory.exit_result_def]
QED

Theorem gas_marked_path_alloca_history:
  !memory ctx func s n t.
    gas_marked_path memory ctx func s n (OK t) /\
    fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s ==>
    alloca_history func t
Proof
  rpt strip_tac >> drule gas_marked_path_exec >>
  metis_tac[gas_path_history]
QED
