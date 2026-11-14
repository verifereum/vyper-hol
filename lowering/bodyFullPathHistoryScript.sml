Theory bodyFullPathHistory
Ancestors
  fragGasOriginPtr allocaHistory fragExec venomMemDefs venomMemProofs venomExecProofs venomState

Theorem body_full_edge_alloca_history[local]:
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (s,G,tn) marks (OK u,G',tn') /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s ==>
  alloca_history func u /\ alloca_inv u
Proof
  strip_tac >> drule gas_origin_ptr_edge_common_fuel >> strip_tac >>
  gvs[exit_result_def]
  >~ [`OK u = step_inst fuel ctx inst s`]
  >- (qpat_x_assum `OK _ = _` (assume_tac o SYM) >> gvs[exit_result_def])
  >~ [`OK u = step_inst fuel ctx inst s`]
  >- (qpat_x_assum `OK _ = _` (assume_tac o SYM) >> gvs[exit_result_def]) >>
  drule_all alloca_history_step >> simp[] >> strip_tac >>
  drule_all alloca_inv_step_inst_proof >> strip_tac
  >>~- ([`alloca_history func (_ with vs_inst_idx := phi_prefix_length _)`],
    drule_all history_phi_entry >> strip_tac >>
    drule eval_phis_preserves_alloca_fields >> strip_tac >>
    gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >> metis_tac[]) >>
  gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED

Theorem body_full_path_alloca_history_pair[local]:
  !cx st marks out.
    gas_origin_ptr_path cx st marks out ==>
    case (cx,st,out) of
      ((D,lo,explicit,ctx,func,PG),(s,G,tn),(r,G',tn')) =>
        !u. r = OK u /\ fn_inst_ids_distinct func /\
          alloca_history func s /\ alloca_inv s ==>
          alloca_history func u /\ alloca_inv u
Proof
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac >>
  rpt gen_tac >> simp[] >> rpt strip_tac >>
  gvs[exit_result_def] >> metis_tac[body_full_edge_alloca_history]
QED

Theorem body_full_path_alloca_history:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) marks (OK u,G',tn') /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s ==>
  alloca_history func u
Proof
  strip_tac >> drule body_full_path_alloca_history_pair >> simp[]
QED

