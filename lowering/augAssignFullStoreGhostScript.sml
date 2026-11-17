(* A word store preserves the ghost frame at any reserved-memory bound. *)
Theory augAssignFullStoreGhost
Ancestors
  bodyPtrDefs ptrDiscipline accountsRelProps sourceUnitExecution vyperStorageFootprint
  vyperStorageBackend vyperState vyperValue venomState
  finite_map pred_set

Theorem clean_storage_store_taint_ok_at:
  dead_lo_ok H D lo cenv cx /\ stor_taint_ok_at D tn s /\
  s.vs_call_ctx.cc_address = cx.txn.target /\
  (!k b. storage_dead H tr
    (update_storage slot w (if tr then contract_transient s else contract_storage s)) k b =
    storage_dead H tr (if tr then contract_transient s else contract_storage s) k b) ==>
  stor_taint_ok_at D
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
    (if tr then tstore slot w s else sstore slot w s)
Proof
  strip_tac >> Cases_on `tr` >>
  gvs[dead_lo_ok_def, stor_taint_ok_at_def, cx_dead_def, sstore_def, tstore_def,
      contract_storage_def, contract_transient_def,
      vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM,
      key_update_def, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem ghost_inv_at_storage_word_store:
  ghost_inv_at D lo d cenv cx es G tn s /\
  dead_lo_ok H D lo cenv cx /\ es'.scopes = es.scopes /\
  s.vs_call_ctx.cc_address = cx.txn.target /\
  (!k b. storage_dead H tr
    (update_storage slot w (if tr then contract_transient s else contract_storage s)) k b =
    storage_dead H tr (if tr then contract_transient s else contract_storage s) k b) ==>
  ghost_inv_at D lo d cenv cx es' G
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
    ((if tr then tstore slot w s else sstore slot w s) with vs_inst_idx := pc)
Proof
  strip_tac >>
  `stor_taint_ok_at D tn s` by fs[ghost_inv_at_def] >>
  drule_all clean_storage_store_taint_ok_at >> strip_tac >>
  Cases_on `d`
  >- (Cases_on `tr` >>
      gvs[ghost_inv_at_def, return_buf_ptr_def, ptr_covers_def, op_taint_def,
          sstore_def, tstore_def, lookup_var_def, allocas_from_def,
          stor_taint_ok_at_def] >> metis_tac[]) >>
  PairCases_on `x` >> Cases_on `tr` >>
  gvs[ghost_inv_at_def, return_buf_ptr_def, ptr_covers_def, op_taint_def,
      sstore_def, tstore_def, lookup_var_def, allocas_from_def,
      stor_taint_ok_at_def] >> metis_tac[]
QED

Theorem ghost_kept_at_storage_word_store:
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 G
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
Proof
  Cases_on `tr` >> simp[ghost_kept_at_def, op_taint_def] >>
  strip_tac >> conj_tac >> first_assum ACCEPT_TAC
QED
