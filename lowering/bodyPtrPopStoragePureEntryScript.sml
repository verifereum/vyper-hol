(* Entry boundaries for nested storage pop. *)
Theory bodyPtrPopStoragePureEntry
Ancestors
  bodyPtrPopTargetDefs exprSimPopNestedBase targetPlaceLive
  appendStorageGhostPtr exprPtrUnwrapStorageFacts
  accountsRelProps vyperStorageBackend vyperValue pred_set compileEnv
  loweringPosts venomState ptrDiscipline exprLoweringProps bodyPtrDefs

Theorem pop_storage_live_agree:
  storage_agree (storage_dead cx tr st) st rt /\
  storage_read_live cx tr st slot tv /\
  w2n slot + type_slot_size tv <= dimword(:256) ==>
  storage_read_live cx tr rt slot tv
Proof
  strip_tac >>
  drule storage_agree_storage_dead >> strip_tac >>
  drule_all storage_range_agree_of_live >> strip_tac >>
  drule storage_range_agree_dead_bytes >> strip_tac >>
  gvs[storage_read_live_def]
QED

Theorem pop_storage_machine_live:
  stmt_state_rel ctx func cenv cx es s /\
  storage_read_live cx tr (get_storage cx es tr) slot tv /\
  w2n slot + type_slot_size tv <= dimword(:256) ==>
  storage_read_live cx tr
    (if tr then contract_transient s else contract_storage s) slot tv
Proof
  strip_tac >> irule pop_storage_live_agree >>
  goal_assum (drule_at Any) >> simp[] >>
  Cases_on `tr` >>
  gvs[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
      get_storage_def, vfmStateTheory.lookup_account_def] >>
  metis_tac[]
QED

Theorem pop_storage_live_header_clean:
  stor_taint_ok cx tn s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
  storage_read_live cx tr
    (if tr then contract_transient s else contract_storage s) slot tv /\
  0 < type_slot_size tv ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}
Proof
  strip_tac >> irule storage_dead_key_taint_empty >>
  goal_assum (drule_at Any) >> simp[] >>
  Cases_on `tr` >>
  gvs[stor_taint_ok_def, cx_dead_def, contract_storage_def,
      contract_transient_def, vfmStateTheory.lookup_account_def] >>
  metis_tac[]
QED

Theorem pop_storage_target_operand_clean:
  target_ptr_ok cenv (PlaceR (StoragePlace tr slot tv))
    (hdr,loc,pt) G tn s ==>
  op_taint tn hdr = {} /\ op_prov G hdr = NONE
Proof
  simp[target_ptr_ok_def]
QED
