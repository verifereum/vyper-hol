Theory bodyLogSavedNonmemoryPtrMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyPtrDefs loweringPosts
  stateRelProj stateRelProjStorage accountsRelProps exprPtrUnwrapStorageFacts
  loweringStateRelDefs vyperStorageBackend sourceUnitExecution pred_set venomState arithmetic

(* Live source slots can only carry taint where the corresponding target
   byte is dead, provided the reached range still agrees. *)
Theorem log_saved_slot_dead[local]:
  storage_agree (storage_dead H tr src) src dst /\
  storage_range_agree src dst w rt /\ storage_read_live H tr src w rt /\
  storage_dead H tr dst j b /\ w2n w <= j /\ j < type_slot_size rt + w2n w ==>
  dead_bytes dst (w2n w) rt j b
Proof
  strip_tac >>
  drule storage_agree_storage_dead >> strip_tac >>
  drule storage_range_agree_dead_bytes >> simp[] >> disch_tac >>
  fs[storage_read_live_def, ADD_COMM]
QED

Theorem log_saved_nonmemory_ptr_mods:
  p.ptr_location <> LocMemory /\
  stmt_state_rel H ctx func ce cx ee u /\
  vv_holds_mods ce cx ty raw (LocatedValue ty p) ee u /\
  vv_storage_live H cx (LocatedValue ty p) ee u /\
  ghost_inv_at_mods D lo d ce cx ee Gu tu u /\
  dead_lo_ok_mods H D lo ce cx /\
  op_taint tu p.ptr_operand = {} /\
  (p.ptr_location = LocCode ==> op_prov Gu p.ptr_operand = NONE) ==>
  ptr_vv_ok cx ty raw (LocatedValue ty p) ee Gu tu u
Proof
  strip_tac >>
  drule stmt_state_rel_state_rel >> strip_tac >>
  `u.vs_call_ctx.cc_address = cx.txn.target` by
    (drule state_rel_call_ctx_rel >> simp[call_ctx_rel_def]) >>
  `tu.t_stor SUBSET (cx_dead H cx).d_stor u.vs_call_ctx.cc_address
                   (u.vs_accounts u.vs_call_ctx.cc_address).storage /\
   tu.t_trans SUBSET (cx_dead H cx).d_trans u.vs_call_ctx.cc_address
                    (u.vs_transient u.vs_call_ctx.cc_address)` by
    fs[dead_lo_ok_mods_def, ghost_inv_at_mods_def, stor_taint_ok_at_def] >>
  simp[ptr_vv_ok_def] >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (strip_tac >>
      drule state_rel_storage_rel >>
      simp[storage_rel_def, GSYM (cj 2 get_storage_def),
           vfmStateTheory.lookup_account_def] >> strip_tac >>
      `storage_range_agree (get_storage cx ee F) (contract_storage u) w ty'` by
        gvs[vv_holds_mods_def, vv_holds_def, storage_holds_def] >>
      `storage_read_live H F (get_storage cx ee F) w ty'` by
        fs[vv_storage_live_def] >>
      `storage_dead H F (contract_storage u) (w2n k) b` by
        (qpat_x_assum `tu.t_stor SUBSET _` mp_tac >>
         simp[cx_dead_def, contract_storage_def, vfmStateTheory.lookup_account_def,
              SUBSET_DEF] >>
         disch_then (qspec_then `(k,b)` mp_tac) >> simp[]) >>
      drule_all log_saved_slot_dead >>
      simp[contract_storage_def, vfmStateTheory.lookup_account_def]) >>
  strip_tac >>
  drule state_rel_transient_rel >>
  simp[transient_rel_def, GSYM (cj 1 get_storage_def)] >> strip_tac >>
  `storage_range_agree (get_storage cx ee T) (contract_transient u) w ty'` by
    gvs[vv_holds_mods_def, vv_holds_def, storage_holds_def] >>
  `storage_read_live H T (get_storage cx ee T) w ty'` by
    fs[vv_storage_live_def] >>
  `storage_dead H T (contract_transient u) (w2n k) b` by
    (qpat_x_assum `tu.t_trans SUBSET _` mp_tac >>
     simp[cx_dead_def, contract_transient_def, SUBSET_DEF] >>
     disch_then (qspec_then `(k,b)` mp_tac) >> simp[]) >>
  drule_all log_saved_slot_dead >> simp[contract_transient_def]
QED
