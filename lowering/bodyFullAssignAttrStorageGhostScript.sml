(* A word-field store preserves the constructor's fixed memory region as
   well as the storage taint permitted by the chosen finite horizon. *)
Theory bodyFullAssignAttrStorageGhost
Ancestors
  assignTuplePtrStorage accountsRelProps bodyPtrDefs ptrDiscipline
  sourceUnitExecution venomState venomInst vyperStorageBackend vyperValue
  loweringStateRelDefs vfmState finite_map pred_set combin

Theorem storage_field_store_ghost_at:
  ghost_inv_at D lo d cenv cx es G tn s /\
  dead_lo_ok H D lo cenv cx /\ es'.scopes = es.scopes /\
  eval_operand dst s = SOME (root + n2w off) /\
  op_taint tn value = {} /\
  MEM (tr,root,StructTV fs) (FST H) /\
  struct_field_slot fs fld = SOME (off,ftv) /\ type_slot_size ftv = 1 ==>
  ghost_inv_at D lo d cenv cx es' G
    (step_taint (mk_inst iid (if tr then TSTORE else SSTORE) [dst;value] [])
      s (if tr then tstore (root + n2w off) w s
           else sstore (root + n2w off) w s) tn)
    (if tr then tstore (root + n2w off) w s
     else sstore (root + n2w off) w s)
Proof
  strip_tac >>
  `!u st. storage_dead H tr (update_storage (root + n2w off) u st) =
          storage_dead H tr st` by
    (rpt gen_tac >> irule storage_dead_update_struct_word_field >>
     metis_tac[]) >>
  `(if tr then tstore (root + n2w off) w s
    else sstore (root + n2w off) w s).vs_allocas = s.vs_allocas /\
   (if tr then tstore (root + n2w off) w s
    else sstore (root + n2w off) w s).vs_fmp = s.vs_fmp` by
    (Cases_on `tr` >> simp[tstore_def, sstore_def]) >>
  drule_all clean_storage_step_taint_ptr >>
  disch_then (qspecl_then [`tr`, `iid`] strip_assume_tac) >>
  `stor_taint_ok_at D
     (step_taint (mk_inst iid (if tr then TSTORE else SSTORE) [dst;value] [])
       s (if tr then tstore (root + n2w off) w s
            else sstore (root + n2w off) w s) tn)
     (if tr then tstore (root + n2w off) w s
      else sstore (root + n2w off) w s)` by
    (fs[ghost_inv_at_def, dead_lo_ok_def, stor_taint_ok_at_def] >>
     Cases_on `tr` >>
     gvs[cx_dead_def, sstore_def, tstore_def, lookup_account_def,
         APPLY_UPDATE_THM] >>
     simp[SUBSET_DEF] >> metis_tac[SUBSET_DEF]) >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_inv_at_def] >> strip_tac >>
  Cases_on `tr` >>
  gvs[tstore_def, sstore_def, allocas_from_def, op_taint_def,
      lookup_var_def, ptr_covers_def] >>
  (Cases_on `d` >-
     (gvs[return_buf_ptr_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
   rename1 `return_buf_ptr (SOME rb) cenv G tn s` >>
   PairCases_on `rb` >>
   gvs[return_buf_ptr_def, ptr_covers_def, op_taint_def, lookup_var_def] >>
   rpt conj_tac >> first_assum ACCEPT_TAC)
QED
