(* Live storage reads and counted readonly loads for augmented places. *)
Theory bodyIntCallFamStmtMutationAugPlaceStorageReady
Ancestors
  bodyIntCallFamStmtMutationLoad stmtSimAugAssignPlaceStorage
  vyperStoragePlaceProvenance vyperPlaceStoragePreservation accountsRelProps
  exprSimUnwrap transientLockProps emitHelperProps venomInst venomState
  bodyIntCallJointContract

Theorem intcall_storage_place_read_ready:
  eval_target_place cx tg es = (INL (StoragePlace tr slot tv),ee) /\
  storage_layout_safe cx /\ contract_storage_well_formed cx ee /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv ==>
  storage_place_region cx (StoragePlace tr slot tv) /\
  slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
  storage_read_live cx tr (get_storage cx ee tr) slot tv /\
  ?cur. read_place cx (StoragePlace tr slot tv) ee = (INL cur,ee) /\
    place_type_value cx (StoragePlace tr slot tv) ee = (INL tv,ee) /\
    value_has_type tv cur
Proof
  strip_tac >>
  `storage_place_region cx (StoragePlace tr slot tv)` by
    metis_tac[eval_target_place_region] >>
  `0 < type_slot_size tv` by
    (drule_all word_type_slot_size >> simp[]) >>
  `slots_in_range (get_storage cx ee tr) (w2n slot) tv` by
    metis_tac[storage_place_region_slots_in_range] >>
  `storage_read_live cx tr (get_storage cx ee tr) slot tv` by
    metis_tac[storage_place_region_read_live] >>
  simp[] >> irule aug_place_storage_read_ready >> metis_tac[]
QED

Theorem intcall_aug_place_storage_load_cont:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env ee sb s /\
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sb s0 ee
    (PlaceR (StoragePlace tr slot tv)) (Type ty) rp s /\
  read_place fp.jc_cx (StoragePlace tr slot tv) ee = (INL cur,ee) /\
  is_word_type ty /\ evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  slots_in_range (get_storage fp.jc_cx ee tr) (w2n slot) tv /\
  storage_read_live fp.jc_cx tr (get_storage fp.jc_cx ee tr) slot tv /\
  emit_op (if tr then TLOAD else SLOAD) [FST rp] sb = (op,sc) /\
  fn_has_code sb sc fp.jc_func /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    eval_operand op u = SOME (typed_val_to_w256 tv cur) /\
    (!x. op = Var x ==> not_fresh_at sc x) /\
    intcall_expr_cont fp ce env ee sb s ee sc u
Proof
  strip_tac >>
  `eval_operand (FST rp) s = SOME slot` by
    fs[loweringPostsTheory.target_post_def,loweringPostsTheory.place_ptr_rel_def] >>
  drule_all aug_place_storage_load_ready >> strip_tac >>
  irule intcall_emit_readonly_cont >> simp[] >>
  qexistsl [`[FST rp]`,`if tr then TLOAD else SLOAD`] >>
  Cases_on `tr` >> gvs[is_terminator_def] >>
  metis_tac[step_SLOAD,step_TLOAD]
QED
