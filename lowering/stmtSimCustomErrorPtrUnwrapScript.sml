Theory stmtSimCustomErrorPtrUnwrap
Ancestors
  stmtSimCustomErrorPtrMaterialise stmtSimCustomErrorPtrWordMaterialise
  stmtSimCustomErrorPtrStorageMaterialise stmtSimCustomErrorPtrCodeMaterialise
  bodyPtrAttributeCase exprSimUnwrap exprSimUnwrapProps exprLoweringProps
  exprOperandVar exprSimVVFrame fragGasSeqPtr freshWrites
  valueEncodingProps loweringPosts bodyPtrDefs exprLowering compileEnv context
  ptrDiscipline venomState finite_map words pred_set fragGasPathPtr

(* The representation-changing branches share one protected-allocation frame.
   This is deliberately independent of the custom-error tuple's contents. *)
Theorem custom_error_materialise_path_ptr[local]:
  unwrap_value ce vv sm = (op,sb) /\ ~ce.ce_is_ctor /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  ptr_buf_ok ce e (vv_operand vv) G s /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  value_has_type tv v /\ post_value_type ce e = expr_type e /\
  lowered_value_type ce e = expr_type e /\
  nb = type_memory_bytes ce (expr_type e) /\ nb = type_memory_size tv /\
  nb < dimword (:256) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ghost_inv d ce cx ee G tn s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  !D PG. ?G' tn' t.
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op t /\
    ptr_val_ok cx (post_value_type ce e) v op G' tn' t /\
    (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G' t) /\
    ghost_inv d ce cx ee G' tn' t /\ ghost_kept ce ee sm G tn s G' tn' /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len i. aid < sm.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= i /\ i < b+len ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tn'.t_mem ==> i IN tn.t_mem))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `vv`
  >- suspend "stack" >>
  rename1 `LocatedValue ty place` >>
  Cases_on `is_word_type ty`
  >- suspend "word" >>
  Cases_on `place.ptr_location = LocMemory`
  >- suspend "memory" >>
  `ty = expr_type e` by gvs[vv_post_def, vv_holds_def] >>
  `~is_word_type (post_value_type ce e)` by metis_tac[] >>
  Cases_on `place.ptr_location`
  >- gvs[]
  >- suspend "storage"
  >- suspend "storage"
  >- suspend "code" >>
  gvs[vv_post_def, vv_holds_def]
QED

Resume custom_error_materialise_path_ptr[stack]:
  gvs[unwrap_value_def, comp_return_def, vv_operand_def] >>
  `vv_post ctx func ce cx e es sa sb s0 ee (Value v) (StackValue t o') s` by
    metis_tac[vv_post_read_result] >>
  qexistsl_tac [`G`,`tn`,`s`] >>
  simp[ghost_kept_def] >>
  conj_tac >- metis_tac[cj 1 gas_path_ptr_rules] >>
  conj_tac >- metis_tac[expr_post_of_vv_post_stack] >>
  gvs[ptr_vv_ok_def]
QED
Resume custom_error_materialise_path_ptr[word]:
  drule_all custom_error_word_unwrap_ptr >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  `is_word_type (post_value_type ce e)` by
    metis_tac[custom_error_vv_post_nonword] >>
  qexistsl_tac [`G'`,`tn'`,`u`] >> simp[]
QED
Resume custom_error_materialise_path_ptr[memory]:
  gvs[unwrap_value_def, comp_return_def, vv_operand_def] >>
  `vv_post ctx func ce cx e es sa sb s0 ee (Value v) (LocatedValue ty place) s` by
    metis_tac[vv_post_read_result] >>
  `expr_post ctx func ce cx e es sa sb s0 ee v place.ptr_operand s` by
    metis_tac[expr_post_of_vv_post_memory] >>
  qexistsl_tac [`G`,`tn`,`s`] >> simp[ghost_kept_def] >>
  conj_tac >- metis_tac[cj 1 gas_path_ptr_rules] >>
  gvs[ptr_vv_ok_def, ptr_val_ok_def] >>
  gvs[vv_post_def, vv_holds_def] >>
  metis_tac[valueCopyBytesTheory.is_bytestring_word_type]
QED
Resume custom_error_materialise_path_ptr[storage]:
  markerLib.RESUME_TAC >> (
  `place.ptr_location = LocStorage \/ place.ptr_location = LocTransient` by simp[] >>
  gvs[vv_operand_def] >>
  mp_tac (Q.INST [`nb` |-> `type_memory_bytes ce (expr_type e)`,
    `ty` |-> `expr_type e`] (SPEC_ALL custom_error_storage_unwrap_ptr)) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >> gvs[] >>
  qexistsl_tac [`G'`,`tn'`,`t`] >> simp[] >>
  conj_tac
  >- (gvs[ptr_buf_ok_def, ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `regions_disjoint (w2n w) (type_memory_bytes ce (expr_type e)) b len` by metis_tac[] >>
  `i NOTIN toplevel_copy_region (w2n w) (type_slot_size tv)` by
    (gvs[loweringStateRelDefsTheory.regions_disjoint_def,
         exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_region_def,
         type_memory_size_slots] >> decide_tac) >>
  metis_tac[])
QED
Resume custom_error_materialise_path_ptr[code]:
  gvs[vv_operand_def] >>
  mp_tac (Q.INST [`nb` |-> `type_memory_bytes ce (expr_type e)`,
    `ty` |-> `expr_type e`] (SPEC_ALL custom_error_code_unwrap_ptr)) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >> gvs[] >>
  qexistsl_tac [`G'`,`tn'`,`t`] >> simp[] >>
  conj_tac
  >- (gvs[ptr_buf_ok_def, ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `regions_disjoint (w2n w) (type_memory_bytes ce (expr_type e)) b len` by metis_tac[] >>
  `i < w2n w \/ w2n w + type_memory_bytes ce (expr_type e) <= i` by
    (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  fs[SUBSET_DEF]
QED
Finalise custom_error_materialise_path_ptr
