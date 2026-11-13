Theory stmtSimCustomErrorPtrUnwrap
Ancestors
  stmtSimCustomErrorPtrMaterialise stmtSimCustomErrorPtrWordMaterialise
  stmtSimCustomErrorPtrStorageMaterialise stmtSimCustomErrorPtrCodeMaterialise
  bodyPtrHashBuiltinsShaEndpoint bodyPtrAttributeCase bodyPtrAttributeAdd emitHelperProps exprSimUnwrap exprSimUnwrapProps exprLoweringProps
  exprOperandVar exprSimVVFrame fragGasSeqPtr freshWrites
  valueEncodingProps loweringPosts bodyPtrDefs exprLowering compileEnv context
  ptrDiscipline venomState finite_map words pred_set fragGasPathPtr

(* The representation-changing branches share one protected-allocation frame.
   This is deliberately independent of the custom-error tuple's contents. *)
Theorem custom_error_materialise_path_ptr[local]:
  unwrap_value ce vv sm = (op,sb) /\ ~ce.ce_is_ctor /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
    ptr_buf_ok ce e op G s) /\
  (!ty place. vv = LocatedValue ty place /\ place.ptr_location = LocMemory ==>
    ptr_buf_ok ce e place.ptr_operand G s) /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  value_has_type tv v /\ post_value_type ce e = expr_type e /\
  (lowered_value_type ce e = expr_type e \/ is_bytestring_type (expr_type e)) /\
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
    (~is_word_type (post_value_type ce e) /\ ~is_bytestring_type (expr_type e) ==> ptr_buf_ok ce e op G' t) /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> Cases_on `vv`
  >- suspend "stack" >>
  rename1 `unwrap_value ce (LocatedValue ty place) sm = (op,sb)` >>
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
  qpat_x_assum `_ \/ is_bytestring_type _` kall_tac >>
  gvs[unwrap_value_def, comp_return_def, vv_operand_def] >>
  `vv_post ctx func ce cx e es sa sb s0 ee (Value v) (StackValue t o') s` by
    metis_tac[vv_post_read_result] >>
  `ptr_val_ok cx (post_value_type ce e) v o' G tn s` by
    (gvs[ptr_vv_ok_def] >> metis_tac[]) >>
  qexistsl_tac [`G`,`tn`,`s`] >>
  gvs[ghost_kept_def] >>
  conj_tac >- metis_tac[cj 1 gas_path_ptr_rules] >>
  metis_tac[expr_post_of_vv_post_stack]
QED
Resume custom_error_materialise_path_ptr[word]:
  drule_all custom_error_word_unwrap_ptr >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  `is_word_type (post_value_type ce e)` by
    metis_tac[custom_error_vv_post_nonword] >>
  qexistsl_tac [`G'`,`tn'`,`u`] >> simp[]
QED
Resume custom_error_materialise_path_ptr[memory]:
  qpat_x_assum `_ \/ is_bytestring_type _` kall_tac >>
  `~is_word_type (expr_type e)` by
    (gvs[vv_post_def, vv_holds_def] >>
     metis_tac[valueCopyBytesTheory.is_bytestring_word_type]) >>
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
  gnvs[vv_operand_def] >>
  mp_tac (Q.INST [`nb` |-> `type_memory_bytes ce (expr_type e)`,
    `ty` |-> `expr_type e`] (SPEC_ALL custom_error_storage_unwrap_ptr)) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >> gnvs[] >>
  qexistsl_tac [`G'`,`tn'`,`t`] >> simp[] >>
  conj_tac
  >- (strip_tac >> gvs[ptr_buf_ok_def, ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `regions_disjoint (w2n w) (type_memory_bytes ce (expr_type e)) b len` by metis_tac[] >>
  `i NOTIN toplevel_copy_region (w2n w) (type_slot_size tv)` by
    (gvs[loweringStateRelDefsTheory.regions_disjoint_def,
         exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_region_def,
         type_memory_size_slots] >> decide_tac) >>
  metis_tac[])
QED
Resume custom_error_materialise_path_ptr[code]:
  gnvs[vv_operand_def] >>
  mp_tac (Q.INST [`nb` |-> `type_memory_bytes ce (expr_type e)`,
    `ty` |-> `expr_type e`] (SPEC_ALL custom_error_code_unwrap_ptr)) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >> gnvs[] >>
  qexistsl_tac [`G'`,`tn'`,`t`] >> simp[] >>
  conj_tac
  >- (strip_tac >> gvs[ptr_buf_ok_def, ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `regions_disjoint (w2n w) (type_memory_bytes ce (expr_type e)) b len` by metis_tac[] >>
  `i < w2n w \/ w2n w + type_memory_bytes ce (expr_type e) <= i` by
    (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  fs[SUBSET_DEF]
QED
Finalise custom_error_materialise_path_ptr

(* Destination construction is sequenced before materialisation. *)
Theorem custom_error_destination_path_ptr[local]:
  (if off = 0 then comp_return (Var x)
   else emit_op ADD [Var x; Lit (n2w off)]) sm = (dst,sn) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
    ptr_buf_ok ce e op G s) /\
  (!ty place. vv = LocatedValue ty place /\ place.ptr_location = LocMemory ==>
    ptr_buf_ok ce e place.ptr_operand G s) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) /\
  (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  ghost_inv d ce cx ee G tn s /\
  ptr_covers G tn x s asz /\ lookup_var x s = SOME (n2w b) /\
  not_fresh_at sm x /\ off + nb <= asz /\ b+asz < dimword (:256) /\
  fn_has_code sm sn func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  !D PG. ?H tm a y.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK a) /\
    vv_post ctx func ce cx e es sa sn s0 ee raw vv a /\
    ptr_vv_ok cx (post_value_type ce e) raw vv ee H tm a /\
    (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
      ptr_buf_ok ce e op H a) /\
    (!ty place. vv = LocatedValue ty place /\ place.ptr_location = LocMemory ==>
      ptr_buf_ok ce e place.ptr_operand H a) /\
    ghost_inv d ce cx ee H tm a /\ ghost_kept ce ee sm G tn s H tm /\
    dst = Var y /\ not_fresh_at sn y /\
    ptr_covers H tm y a nb /\ lookup_var y a = SOME (n2w (b+off)) /\
    a.vs_current_bb = sn.cs_current_bb /\
    a.vs_inst_idx = LENGTH sn.cs_current_insts /\ ~a.vs_halted /\
    a.vs_memory = s.vs_memory /\ a.vs_allocas = s.vs_allocas /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!z. not_fresh_at sm z ==> lookup_var z a = lookup_var z s /\
      FLOOKUP H z = FLOOKUP G z /\ op_taint tm (Var z) = op_taint tn (Var z))
Proof
  Cases_on `off = 0`
  >- (strip_tac >> gvs[comp_return_def] >> rpt gen_tac >>
      qexistsl_tac [`G`,`tn`,`s`] >> simp[ghost_kept_def] >>
      conj_tac >- metis_tac[cj 1 gas_path_ptr_rules] >>
      gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  strip_tac >> gvs[] >> rpt gen_tac >>
  `eval_operand (Var x) s = SOME (n2w b) /\
   eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_taint tn (Var x) = {} /\ op_taint tn (Lit (n2w off)) = {}` by
    gvs[ptr_covers_def, eval_operand_def, op_taint_def] >>
  drule_all (attribute_emit_binop_path_ptr |> SPEC_ALL
    |> Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  suspend "add"
QED

Resume custom_error_destination_path_ptr[add]:
  gvs[] >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK a)` >>
  `!z. not_fresh_at sm z ==> z <> STRING #"%" (toString sm.cs_next_var)` by
    (rpt strip_tac >> gvs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     first_x_assum (qspec_then `sm.cs_next_var` mp_tac) >> simp[]) >>
  `vv_post ctx func ce cx e es sa sn s0 ee raw vv a /\
   ptr_vv_ok cx (post_value_type ce e) raw vv ee H tm a /\
   (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
     ptr_buf_ok ce e op H a) /\
   (!ty place. vv = LocatedValue ty place /\ place.ptr_location = LocMemory ==>
     ptr_buf_ok ce e place.ptr_operand H a)` by
    (qunabbrev_tac `a` >> irule custom_error_fresh_add_transport >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `ghost_inv d ce cx ee H tm a /\ ghost_kept ce ee sm G tn s H tm` by
    (qunabbrev_tac `a` >> irule attribute_fresh_ghost_update >>
     simp[] >> qexistsl_tac [`G`,`tn`] >> simp[ghost_kept_def]) >>
  qexistsl_tac [`H`,`tm`,`a`] >>
  simp[] >>
  drule loweringShapeRulesTheory.emit_op_facts >> strip_tac >> gvs[] >>
  simp[Abbr `a`, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       wordsTheory.word_add_n2w] >>
  reverse conj_tac >- metis_tac[] >>
  simp[ptr_covers_def, Abbr `H`, attribute_add_provenance, op_prov_def,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  gvs[ptr_covers_def, wordsTheory.word_add_n2w] >>
  `b + off < dimword (:256)` by decide_tac >>
  simp[wordsTheory.w2n_n2w] >> decide_tac
QED
Finalise custom_error_destination_path_ptr

(* Complete destination-before-materialisation interface. *)
Theorem custom_error_unwrap_path_ptr:
  (if off = 0 then comp_return (Var x)
   else emit_op ADD [Var x; Lit (n2w off)]) sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,sb) /\ ~ce.ce_is_ctor /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
    ptr_buf_ok ce e op G s) /\
  (!ty place. vv = LocatedValue ty place /\ place.ptr_location = LocMemory ==>
    ptr_buf_ok ce e place.ptr_operand G s) /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  value_has_type tv v /\ post_value_type ce e = expr_type e /\
  (lowered_value_type ce e = expr_type e \/ is_bytestring_type (expr_type e)) /\
  nb = type_memory_bytes ce (expr_type e) /\ nb = type_memory_size tv /\
  nb < dimword (:256) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) /\
  ghost_inv d ce cx ee G tn s /\
  (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  ptr_covers G tn x s asz /\ lookup_var x s = SOME (n2w b) /\
  not_fresh_at sm x /\ off + nb <= asz /\ b+asz < dimword (:256) /\
  fn_has_code sm sn func /\ fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  !D PG. ?Gf tf t y.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK t) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op t /\
    ptr_val_ok cx (post_value_type ce e) v op Gf tf t /\
    (~is_word_type (post_value_type ce e) /\ ~is_bytestring_type (expr_type e) ==> ptr_buf_ok ce e op Gf t) /\
    ghost_inv d ce cx ee Gf tf t /\ ghost_kept ce ee sm G tn s Gf tf /\
    dst = Var y /\ ptr_covers Gf tf y t nb /\
    lookup_var y t = SOME (n2w (b+off)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!z. not_fresh_at sm z ==> lookup_var z t = lookup_var z s /\
      FLOOKUP Gf z = FLOOKUP G z /\ op_taint tf (Var z) = op_taint tn (Var z)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len i. aid < sm.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= i /\ i < b+len ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem ==> i IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >>
  `sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id` by
    (Cases_on `off = 0` >> gvs[comp_return_def] >>
     drule emitted_insts_emit_op >> simp[]) >>
  drule_all custom_error_destination_path_ptr >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  `local_ptrs_reserved ce sn` by metis_tac[local_ptrs_reserved_next_var] >>
  `sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id` by decide_tac >>
  `(!z. vv_operand vv = Var z ==> not_fresh_at sn z) /\
   (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sn z) /\
   (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sn z)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  drule_all custom_error_materialise_path_ptr >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  suspend "compose"
QED
Resume custom_error_unwrap_path_ptr[compose]:
  `!z. not_fresh_at sm z ==> not_fresh_at sn z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `ghost_kept ce ee sm G tn s G' tn'` by
    (irule hash_ghost_kept_then >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `ptr_covers G' tn' y t nb` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  qexistsl_tac [`G'`,`tn'`,`t`,`y`] >> simp[] >>
  conj_tac >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD] >>
  rpt gen_tac >> strip_tac >>
  `aid < sn.cs_next_id` by decide_tac >> metis_tac[]
QED
Finalise custom_error_unwrap_path_ptr
