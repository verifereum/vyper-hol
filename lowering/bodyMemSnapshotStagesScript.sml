(* Compiler slices and semantic resources for a nonword RHS snapshot. *)
Theory bodyMemSnapshotStages
Ancestors
  bodyMemSnapshotAlloc bodyMemSnapshotIdentity bodyMemSnapshotUnwrap
  exprLoweringProps exprLowering context compileEnv fragExec
  exprSimMemDefs loweringPosts valueCopyBytes exprOperandVar valueTypingMemoryProps
  venomExecSemantics venomState exprSimCopy

Theorem snapshot_nonword_slices:
  ~is_word_type (lowered_value_type ce e) /\
  compile_snapshot_vv ce T (vv_with_type (lowered_value_type ce e) vv) sm =
    (saved,sb) /\ fn_has_code sm sb func ==>
  ?buf mid src sc.
    compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) sm =
      (buf,mid) /\
    unwrap_value ce (vv_with_type (lowered_value_type ce e) vv) mid = (src,sc) /\
    compile_store_memory ce src buf.buf_operand
      (lowered_value_type ce e) (lowered_value_type ce e) sc = ((),sb) /\
    saved = LocatedValue (lowered_value_type ce e) (mk_ptr buf.buf_operand LocMemory) /\
    ci_mono sm mid /\ ci_mono mid sc /\ ci_mono sc sb /\
    fn_has_code sm mid func /\ fn_has_code mid sc func /\ fn_has_code sc sb func
Proof
  strip_tac >>
  `vv_type (vv_with_type (lowered_value_type ce e) vv) = lowered_value_type ce e` by
    (Cases_on `vv` >> simp[vv_with_type_def, vv_type_def]) >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) sm` >>
  rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  Cases_on `unwrap_value ce (vv_with_type (lowered_value_type ce e) vv) mid` >>
  rename1 `unwrap_value _ _ mid = (src,sc)` >>
  Cases_on `compile_store_memory ce src buf.buf_operand
    (lowered_value_type ce e) (lowered_value_type ce e) sc` >>
  rename1 `compile_store_memory _ _ _ _ _ sc = (ans,fin)` >>
  `ans = ()` by (Cases_on `ans` >> simp[]) >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  simp[compile_snapshot_vv_def, compile_materialize_vv_def,
       comp_bind_def, comp_return_def] >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >> strip_tac >>
  qpat_x_assum `fin = sb` SUBST_ALL_TAC >>
  `ci_mono sm mid /\ ci_mono mid sc /\ ci_mono sc sb` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_unwrap_value,
              ci_mono_compile_store_memory, pairTheory.SND] >>
  simp[] >>
  gvs[ci_mono_def] >>
  metis_tac[fn_has_code_split, cs_extends_trans]
QED

Theorem snapshot_lowered_encoding:
  post_value_type ce e = expr_type e /\ ~is_word_type (expr_type e) /\
  (lt = expr_type e \/ is_bytestring_type (expr_type e) /\
    is_bytestring_type lt /\ arg_type_fits lt (expr_type e)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) lt = SOME ltv /\
  value_has_type ltv v /\
  expr_post ctx func ce cx e es sa sc s0 ee v src s ==>
  val_wf ltv v /\ ?w. eval_operand src s = SOME w /\
    val_in_memory ltv v (w2n w) s.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_val_rel cx (expr_type e) v src s` by
    (fs[expr_post_def] >> metis_tac[]) >>
  `?w. eval_operand src s = SOME w /\ val_in_memory tv v (w2n w) s.vs_memory` by
    (fs[expr_val_rel_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[value_has_type_memory_wf] >>
  qexists_tac `w` >> simp[] >>
  metis_tac[bytestring_val_in_memory_transfer, optionTheory.SOME_11]
QED

Theorem snapshot_unwrap_source_mem:
  !ctx func ce cx e es sa sm sc s0 ee raw v vv src s dst d aid cap.
  post_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type ce e) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location <> LocMemory ==>
    lowered_value_type ce e = expr_type e) /\
  unwrap_value ce (vv_with_type (lowered_value_type ce e) vv) sm = (src,sc) /\
  read_result cx raw ee = (INL v,ee) /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
    type_memory_bytes ce (expr_type e) = type_memory_size tvt /\
    type_memory_size tvt < 2**64) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  local_ptrs_reserved ce sm /\
  (?x. dst = Var x /\ not_fresh_at sm x) /\
  eval_operand dst s = SOME d /\
  FLOOKUP s.vs_allocas aid = SOME (w2n d,cap) /\
  (!n b len. local_region ce ee.scopes s n b len ==>
    regions_disjoint (w2n d) cap b len) ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\
    expr_post ctx func ce cx e es sa sc s0 ee v src z /\
    (!w ltv. eval_operand src z = SOME w /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv ==>
      type_memory_size ltv = 0 \/ w2n w + type_memory_size ltv <= z.vs_alloca_next) /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP z.vs_allocas aid = SOME entry) /\
    pure_frame ce func ee sm s z /\ alloca_history func z /\
    s.vs_alloca_next <= z.vs_alloca_next /\ ~z.vs_halted /\
    z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    eval_operand dst z = SOME d /\
    FLOOKUP z.vs_allocas aid = SOME (w2n d,cap) /\
    (!n b len. local_region ce ee.scopes z n b len ==>
      regions_disjoint (w2n d) cap b len)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `!t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory`
  >- (drule_all snapshot_identity_unwrap_mem >> strip_tac >>
      qexists_tac `s` >> simp[] >> metis_tac[]) >>
  `?t p. vv = LocatedValue t p /\ p.ptr_location <> LocMemory` by metis_tac[] >>
  `t = expr_type e` by
    (fs[vv_post_def, vv_holds_def] >> metis_tac[]) >>
  `lowered_value_type ce e = expr_type e` by metis_tac[] >>
  gvs[vv_with_type_def, vv_operand_def] >>
  drule_all (SRULE [arithmeticTheory.ADD_COMM] snapshot_nonmemory_unwrap_mem) >> strip_tac >>
  rename1 `eval_operand (Var dp) s = SOME d` >>
  `eval_operand (Var dp) z = SOME d` by
    (simp[eval_operand_def] >>
     qpat_x_assum `!x. not_fresh_at sm x ==> _` (qspec_then `dp` mp_tac) >>
     simp[] >> gvs[eval_operand_def]) >>
  `!n b len. local_region ce ee.scopes z n b len ==>
    regions_disjoint (w2n d) cap b len` by
    (rpt strip_tac >>
     `local_region ce ee.scopes s n b len` by
       metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame] >>
     metis_tac[]) >>
  qexists_tac `z` >> simp[] >> metis_tac[optionTheory.SOME_11]
QED
