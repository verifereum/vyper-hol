(* Physical source interface for compiled widened conditional arms. *)
Theory bodyIfExpCompiledAggregate
Ancestors
  bodyIfExpTypedMemory fragGasAllocationResources
  exprSimUnwrapProps exprSimMemDefs exprSimUnwrap
  exprSimIfExp context compileEnv exprLowering loweringPosts

Theorem ifexp_compiled_aggregate_source[local]:
  compile_expr ce ty e se = (vv,sa) /\
  sty = lowered_value_type ce e /\ dty = expr_type e /\ sty <> dty /\
  ~is_word_type sty /\ ~is_word_type dty /\
  sty = post_value_type ce e /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ 0 < type_memory_size stv /\
  read_result cx raw ee = (INL v,ee) /\
  vv_post ctx func ce cx e es origin sa s0 ee raw vv s /\
  vv_store_bound cx dty sty ee raw vv s ==>
  ?src sw. unwrap_value ce vv = comp_return src /\
    src = vv_operand vv /\
    expr_post ctx func ce cx e es origin sa s0 ee v src s /\
    eval_operand src s = SOME sw /\
    w2n sw + type_memory_size stv <= s.vs_alloca_next
Proof
  strip_tac >>
  `?src. unwrap_value ce vv = comp_return src` by
    (irule ifexp_different_type_unwrap_pure >> metis_tac[]) >>
  drule vv_post_read_result >> disch_then (fn th => fs[th]) >>
  Cases_on `vv`
  >- suspend "stack"
  >> suspend "located"
QED

Resume ifexp_compiled_aggregate_source[stack]:
  gvs[unwrap_value_def, comp_return_def, FUN_EQ_THM, vv_operand_def] >>
  `expr_post ctx func ce cx e es origin sa s0 ee v o' s` by
    metis_tac[expr_post_of_vv_post_stack] >>
  `?w. eval_operand o' s = SOME w` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  qexists_tac `w` >> simp[] >>
  fs[vv_store_bound_def] >> gvs[]
QED
Resume ifexp_compiled_aggregate_source[located]:
  `~is_word_type t` by
    (fs[vv_post_def, vv_holds_def] >>
     metis_tac[valueCopyBytesTheory.is_bytestring_word_type]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (gvs[unwrap_value_def, comp_return_def, FUN_EQ_THM, vv_operand_def] >>
      `expr_post ctx func ce cx e es origin sa s0 ee v p.ptr_operand s` by
        metis_tac[expr_post_of_vv_post_memory] >>
      `?w. eval_operand p.ptr_operand s = SOME w` by
        (fs[vv_post_def, vv_holds_def] >> metis_tac[]) >>
      qexists_tac `w` >> simp[] >> fs[vv_store_bound_def] >> gvs[]) >>
  `p.ptr_location <> LocCalldata` by
    (fs[vv_post_def, vv_holds_def] >> Cases_on `p.ptr_location` >> fs[]) >>
  `!sm. src = Var ("%" ++ toString sm.cs_next_var)` by
    (gen_tac >> qpat_x_assum `unwrap_value _ _ = _` mp_tac >>
     simp[unwrap_value_def, FUN_EQ_THM, comp_return_def] >>
     disch_then (qspec_then `sm` mp_tac) >>
     Cases_on `p.ptr_location` >> gvs[compile_ensure_in_memory_def,
       compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[]) >>
  first_assum (qspec_then `sa with cs_next_var := 0` assume_tac) >>
  first_x_assum (qspec_then `sa with cs_next_var := 1` mp_tac) >>
  gvs[] >> EVAL_TAC
QED
Finalise ifexp_compiled_aggregate_source[local]

Theorem ifexp_compiled_aggregate_arm_path_mem:
  compile_expr ce ty e se = (vv,sa) /\
  compile_ifexp_arm ce dty sty vv sa = (op,sb) /\
  sty = lowered_value_type ce e /\ dty = expr_type e /\
  sty = post_value_type ce e /\ sty <> dty /\
  ~same_memory_layout ce sty dty /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  0 < type_memory_size stv /\ type_memory_size dtv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce se /\ local_ptrs_reserved ce origin /\
  local_ptrs_reserved ce sa /\
  origin.cs_next_var <= sa.cs_next_var /\ origin.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!buf sm. compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) ==>
    (emitted_blocks sm sb <> [] ==>
      ?bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0)) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_post ctx func ce cx e es origin sa s0 ee raw vv s /\
  vv_store_bound cx dty sty ee raw vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n u w. gas_path_mem ctx func s n (OK u) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    expr_post ctx func ce cx (IfExp dty c a b) es origin sb s0 ee v op u /\
    eval_operand op u = SOME w /\
    w2n w + type_memory_size dtv <= u.vs_alloca_next /\
    vv_store_bound cx dty dty ee raw (LocatedValue dty (mk_ptr op LocMemory)) u /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    s0.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  drule_all ifexp_compiled_aggregate_source >> strip_tac >>
  `!x. src = Var x ==> not_fresh_at sa x` by
    (gvs[] >> metis_tac[exprOperandVarTheory.compiler_compile_var]) >>
  qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >>
  simp[compile_ifexp_arm_def, compile_store_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  `?n u w. gas_path_mem ctx func s n (OK u) /\
     ~u.vs_halted /\ u.vs_current_bb = cs''.cs_current_bb /\
     u.vs_inst_idx = LENGTH cs''.cs_current_insts /\
     expr_post ctx func ce cx (IfExp (expr_type e) c a b)
       es origin cs'' s0 ee v tmp.buf_operand u /\
     eval_operand tmp.buf_operand u = SOME w /\
     w2n w + type_memory_size dtv <= u.vs_alloca_next` by
    (irule ifexp_typed_normalize_post_path_mem >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`n`, `u`, `w`] >> simp[] >>
  conj_tac
  >- (simp[vv_store_bound_def, mk_ptr_def] >> rpt strip_tac >> gvs[] >>
      `val_store_size dtv v <= type_memory_size dtv` by
        (irule exprSimPropsTheory.val_store_size_le >> simp[]) >> decide_tac) >>
  `alloca_inv s` by
    fs[expr_post_def, exprLoweringPropsTheory.stmt_state_rel_def] >>
  drule_all gas_path_mem_allocation_resources >> strip_tac >>
  simp[] >> decide_tac
QED
