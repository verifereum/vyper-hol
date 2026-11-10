(* Physical source interface for compiled widened conditional arms. *)
Theory bodyIfExpCompiledAggregate
Ancestors
  bodyIfExpTypedMemory exprSimUnwrapProps exprSimMemDefs exprSimUnwrap
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
