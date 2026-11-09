Theory exprSimAbiEncodeArgsMaterializePath
Ancestors
  abiEncodeMaterialize exprSimAbiGasBridge exprSimHash vyperCompiler context
  loweringPosts compileEnv finite_map

Definition materialize_owned_post_def:
  materialize_owned_post ctx func ce cx e es sa sm sb s0 es' v dst tv s <=>
    stmt_state_rel ctx func ce cx es' s /\
    wb_frame ce es es' sa s0 s /\
    expr_val_rel cx (lowered_value_type ce e) v dst s /\
    expr_val_at ce cx (lowered_value_type ce e) sa sb es' v dst s /\
    sm.cs_next_id < sb.cs_next_id /\
    ?w. eval_operand dst s = SOME w /\
        FLOOKUP s.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
        val_in_memory tv v (w2n w) s.vs_memory /\
        (!name b len. local_region ce es'.scopes s name b len ==>
           w2n w + type_memory_size tv <= b \/ b + len <= w2n w)
End

Theorem materialize_owned_post_returndata:
  materialize_owned_post ctx func ce cx e es sa sm sb s0 es' v dst tv
    (s with vs_returndata := rd) <=>
  materialize_owned_post ctx func ce cx e es sa sm sb s0 es' v dst tv s
Proof
  Cases_on `dst` >>
  simp[materialize_owned_post_def, hash_returndata_state_rel,
       wb_frame_def, expr_val_rel_def, expr_val_at_def,
       locals_kept_def, popped_kept_def, local_region_def, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def]
QED

Theorem compile_materialize_vv_owned_path:
  compile_materialize_vv ce (lowered_value_type ce e) vv sm = (dst,sb) /\
  expr_body_pre ce cx env e es_pre /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  read_result cx tvv es' = (INL v,es') /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
         ~is_word_type (post_value_type ce e) ==>
         type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
         type_memory_size tvt < 2 ** 64) /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\
  type_memory_size tv + 64 < dimword (:256) /\
  cs_extends sm sb /\ frag_gas_free sm sb /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path F ctx func r 0 (OK t) /\
      materialize_owned_post ctx func ce cx e es sa sm sb s0 es' v dst tv t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all compile_materialize_vv_owned_sim >>
  disch_then (qspec_then `\r. F` mp_tac) >>
  rewrite_tac[GSYM materialize_owned_post_def] >> strip_tac >>
  drule frag_exec_gas_path >>
  disch_then (qspecl_then [`func`, `r`] mp_tac) >>
  simp[materialize_owned_post_returndata]
QED

Theorem materialize_extends:
  compile_materialize_vv ce ty vv sa = (dst,sb) ==> cs_extends sa sb
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`ce`, `ty`, `vv`, `sa`]
    exprLoweringPropsTheory.ci_mono_compile_materialize_vv) >>
  simp[exprLoweringPropsTheory.ci_mono_def]
QED

Theorem materialize_stack_gas_free:
  compile_materialize_vv ce ty (StackValue vty op) sa = (dst,sb) /\
  (!l. op <> Label l) ==> frag_gas_free sa sb
Proof
  Cases_on `is_word_type ty` >> Cases_on `is_bytestring_type ty` >>
  Cases_on `type_memory_bytes ce ty` >>
  simp[exprLoweringTheory.compile_materialize_vv_def, exprLoweringTheory.unwrap_value_def,
       contextTheory.compile_store_memory_def,
       contextTheory.compile_alloc_buffer_def,
       contextTheory.compile_store_bytestring_def,
       contextTheory.compile_bytestring_copy_len_def,
       contextTheory.compile_copy_memory_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
       compileEnvTheory.emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> strip_tac >> gvs[] >>
  simp[frag_gas_free_def, frag_code_def, fragExecTheory.emitted_blocks_def,
       exprLoweringPropsTheory.emitted_insts_def, rich_listTheory.DROP_APPEND, arithmeticTheory.SUB_PLUS,
       arithmeticTheory.SUB_EQ_0, venomInstTheory.mk_inst_def]
QED

Theorem materialize_memory_gas_free:
  compile_materialize_vv ce ty (LocatedValue vty p) sa = (dst,sb) /\
  ~is_word_type vty /\ p.ptr_location = LocMemory /\
  (!l. p.ptr_operand <> Label l) ==> frag_gas_free sa sb
Proof
  strip_tac >> irule materialize_stack_gas_free >>
  qexistsl_tac [`ce`, `dst`, `p.ptr_operand`, `ty`, `vty`] >> simp[] >>
  gvs[exprLoweringTheory.compile_materialize_vv_def,
      exprLoweringTheory.unwrap_value_def, comp_bind_def]
QED
