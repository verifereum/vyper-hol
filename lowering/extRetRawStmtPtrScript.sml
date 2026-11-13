Theory extRetRawStmtPtr
Ancestors
  extRetRawValuePtr extRetStaticStmtPtr exprOperandVar extRetNormalEvidencePtr
  extRetSomeComposePtr bodyPtrDefs typedCopyPtr loweringPosts stmtSimReturn
  exprLowering exprLoweringProps gasSummaryComposePtr stmtLowering emitHelper
  emitHelperProps fragExec loweringHalt compileEnv rich_list list
  aggregateTypedCopyRawShape abiBuiltinAllocation extRetRawStagePtr
  extRetRawMemoryReturnPtr abiDecoderBytesRuntime valueEncoding context
  fragGasPathPtr words arithmetic venomExecSemantics vyperTypeSystem vyperValue venomState
  typedCopyVarFlow

Theorem external_return_raw_stmt_parts[local]:
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv',sb) /\
  fn_has_code sa sb func /\ ~block_is_terminated sa /\
  cenv.ce_return_pc = NONE /\ ~is_word_type ty /\ cenv.ce_raw_return /\
  cenv.ce_nonreentrant = (F,nkey,ut,iv) /\
  (is_bytestring_type ty /\ is_bytestring_type (lowered_value_type cenv e) \/
   lowered_value_type cenv e = ty) ==>
  ?op sm buf sn sp.
    lower_value compile_expr cenv ty e sa = (op,sm) /\
    compile_alloc_buffer (type_memory_bytes cenv ty) sm = (buf,sn) /\
    compile_store_memory_typed cenv buf.buf_operand ty op
      (lowered_value_type cenv e) sn = ((),sp) /\
    compile_external_return (SOME buf.buf_operand) F T cenv.ce_ret_enc_info
      cenv.ce_max_return_size F nkey ut iv sp = ((),sb) /\
    fn_has_code sa sm func /\ fn_has_code sm sn func /\
    fn_has_code sn sp func /\ fn_has_code sp sb func
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `compile_external_return _ _ _ _ _ _ _ _ _ sp = ((),sf)` >>
  `cs_extends sp sf` by
    (qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_external_return_def, optional_unlock_view,
          emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_id_def,
          fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
     irule cs_extends_same_block >> simp[IS_PREFIX_APPEND, GSYM APPEND_ASSOC]) >>
  drule aggregate_typed_store_extends >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  metis_tac[cs_appends_emit_helpers, cs_appends_def,
            cs_extends_trans, fn_has_code_split]
QED
Theorem external_return_raw_stmt_frag_ptr:
  cenv.ce_return_pc = NONE /\ cenv.ce_raw_return /\
  cenv.ce_nonreentrant = (F,nkey,ut,iv) /\
  ~is_word_type ty /\ ~is_word_type (expr_type e) /\
  is_bytestring_type (expr_type e) /\
  is_bytestring_type ty /\ is_bytestring_type (lowered_value_type cenv e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic k))) /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic n))) /\ k <= n /\
  type_memory_bytes cenv ty = type_memory_size (BaseTV (BytesT (Dynamic n))) /\
  type_memory_bytes cenv ty < dimword(:256) /\
  expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_expr e) /\
  post_value_type cenv e = expr_type e /\
  expr_sim_ptr d ctx PG func cenv cx ty e es ==>
  stmt_frag_ptr d ctx PG func cx lctx (\v es gt r. T) cenv
    (stmt_env cenv lctx ty (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >> rw[stmt_frag_ptr_def] >>
  drule external_return_raw_stmt_parts >> simp[] >>
  disch_then drule_all >> strip_tac >>
  drule_at (Pat `lower_value _ _ _ _ _ = _`) compile_lower_value_var >>
  simp[] >> disch_then assume_tac >>
  drule return_forced_admissible >> strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_ptr_def] >>
  disch_then (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  dxrule gas_outcome_ptr_normal_evidence >> strip_tac >>
  drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)
    external_return_some_outcome_ptr >>
  disch_then irule >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all expr_post_ptr_return_inputs >> strip_tac >>
  drule_all external_return_forced_value_typed >> strip_tac >>
  `?bs. v = BytesV bs` by
    (Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]) >>
  gvs[] >>
  `expr_val_at cenv cx (expr_type e) sa sm ee (BytesV bs) op t` by gvs[expr_post_def] >>
  `LENGTH bs <= n` by gvs[vyperTypingTheory.value_has_type_def] >>
  `32 + LENGTH bs <= type_memory_size (BaseTV (BytesT (Dynamic n))) /\
   LENGTH bs + 31 < dimword(:256) /\
   32 + 32 * ((LENGTH bs + 31) DIV 32) < dimword(:256)` by
    (drule abi_decode_bytes_round_capacity >>
     qspec_then `LENGTH bs` assume_tac (GEN_ALL abi_decode_bytes_round_bounds) >>
     gvs[type_memory_size_def, vfmConstantsTheory.word_size_def] >> decide_tac) >>
  `?src. op = Var src` by
    (qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
     simp[ptr_val_ok_def, ptr_mem_ok_def] >> strip_tac >>
     gvs[val_footprint_def] >> metis_tac[]) >> gvs[] >>
  `compile_store_memory_typed cenv buf.buf_operand ty (Var src)
      (expr_type e) sn = ((),sp)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def] >>
     simp[Once compile_store_memory_typed_def]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[] >>
     drule (cj 2 compile_expr_grows) >> simp[cs_extends_def]) >>
  `lookup_var src t = SOME w` by gvs[eval_operand_def] >>
  `value_has_type (BaseTV (BytesT (Dynamic n))) (BytesV bs)` by
    simp[vyperTypingTheory.value_has_type_def] >>
  `LENGTH bs + 31 < dimword(:256)` by decide_tac >>
  drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)
    raw_bytes_stage_counted_ptr >>
  simp[] >> disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ ty = _`)) >> simp[] >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >> simp[] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  `not_fresh_at sp dst` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule compile_store_memory_typed_next_var >> strip_tac >>
     qpat_x_assum `emit_op ALLOCA _ _ = _` mp_tac >>
     simp[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_var_def, fresh_id_def, emit_def] >> strip_tac >>
     gvs[] >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def,
          ASCIInumbersTheory.toString_inj] >>
     gvs[cs_extends_def] >> decide_tac) >>
  gvs[] >>
  drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)
    compile_external_return_raw_memory_gas_path_ptr >>
  simp[] >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (qspec_then `BaseTV (BytesT (Dynamic n))` mp_tac) >>
  simp[] >> disch_then (drule_at (Pat `_ + _ < dimword(:256)`)) >>
  simp[] >> disch_then (drule_at (Pat `LENGTH _ + 32 <= _`)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  metis_tac[gas_path_ptr_then, ADD_0]
QED
