Theory extRetRawStmtPtr
Ancestors
  extRetRawValuePtr extRetStaticStmtPtr exprOperandVar extRetNormalEvidencePtr
  extRetSomeComposePtr bodyPtrDefs typedCopyPtr loweringPosts stmtSimReturn
  exprLowering exprLoweringProps gasSummaryComposePtr stmtLowering emitHelper
  emitHelperProps fragExec loweringHalt compileEnv rich_list list

Theorem external_return_raw_stmt_parts[local]:
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv',sb) /\
  fn_has_code sa sb func /\ ~block_is_terminated sa /\
  cenv.ce_return_pc = NONE /\ ~is_word_type ty /\ cenv.ce_raw_return /\
  cenv.ce_nonreentrant = (F,nkey,ut,iv) /\
  (is_bytestring_type ty /\ is_bytestring_type (lowered_value_type cenv e) \/
   lowered_value_type cenv e = ty) ==>
  ?op sm.
    lower_value compile_expr cenv ty e sa = (op,sm) /\
    compile_external_return (SOME op) F T cenv.ce_ret_enc_info
      cenv.ce_max_return_size F nkey ut iv sm = ((),sb) /\
    fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `cs_extends cs'' cs'` by
    (qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_external_return_def, optional_unlock_view,
          emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_id_def,
          fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
     irule cs_extends_same_block >> simp[IS_PREFIX_APPEND, GSYM APPEND_ASSOC]) >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule_all fn_has_code_split >> simp[]
QED

Theorem external_return_raw_stmt_frag_ptr:
  cenv.ce_return_pc = NONE /\ cenv.ce_raw_return /\
  cenv.ce_nonreentrant = (F,nkey,ut,iv) /\
  ~is_word_type ty /\ ~is_word_type (expr_type e) /\
  (is_bytestring_type ty /\ is_bytestring_type (lowered_value_type cenv e) \/
   lowered_value_type cenv e = ty) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic k))) /\
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
  drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)
    compile_external_return_raw_value_gas_path_ptr >>
  simp[] >> disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then drule_all >> simp[]
QED
