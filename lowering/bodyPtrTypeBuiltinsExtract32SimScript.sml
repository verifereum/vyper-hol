Theory bodyPtrTypeBuiltinsExtract32Sim
Ancestors
  bodyPtrTypeBuiltinsExtract32Prefix bodyPtrTypeBuiltinsExtract32Callback
  exprSimExtract32Source exprSimExtract32ReadyFacts exprPtrUnwrap
  gasSummaryComposePtr bodyPtrDefs bodyPtrPreds exprSimHypsDefs
  exprLowering exprLoweringProps loweringPosts compileEnv vyperAST vyperTypeSystem

Theorem extract32_ready_expr_vv_sim_ptr:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx [src;off] /\
  expr_body_pre cenv cx env (TypeBuiltin ann Extract32 typ [src;off]) es /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\ is_uint_type (expr_type off) ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin ann Extract32 typ [src;off]) es
Proof
  strip_tac >> simp[expr_vv_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  rewrite_tac[compile_extract32_stages] >>
  Cases_on `lower_value compile_expr cenv (expr_type src) src sa` >>
  rename1 `_ = (srcop,sx)` >> simp[] >>
  Cases_on `compile_bytestring_src srcop sx` >>
  PairCases_on `q` >> rename1 `_ = ((lenop,dataop),sm)` >> simp[] >>
  Cases_on `lower_value compile_expr cenv ty off sm` >>
  rename1 `_ = (offop,sc)` >> simp[] >>
  Cases_on `compile_extract32_load lenop dataop offop sc` >>
  rename1 `_ = (raw,sd)` >> simp[] >>
  Cases_on `compile_clamp_basetype raw typ sd` >>
  rename1 `_ = (op,se)` >>
  simp[as_stack_val_def, comp_bind_def, comp_return_def] >> strip_tac >> gvs[] >>
  irule extract32_operands_ptr_prefix >> simp[is_uint_type_def] >>
  qpat_assum `lower_value _ _ _ src _ = _` (irule_at Any) >>
  qpat_assum `compile_bytestring_src _ _ = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ off _ = _` (irule_at Any) >>
  qpat_assum `compile_extract32_load _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_clamp_basetype _ _ _ = _` (irule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`tops`,`env`] >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `is_uint_type (expr_type off)` by simp[is_uint_type_def] >>
  `lower_value compile_expr cenv (expr_type src) src sa = (Var sv,sx)` by simp[] >>
  `ptr_mem_ok cx (expr_type src) (BytesV bs) (Var sv) J un v` by simp[] >>
  drule_all extract32_callback_ptr_ready >>
  strip_tac >> gvs[] >> irule gas_outcome_ptr_conseq >>
  qpat_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  `is_word_type ann` by
    (drule extract32_body_pre_shape >> strip_tac >> gvs[] >>
     metis_tac[extract32_ready_result_word, extract32_ready_result_evaluates]) >>
  simp[expr_type_def] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  gvs[expr_type_def, vv_post_def, vv_holds_def, vv_at_def, vv_own_def, ptr_vv_ok_def] >>
  gvs[]
QED
