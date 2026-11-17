Theory bodyFullLiteralWord
Ancestors
  bodySimFull gasOutcomeFullCompose exprSimSource
  exprSimLiteralWord exprSimProps exprSimHypsDefs exprLoweringProps
  exprLowering vyperTyping vyperTypeSystem loweringPosts valueEncoding
  vyperValueOperation exprSimMemDefs bodyPtrDefs gasShadow fragGasOriginPtr
  ptrDiscipline loweringSlice compileEnv vyperContext vyperAST
  vyperInterpreter vyperState vyperValue venomState list

val literal_word_posts =
  simp[vv_post_def, vv_holds_def, vv_at_def, vv_storage_live_def,
       vv_store_bound_def, lowered_value_type_def, ptr_vv_ok_def,
       contextTheory.vv_location_def, read_result_def, return_def,
       gas_origin_ptr_path_rules, expr_store_bound_def, vyperASTTheory.expr_type_def,
       is_word_type_def, ptr_val_ok_def, op_taint_def, ghost_kept_at_def,
       evaluate_literal_def] >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def, expr_type_def,
       typed_val_to_w256_word_value, word_value_def, val_to_w256_def,
       eval_operand_def, locals_kept_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def] >>
  simp[];

val literal_word_finish =
  gvs[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
      compile_literal_vv_def, unwrap_value_def, gas_shadow_expr_def,
      vyperASTTheory.expr_type_def] >> literal_word_posts;

val literal_word_vv_finish =
  qpat_x_assum `compile_expr _ _ _ sa = _` mp_tac >>
  simp[compile_expr_def, compile_literal_vv_def, comp_return_def,
       vyperASTTheory.expr_type_def] >> strip_tac >> gvs[] >>
  literal_word_posts;

Theorem literal_word_value_full:
  expr_body_pre cenv cx env (Literal ann l) es /\ is_word_type ann ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Literal ann l) es
Proof
  rw[expr_sim_full_def] >>
  `expr_sim_pre cenv cx env (Literal ann l) es` by
    simp[expr_sim_pre_body, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G0`, `es`, `INL (evaluate_literal l)`, `s0`, `tn0`] >>
  conj_tac >- simp[literal_read_all_tails] >>
  BETA_TAC >> gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  `ghost_inv_at (DF H) lo d cenv cx (es with gas_obs := []) G0 tn0 s0` by
    (qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ghost_inv_at_def] >> metis_tac[]) >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (qpat_x_assum `storage_well_formed_on _ _ _` mp_tac >>
     simp[vyperStorageFootprintTheory.storage_well_formed_on_def,
          vyperStorageBackendTheory.get_storage_def] >>
     strip_tac >> rpt gen_tac >>
     qpat_x_assum `!b slot tv. _` (qspec_then `b` mp_tac) >>
     Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  gvs[expr_sim_pre_def, well_typed_expr_def] >>
  Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  Cases_on `l` >> gvs[well_typed_literal_def, is_word_type_def] >>
  all_tac >~ [`BytesT bd`] >- (Cases_on `bd` >> gvs[is_word_type_def] >> literal_word_finish) >>
  all_tac >~ [`BoolL b`] >- (Cases_on `b` >> literal_word_finish) >>
  literal_word_finish
QED

Theorem literal_word_vv_full:
  expr_body_pre cenv cx env (Literal ann l) es /\ is_word_type ann ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Literal ann l) es
Proof
  rw[expr_vv_sim_full_def] >>
  `expr_sim_pre cenv cx env (Literal ann l) es` by
    simp[expr_sim_pre_body, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G0`, `es`, `INL (Value (evaluate_literal l))`, `s0`, `tn0`] >>
  conj_tac >- simp[Once evaluate_def, return_def] >>
  BETA_TAC >> gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  `ghost_inv_at (DF H) lo d cenv cx (es with gas_obs := []) G0 tn0 s0` by
    (qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ghost_inv_at_def] >> metis_tac[]) >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (qpat_x_assum `storage_well_formed_on _ _ _` mp_tac >>
     simp[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
     strip_tac >> rpt gen_tac >>
     qpat_x_assum `!b slot tv. _` (qspec_then `b` mp_tac) >>
     Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  gvs[expr_sim_pre_def, well_typed_expr_def] >>
  Cases_on `ann` >> gvs[well_typed_literal_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  Cases_on `l` >> gvs[well_typed_literal_def, is_word_type_def] >>
  all_tac >~ [`BytesT bd`] >- (Cases_on `bd` >> gvs[is_word_type_def] >> literal_word_vv_finish) >>
  all_tac >~ [`BoolL b`] >- (Cases_on `b` >> literal_word_vv_finish) >>
  literal_word_vv_finish
QED
