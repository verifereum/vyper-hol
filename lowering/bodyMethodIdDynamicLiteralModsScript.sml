(* A recognized MethodId compiles and evaluates as a four-byte literal.
   Reuse the linked literal's allocated endpoint, not a singleton post. *)
Theory bodyMethodIdDynamicLiteralMods
Ancestors
  bodyAllocLiteralMods bodyFullPredsMods bodyFullPostsMods exprSimHypsDefs
  exprSimHash gasShadow allocLimits loweringPosts bodyPtrDefs
  vyperTypeSystem vyperInterpreter vyperState vyperValue vyperAST
  exprLowering compileEnv vyperValueOperation vyperTypeCallGraph
  supportedExprTraverse supportedProgram list vyperTypeBytesCrypto

Theorem method_id_dynamic_eval[local]:
  method_id_literal (Literal la l) = SOME bs ==>
  eval_expr cx (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) =
  eval_expr cx (Literal (BaseT (BytesT (Dynamic 4)))
    (BytesL (TAKE 4 (Keccak_256_w64 bs))))
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `eval_expr cx (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) x` >>
  drule_all eval_expr_method_id_literal >>
  simp[Once evaluate_def, return_def, evaluate_literal_def]
QED

Theorem method_id_dynamic_compile[local]:
  method_id_literal (Literal la l) = SOME bs ==>
  compile_expr cenv ty (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) =
  compile_expr cenv ty (Literal (BaseT (BytesT (Dynamic 4)))
    (BytesL (TAKE 4 (Keccak_256_w64 bs))))
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  drule compile_expr_method_id_literal >> disch_then (rewrite_tac o single) >>
  simp[Once compile_expr_def, expr_type_def]
QED

Theorem method_id_dynamic_shadow[local]:
  method_id_literal (Literal la l) = SOME bs ==>
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l])) =
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Literal (BaseT (BytesT (Dynamic 4)))
      (BytesL (TAKE 4 (Keccak_256_w64 bs)))))
Proof
  simp[gas_shadow_expr_def, gas_shadow_builtin_def, method_id_dynamic_compile]
QED

Theorem method_id_dynamic_literal_pre[local]:
  expr_body_pre_mods mods cenv cx env
    (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) es ==>
  expr_body_pre_mods mods cenv cx env
    (Literal (BaseT (BytesT (Dynamic 4))) (BytesL (TAKE 4 (Keccak_256_w64 bs)))) es
Proof
  simp[expr_body_pre_mods_def, well_typed_expr_def, well_typed_literal_def,
       well_formed_type_def, compatible_bound_def, alloc_limits_expr_def,
       literal_alloc_ok_def, LENGTH_TAKE, LENGTH_Keccak_256_w64,
       vfmConstantsTheory.word_size_def, vyperValueTheory.evaluate_type_def,
       byte_widths_expr_def, int_calls_expr_def, expr_has_evm_run_thm,
       supported_expr_exists_def, const_name_root_mods_def,
       unallocated_bare_global_root_def, expr_abi_decode_target_root_def]
QED

Theorem method_id_dynamic_literal_sim_mods:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env
    (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) es /\
  method_id_literal (Literal la l) = SOME bs ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) es
Proof
  strip_tac >>
  qabbrev_tac `e = Literal (BaseT (BytesT (Dynamic 4))) (BytesL (TAKE 4 (Keccak_256_w64 bs)))` >>
  `body_expr_full_ok_mods mods exps cx e` by
    simp[Abbr `e`, alloc_literal_full_ok_mods, is_word_type_def] >>
  `expr_body_pre_mods mods cenv cx env e es` by
    (drule method_id_dynamic_literal_pre >> simp[Abbr `e`]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (qpat_x_assum `body_expr_full_ok_mods _ _ _ e` mp_tac >>
     simp[Once body_expr_full_ok_mods_def, Abbr `e`] >>
     disch_then (irule_at Any) >> simp[] >>
     conj_tac >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  `LENGTH (TAKE 4 (Keccak_256_w64 bs)) = 4` by simp[LENGTH_TAKE, LENGTH_Keccak_256_w64] >>
  drule_then assume_tac method_id_dynamic_eval >>
  drule_then assume_tac method_id_dynamic_compile >>
  drule_then assume_tac method_id_dynamic_shadow >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ e _` mp_tac >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ e _` mp_tac >>
  simp[Abbr `e`, expr_sim_full_mods_def, expr_vv_sim_full_mods_def,
       lower_value_def, expr_post_mods_def, expr_post_def, vv_post_mods_def,
       ptr_buf_ok_def, expr_type_def, lowered_value_type_def] >>
  ntac 2 disch_tac >> conj_tac >> first_assum ACCEPT_TAC
QED
