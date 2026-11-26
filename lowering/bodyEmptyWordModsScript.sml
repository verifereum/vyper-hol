(* Empty at a word type returns the typed zero without emitting code. *)
Theory bodyEmptyWordMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShared bodyInvSplit bodyFullShadowBodyInv
  exprBodyPreProps exprSimHyps exprSimAggregates exprLoweringProps
  exprLowering loweringPosts loweringStateRelDefs exprSimMemDefs bodyPtrDefs
  gasShadow gasShadowCompileStmtHelpers gasOutcomeFullPostMods fragGasOriginPtr
  vyperStorageFootprint vyperTypeSystem vyperTyping vyperValue vyperContext
  vyperInterpreter vyperState vyperAST valueEncoding compileEnv context
  venomState loweringSlice ptrDiscipline

Theorem empty_word_ready[local]:
  expr_body_pre_mods mods cenv cx env (TypeBuiltin ann Empty typ xs) es ==>
  xs = [] /\ ann = typ /\ ?rt. evaluate_type (get_tenv cx) typ = SOME rt
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `env.type_defs = get_tenv cx` by
    fs[vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  gvs[well_typed_expr_def, well_typed_type_builtin_args_def,
      type_builtin_result_ok_def, well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  goal_assum drule
QED

Theorem empty_word_compile[local]:
  is_word_type typ ==>
  compile_expr cenv ty (TypeBuiltin typ Empty typ []) sa =
    (StackValue typ (Lit 0w),sa)
Proof
  simp[compile_expr_type_builtin_dispatch, Once compile_type_builtin_dispatch_component_eq]
QED

Theorem empty_word_shadow_compile[local]:
  is_word_type typ /\ gas_shadow_state sa sha ==>
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (TypeBuiltin typ Empty typ [])) sha =
      (StackValue typ (Lit 0w),sha)
Proof
  strip_tac >>
  `gas_shadow_compiles (compile_expr cenv ty (TypeBuiltin typ Empty typ []))
     (compile_expr (gas_shadow_env T cenv) ty
       (gas_shadow_expr (TypeBuiltin typ Empty typ [])))` by
    irule gas_shadow_stmt_compile_expr_env >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (mp_tac o Q.SPECL [`sa`, `sha`] o REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >>
  `SND (compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr (TypeBuiltin typ Empty typ [])) sha) = sha` by
    simp[gas_shadow_expr_def, empty_word_compile] >>
  simp[quantHeuristicsTheory.PAIR_EQ_EXPAND, empty_word_compile] >>
  metis_tac[]
QED

Theorem empty_word_eval[local]:
  evaluate_type (get_tenv cx) typ = SOME rt ==>
  eval_expr cx (TypeBuiltin typ Empty typ []) es = (INL (Value (default_value rt)),es)
Proof
  strip_tac >>
  simp[Once evaluate_def, evaluate_type_builtin_def, bind_def, return_def,
       lift_option_def, lift_sum_def] >>
  simp[Once evaluate_def, ignore_bind_def, type_check_def,
       type_builtin_args_length_ok_def, bind_def, return_def, assert_def]
QED

Theorem empty_word_post_frame[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  immutable_frame_mods func cenv cx es s /\
  storage_well_formed_on cx es (FST H) /\
  ghost_inv_at_mods (DF H) lo d cenv cx es G tn s ==>
  stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s /\
  immutable_frame_mods func cenv cx (es with gas_obs := []) s /\
  storage_well_formed_on cx (es with gas_obs := []) (FST H) /\
  ghost_inv_at_mods (DF H) lo d cenv cx (es with gas_obs := []) G tn s
Proof
  strip_tac >> conj_tac
  >- (drule msg_gas_state_frame >>
      disch_then (qspecl_then [`s.vs_gas_readings`, `s.vs_inst_idx`, `[]`] mp_tac) >>
      simp[]) >>
  conj_tac
  >- (qpat_assum `immutable_frame_mods _ _ _ es _` mp_tac >>
      PURE_REWRITE_TAC[immutable_frame_mods_def, immutables_rel_mods_def,
        immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
        loweringStateRelDefsTheory.immutables_rel_def, evaluation_state_accfupds] >>
      simp[]) >>
  conj_tac
  >- (`storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
       storage_well_formed_on cx es (FST H)` suffices_by simp[] >>
      irule storage_well_formed_on_backends >> simp[]) >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ es _ _ _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[ghost_inv_at_mods_def] >>
  PURE_REWRITE_TAC[evaluation_state_accfupds] >> simp[]
QED

Theorem empty_word_value_sim[local]:
  is_word_type typ /\ evaluate_type (get_tenv cx) typ = SOME rt ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin typ Empty typ []) es
Proof
  strip_tac >> rw[expr_sim_full_mods_def] >>
  `compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr (TypeBuiltin typ Empty typ [])) shadow_sa =
      (StackValue typ (Lit 0w),shadow_sa)` by
    (irule empty_word_shadow_compile >> simp[] >> goal_assum drule) >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  qpat_x_assum `lower_value _ cenv _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def,
       empty_word_compile] >> strip_tac >> strip_tac >> gvs[] >>
  drule_then assume_tac empty_word_eval >>
  drule_all_then assume_tac typed_val_to_w256_default_word >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G0`,`es`,`INL (default_value rt)`,`s0`,`tn0`] >>
  simp[bind_def, read_result_def, return_def] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac empty_word_post_frame >>
  simp[gas_origin_ptr_path_rules, expr_post_mods_def, expr_post_def,
       expr_store_bound_def, expr_val_rel_def, expr_val_at_def, expr_type_def,
       typed_val_to_w256_default_word, eval_operand_def, ptr_val_ok_def,
       op_taint_def, locals_kept_def, ghost_kept_at_def]
QED

Theorem empty_word_vv_sim[local]:
  is_word_type typ /\ evaluate_type (get_tenv cx) typ = SOME rt ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin typ Empty typ []) es
Proof
  strip_tac >> rw[expr_vv_sim_full_mods_def] >>
  `compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr (TypeBuiltin typ Empty typ [])) shadow_sa =
      (StackValue typ (Lit 0w),shadow_sa)` by
    (irule empty_word_shadow_compile >> simp[] >> goal_assum drule) >>
  gvs[empty_word_compile] >>
  drule_then assume_tac empty_word_eval >>
  drule_all_then assume_tac typed_val_to_w256_default_word >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G0`,`es`,`INL (Value (default_value rt))`,`s0`,`tn0`] >>
  simp[] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac empty_word_post_frame >>
  simp[gas_origin_ptr_path_rules, vv_post_mods_def, vv_holds_mods_def,
       vv_place_ptr_mods_def, vv_holds_def, vv_at_def, vv_storage_live_def,
       vv_place_ptr_def, vv_store_bound_def, lowered_value_type_def,
       contextTheory.vv_location_def, read_result_def, return_def,
       expr_val_rel_def, expr_val_at_def, expr_type_def, typed_val_to_w256_default_word,
       eval_operand_def, ptr_vv_ok_def, ptr_val_ok_def, op_taint_def,
       locals_kept_def, ghost_kept_at_def]
QED

Theorem empty_word_full_ok_mods:
  !mods exps cx ann typ xs. is_word_type typ ==>
    body_expr_full_ok_mods mods exps cx (TypeBuiltin ann Empty typ xs)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_expr_full_ok_mods_def] >>
  rpt gen_tac >> strip_tac >> drule_then strip_assume_tac empty_word_ready >> gvs[] >>
  conj_tac
  >- (irule empty_word_value_sim >> simp[] >> goal_assum drule) >>
  irule empty_word_vv_sim >> simp[] >> goal_assum drule
QED
