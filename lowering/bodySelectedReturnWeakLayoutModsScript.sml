(* Reached value layouts for a linked buffered Return, without expr_body_pre_mods. *)
Theory bodySelectedReturnWeakLayoutMods
Ancestors
  bodyCopyReadPhysicalTypeMods exprBodyPreProps vyperTypeEvalCaseProofs
  bodySim allocLimits vyperTypeCallGraph vyperTypeEvalSoundness
  logArgumentTypeEval typedCopyCompatibility typedMemoryCopy
  abiEncodeMaterialize vyperTypeArgFits loweringPosts exprSimHypsDefs
  vyperTypeSystem vyperTypeExprSoundness

Theorem selected_return_annotation_read[local]:
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_expr e) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
  value_runtime_typed env (expr_type e) v
Proof
  strip_tac >>
  drule_at (Pat `bind _ _ _ = _`) (REWRITE_RULE [ETA_AX] eval_expr_read_type_sound) >>
  disch_then (qspec_then `env` mp_tac) >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
  simp[]
QED

Theorem selected_return_post_read[local]:
  value_runtime_typed env (expr_type e) v /\
  value_runtime_typed env (lowered_value_type cenv e) v ==>
  value_runtime_typed env (post_value_type cenv e) v
Proof
  strip_tac >> Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
  >- (gvs[post_value_type_def, vyperASTTheory.expr_type_def] >> IF_CASES_TAC >> gvs[]) >>
  metis_tac[post_value_type_not_int_call]
QED

Theorem selected_return_weak_layout_mods:
  expr_sim_inv_mods mods cenv cx env es /\
  stmt_exprs_ok cenv (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  ~is_word_type ret /\ evaluate_type (get_tenv cx) ret = SOME tv /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) =
    (INL v,ee) ==>
  ?stv ptv.
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv /\
    value_has_type stv v /\ value_has_type ptv v /\ value_has_type tv v /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) ret /\
    (post_value_type cenv e = lowered_value_type cenv e \/
     is_bytestring_type (post_value_type cenv e) /\
     is_bytestring_type (lowered_value_type cenv e)) /\
    arg_type_fits (lowered_value_type cenv e) (expr_type e) /\
    alloc_limits_expr cenv e
Proof
  strip_tac >>
  `well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) ret` by
    fs[type_stmt_def, AllCaseEqs()] >>
  `alloc_limits_expr cenv e` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def, alloc_limits_expr_def] >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    fs[int_calls_stmt_def, int_calls_expr_def] >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `well_formed_type env.type_defs (expr_type e)` by
    (drule_all checked_expr_type_well_formed >> simp[]) >>
  `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    (drule_all copy_lowered_fits_mods >> simp[]) >>
  `type_widens_to env.type_defs (lowered_value_type cenv e) (expr_type e)` by
    simp[type_widens_to_def] >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) ret` by
    metis_tac[type_widens_to_trans] >>
  `~is_word_type (expr_type e)` by metis_tac[return_source_word_widens_eq] >>
  `(expr_sim_inv_mods mods cenv cx env (es with gas_obs := prefix) <=>
    expr_sim_inv_mods mods cenv cx env es)` by
    simp_tac (srw_ss()) [expr_sim_inv_mods_def] >>
  `expr_sim_inv_mods mods cenv cx env (es with gas_obs := prefix)` by simp[] >>
  drule_all_then assume_tac copy_read_lowered_type_mods >>
  drule_all_then assume_tac selected_return_annotation_read >>
  drule_all_then assume_tac selected_return_post_read >>
  qpat_x_assum `value_runtime_typed env (lowered_value_type _ _) _`
    (qx_choose_then `stv` strip_assume_tac o REWRITE_RULE [value_runtime_typed_def]) >>
  qpat_x_assum `value_runtime_typed env (post_value_type _ _) _`
    (qx_choose_then `ptv` strip_assume_tac o REWRITE_RULE [value_runtime_typed_def]) >>
  qpat_x_assum `env.type_defs = get_tenv cx` SUBST_ALL_TAC >>
  `value_has_type tv v` by
    (qpat_assum `type_widens_to (get_tenv cx) (lowered_value_type _ _) ret`
       (mp_then Any mp_tac type_widens_to_value_has_type) >>
     disch_then (qspecl_then [`v`,`stv`] mp_tac) >> simp[]) >>
  qexistsl_tac [`stv`,`ptv`] >> simp[] >>
  irule materialize_post_lowered_classify >> simp[]
QED
