(* The real and shadow compiler cuts for one ECRecover operand. *)
Theory bodyECRecoverOperandConsCodeMods
Ancestors
  bodyFullWordArgs exprBodyPreProps exprLoweringProps exprSimFullBundleProps
  exprSimWordArgs exprWordOperand fragExec gasShadowCompileStmtHelpers
  vyperTypeEvalCaseProofs exprSimSource vyperTypeSystem

Theorem ecrecover_operand_cons_code_mods:
  lower_word_args cenv (\e. ty) (e::rest) sa = (xs,sb) /\
  lower_word_args (gas_shadow_env T cenv) (\e. ty)
    (MAP gas_shadow_expr (e::rest)) shadow_sa = (xs,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) /\
  expr_body_pre_mods mods cenv cx env e es /\ is_word_type (expr_type e) ==>
  ?x ys s1 shadow_s1. xs = x::ys /\
    lower_value compile_expr cenv ty e sa = (x,s1) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr e) shadow_sa = (x,shadow_s1) /\
    lower_word_args cenv (\e. ty) rest s1 = (ys,sb) /\
    lower_word_args (gas_shadow_env T cenv) (\e. ty)
      (MAP gas_shadow_expr rest) shadow_s1 = (ys,shadow_sb) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,s1,shadow_sa,shadow_s1) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (s1,sb,shadow_s1,shadow_sb) /\
    sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
    (!l. x <> Label l) /\ (!z. x = Var z ==> not_fresh_at s1 z)
Proof
  simp[lower_word_args_cons, expr_sim_full_code_def] >> strip_tac >> gvs[] >>
  `gas_shadow_state s1 s1'` by
    (mp_tac (Q.INST [`sd` |-> `T`, `ty` |-> `ty`] gas_shadow_stmt_lower_value_env) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >>
     simp[well_formed_type_def]) >>
  drule_all_then strip_assume_tac lower_value_word_shape >>
  qpat_assum `lower_value compile_expr (gas_shadow_env T _) _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP (cj 2 compile_expr_grows)) >>
  qpat_assum `lower_word_args cenv _ _ _ = _`
    (strip_assume_tac o MATCH_MP (REWRITE_RULE [ci_mono_def] ci_mono_lower_word_args)) >>
  qpat_assum `lower_word_args (gas_shadow_env T _) _ _ _ = _`
    (strip_assume_tac o MATCH_MP (REWRITE_RULE [ci_mono_def] ci_mono_lower_word_args)) >>
  simp[] >> rpt conj_tac >> metis_tac[fn_has_code_mid, compileEnvTheory.cs_extends_refl]
QED
