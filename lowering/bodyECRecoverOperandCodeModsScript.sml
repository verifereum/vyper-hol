(* Paired ECRecover compiler cut after the four word operands, before allocation. *)
Theory bodyECRecoverOperandCodeMods
Ancestors
  bodyFullWordArgs exprSimPrecompiles exprSimFullBundleProps exprLoweringProps
  exprLowering builtinMisc compileEnv context fragExec gasShadowState gasShadow
  vyperAST list

Theorem ecrecover_operand_code_mods:
  ann = BaseT AddressT /\ LENGTH args = 4 /\
  lower_value compile_expr cenv ty (Builtin ann ECRecover args) sa = (res,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin ann ECRecover args)) shadow_sa = (shadow_res,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) ==>
  ?h v r sig sf shadow_sf.
    lower_word_args cenv (\e. ty) args sa = ([h;v;r;sig],sf) /\
    lower_word_args (gas_shadow_env T cenv) (\e. ty) (MAP gas_shadow_expr args)
      shadow_sa = ([h;v;r;sig],shadow_sf) /\
    compile_ecrecover h v r sig sf = (res,sb) /\
    compile_ecrecover h v r sig shadow_sf = (shadow_res,shadow_sb) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sf,shadow_sa,shadow_sf) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sf,sb,shadow_sf,shadow_sb) /\
    ci_mono sa sf /\ ci_mono shadow_sa shadow_sf
Proof
  strip_tac >>
  drule_all_then strip_assume_tac expr_sim_full_code_fields >>
  drule_all_then strip_assume_tac lower_value_ecrecover_args >>
  `?hh hv hr hs cut.
     lower_word_args (gas_shadow_env T cenv) (\e. ty) (MAP gas_shadow_expr args)
       shadow_sa = ([hh;hv;hr;hs],cut) /\
     compile_ecrecover hh hv hr hs cut = (shadow_res,shadow_sb)` by
    (irule lower_value_ecrecover_args >>
     fs[gas_shadow_expr_def,gas_shadow_builtin_def] >>
     qexists `ann` >> simp[]) >>
  rename1 `lower_word_args cenv (\e. ty) args sa = ([h;v;r;sig],sf)` >>
  rename1 `lower_word_args (gas_shadow_env T cenv) _ _ shadow_sa = (_,shadow_sf)` >>
  `gas_shadow_compiles (lower_word_args cenv (\e. ty) args)
    (lower_word_args (gas_shadow_env T cenv) (\e. ty) (MAP gas_shadow_expr args))` by
    simp[gas_shadow_compiles_lower_word_args] >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (mp_tac o Q.SPECL [`sa`,`shadow_sa`] o REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[] >> strip_tac >> gvs[] >>
  imp_res_tac ci_mono_lower_word_args >>
  imp_res_tac compile_ecrecover_extends >>
  `cs_extends sa sf /\ cs_extends shadow_sa shadow_sf` by fs[ci_mono_def] >>
  `fn_has_code sa sf func /\ fn_has_code sf sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_sa shadow_sf shadow_func /\ fn_has_code shadow_sf shadow_sb shadow_func` by
    (irule fn_has_code_split >> simp[]) >>
  simp[expr_sim_full_code_def]
QED
