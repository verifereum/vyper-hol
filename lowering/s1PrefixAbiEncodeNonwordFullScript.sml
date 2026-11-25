(* Request-prefix companion to bodyFullAbiEncodeNonwordFull. *)
Theory s1PrefixAbiEncodeNonwordFull
Ancestors
  s1PrefixPreds bodyFullAbiEncodeNonwordFull s1PrefixDefs s1PrefixOfVV
  exprSimAbiEncodeRuntimeInputs exprSimHyps exprLowering exprLoweringProps
  gasShadow gasShadowState gasShadowCompileHelpers gasShadowCompileStmtHelpers
  compileEnv fragExec vyperState stmtSimForArrayFrame list

Theorem abi_encode_nonword_vv_prefix_from_packaging:
  body_inv tops ctx ce cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  ~is_word_type (expr_type e) ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        ce cx cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) es
Proof
  strip_tac >>
  `expr_body_pre ce cx env e es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx (expr_type e) e es` by
    (qpat_assum `body_expr_prefix_ok cx e`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     metis_tac[]) >>
  rewrite_tac[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `compile_expr _ _ (TypeBuiltin _ _ _ _) sa = _`)
    compile_abi_encode_body_layout >>
  disch_then (drule_then strip_assume_tac) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) shadow_sa = _`
    (assume_tac o REWRITE_RULE [gas_shadow_expr_def]) >>
  drule_at (Pat `compile_expr _ _ (TypeBuiltin _ _ _ _) shadow_sa = _`)
    compile_abi_encode_body_layout >>
  disch_then (drule_then strip_assume_tac) >>
  Cases_on `compile_expr ce (expr_type e) e sa` >>
  rename1 `compile_expr ce _ e sa = (ev,si)` >>
  Cases_on `compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) shadow_sa = (hev,hsi)` >>
  `hev = ev /\ gas_shadow_state si hsi` by
    (mp_tac (Q.INST [`cenv` |-> `ce`, `ty` |-> `expr_type e`, `sd` |-> `T`]
       gas_shadow_stmt_compile_expr_env) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `hev = ev` SUBST_ALL_TAC >>
  `ci_mono si st /\ ci_mono hsi st'` by
    (qpat_x_assum `compile_abi_encode_args _ _ _ sa = _` mp_tac >>
     qpat_x_assum `compile_abi_encode_args _ _ _ shadow_sa = _` mp_tac >>
     simp[compile_abi_encode_args_def, compile_ext_call_args_def,
          comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
     metis_tac[ci_mono_compile_snapshot_vv, pairTheory.SND]) >>
  `fn_has_code sa si func /\ fn_has_code shadow_sa hsi shadow_func` by
    metis_tac[ci_mono_def, exprSimUnwrapTheory.compile_expr_extends, fn_has_code_split] >>
  `!s. SND (eval_expr cx (TypeBuiltin ann (AbiEncode F mid) ty [e]) s) =
       SND (eval_expr cx e s)` by
    (gen_tac >>
     `SND (eval_expr cx (TypeBuiltin ann (AbiEncode F mid) ty [e]) s) =
      SND (eval_exprs cx [e] s)` by
       (simp[eval_expr_abi_encode_action] >>
        Cases_on `eval_exprs cx [e] s` >> rename1 `_ = (res,ee)` >>
        Cases_on `res` >> simp[bind_def]) >>
     Cases_on `eval_expr cx e s` >>
     drule_then strip_assume_tac eval_exprs_singleton_end_state >> simp[]) >>
  qpat_assum `!s. SND (eval_expr cx (TypeBuiltin _ _ _ _) s) = _`
    (fn eq => rewrite_tac[MATCH_MP gas_prefix_full_state_cong eq]) >>
  qpat_x_assum `expr_vv_sim_prefix _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`si`,`shadow_sa`,`hsi`,`ev`,`s0`,`G0`,`tn0`] mp_tac) >>
  simp[] >> metis_tac[expr_body_pre_vv_gas_admissible]
QED
