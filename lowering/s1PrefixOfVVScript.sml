(* Reading a result contributes no additional storage trace. *)
Theory s1PrefixOfVV
Ancestors
  s1PrefixDefs exprSimMemorySource exprSimStack exprSimUnwrap
  gasShadowCompile gasShadowCompileBase gasShadowState
  compileEnv exprLowering exprLoweringProps exprOperandVar fragExec vyperState pair

Theorem gas_prefix_full_state_cong:
  (!qe. SND (source qe) = SND (source' qe)) ==>
  (gas_prefix_full P cx st0 source (es,s,G,tn) <=>
   gas_prefix_full P cx st0 source' (es,s,G,tn))
Proof
  strip_tac >>
  PairCases_on `P` >> PURE_REWRITE_TAC[gas_prefix_full_def] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >>
  eq_tac >> rpt strip_tac >>
  qpat_assum `!tail res ee obs_pre rq outcome sfx H. _ ==> request_site _ _ _ _ _ _ _`
    (qspec_then `tail` irule) >>
  metis_tac[pairTheory.PAIR, pairTheory.SND]
QED

Theorem gas_prefix_full_bind_read_result:
  gas_prefix_full P cx st0 (bind source (read_result cx)) (es,s,G,tn) <=>
  gas_prefix_full P cx st0 source (es,s,G,tn)
Proof
  `!qe. SND (bind source (read_result cx) qe) = SND (source qe)` by
    (gen_tac >> Cases_on `source qe` >> rename1 `_ = (res,ee)` >>
     Cases_on `res` >> simp[bind_def] >>
     rename1 `SND (read_result cx raw ee) = ee` >>
     Cases_on `read_result cx raw ee` >> drule read_result_state >> simp[]) >>
  irule gas_prefix_full_state_cong >> simp[]
QED

Theorem expr_sim_prefix_of_vv:
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty e es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty e es
Proof
  strip_tac >> PURE_REWRITE_TAC[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_x_assum `lower_value compile_expr cenv ty e sa = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv,sm)` >>
  simp[] >> strip_tac >>
  qpat_x_assum `lower_value compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  pairarg_tac >>
  rename1 `compile_expr _ _ (gas_shadow_expr _) _ = (shadow_vv,shadow_sm)` >>
  simp[gasShadowCompileBaseTheory.unwrap_value_gas_shadow_env] >> strip_tac >>
  `shadow_vv = vv /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (compile_expr cenv ty e)
       (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e))` by
       irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
              Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
     qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     simp[]) >>
  gvs[] >>
  `cs_extends sa sm /\ cs_extends sm sb /\
   cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by
    metis_tac[compile_expr_extends, unwrap_value_extends] >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  rewrite_tac[gas_prefix_full_bind_read_result] >>
  qpat_x_assum `expr_vv_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def]) >>
  disch_then (qspecl_then
    [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`shadow_vv`,`s0`,`G0`,`tn0`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem expr_vv_sim_stack_prefix:
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es /\
  (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
  (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es
Proof
  rw[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  qpat_x_assum `!sa. ?t op sb. _` (qspec_then `sa` strip_assume_tac) >>
  gvs[] >>
  `lower_value compile_expr cenv ty e sa = (op,sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  `lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa =
     (op,shadow_sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[eval_expr_force_admissible] >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  disch_then (qspecl_then
    [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  simp[gas_prefix_full_bind_read_result] >> metis_tac[]
QED
