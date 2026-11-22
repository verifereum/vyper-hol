(* Request-prefix companion to bodyFullAttribute. *)
Theory s1PrefixAttribute
Ancestors
  s1PrefixPreds s1PrefixDefs s1PrefixOfVV bodyAttributeMemory
  bodyFullPreds exprSimAttribute exprSimUnwrap exprSimHyps fragExec
  gasShadow gasShadowState gasShadowCompile vyperState

Theorem attribute_vv_sim_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx env ty ann obj fld es.
  expr_body_pre cenv cx env (Attribute ann obj fld) es /\
  expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty obj es /\
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty obj es ==>
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Attribute ann obj fld) es
Proof
  rpt gen_tac >> strip_tac >> drule attr_pre_base >> strip_tac >>
  simp[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  drule compile_expr_attribute >> strip_tac >>
  rename1 `compile_expr cenv ty obj sa = (bvv,sm)` >>
  `fn_has_code sa sm func` by
    metis_tac[fn_has_code_split, compile_expr_extends, attr_extends] >>
  `gas_shadow_compiles (compile_expr cenv ty obj)
     (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
           Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  `?shadow_sm. compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa =
      (bvv,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`, `shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa` >>
     simp[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (qpat_assum `compile_expr _ _ (gas_shadow_expr (Attribute _ _ _)) _ = _`
       (strip_assume_tac o MATCH_MP compile_expr_attribute o
        REWRITE_RULE [gas_shadow_expr_def]) >>
     fs[] >> metis_tac[fn_has_code_split, compile_expr_extends, attr_extends]) >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  `!st. SND (eval_expr cx (Attribute ann obj fld) st) = SND (eval_expr cx obj st)` by
    (gen_tac >> Cases_on `eval_expr cx obj st` >> rename1 `_ = (res,mid)` >>
     Cases_on `res` >> simp[eval_expr_attribute, bind_def] >>
     qmatch_goalsub_rename_tac `select_result cx _ raw _ mid` >>
     qspecl_then [`cx`, `expr_type obj`, `raw`, `fld`, `mid`, `mid.gas_obs`]
       mp_tac select_attr_gas_obs >> simp[] >>
     disch_then (mp_tac o Q.AP_TERM `SND`) >> simp[]) >>
  qpat_assum `!st. SND (eval_expr cx (Attribute _ _ _) st) = _`
    (fn eq => rewrite_tac[MATCH_MP gas_prefix_full_state_cong eq]) >>
  qpat_x_assum `expr_vv_sim_prefix _ _ _ _ obj _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
                          `bvv`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> simp[]
QED

Theorem attribute_expr_prefix_ok:
  !cx v9 e id.
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_expr_prefix_ok cx (Attribute v9 e id)
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once body_expr_prefix_ok_def] >> rpt gen_tac >> strip_tac >>
  drule attr_pre_base >> strip_tac >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty e es` by
    (qpat_assum `body_expr_full_ok _ _`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     metis_tac[]) >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty e es` by
    (qpat_assum `body_expr_prefix_ok _ _`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     metis_tac[]) >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Attribute v9 e id) es` by
    metis_tac[attribute_vv_sim_prefix] >>
  simp[expr_sim_prefix_of_vv]
QED
