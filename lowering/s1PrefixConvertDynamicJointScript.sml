(* Request-prefix companion to bodyFullConvertDynamicJoint. *)
Theory s1PrefixConvertDynamicJoint
Ancestors
  s1PrefixPreds s1PrefixDefs s1PrefixOfVV
  exprSimConvertFromBytes exprSimConvert exprSimSource
  externalEntryShape gasShadowCompileStmtHelpers gasShadowState
  exprLoweringProps exprLowering compileEnv vyperAST vyperState

Theorem convert_dynamic_vv_sim_prefix:
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  is_bytestring_type (expr_type e) /\
  ~is_bytestring_type dst ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  strip_tac >> drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  `well_formed_type env.type_defs ann` by metis_tac[dynamic_convert_typing_boundary] >>
  `is_word_type ann /\ (!n. ann <> FlagT n)` by (drule_all dynamic_scalar_type >> simp[]) >>
  `?bt. ann = BaseT bt` by (Cases_on `ann` >> gvs[is_word_type_def]) >> gvs[] >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_prefix_ok _ _` mp_tac >>
     simp[Once body_expr_prefix_ok_def] >> metis_tac[]) >>
  rewrite_tac[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (x,sm)` >>
  `?shadow_sm. lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) shadow_sa = (x,shadow_sm) /\
      gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
       (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
         (gas_shadow_expr e))` by irule gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o
                REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa` >> simp[]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    metis_tac[compile_expr_grows] >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    (qpat_x_assum `compile_expr _ _ (TypeBuiltin _ _ _ _) _ = _` mp_tac >>
     qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gasShadowTheory.gas_shadow_expr_def, gasShadowTheory.gas_shadow_expr_type] >>
     simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
     simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
     simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
          compile_type_builtin_dispatch_body_def, exprCallBoundsTheory.expr_child_callback_def] >>
     simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
          compile_type_builtin_dispatch_body_def, exprCallBoundsTheory.expr_child_callback_def] >>
     simp[exprBopLoweringTheory.lower_value_child_call, SF ETA_ss, expr_type_def] >>
     rpt strip_tac >>
     Cases_on `lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
               lowered_value_type cenv e = BaseT (StringT 0)` >>
     gvs[exprBopLoweringTheory.as_stack_val_pair] >>
     metis_tac[cj 1 externalEntryShapeTheory.compile_type_convert_labels,
       pairTheory.SND, compileEnvTheory.cs_extends_refl]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  (* Neither conversion branch adds any source gas observations. *)
  ONCE_REWRITE_TAC[GSYM gas_prefix_full_bind_read_result] >>
  rewrite_tac[eval_expr_convert_action] >>
  `!qe. SND (bind (bind (eval_expr cx e) (read_result cx))
                (\v ee. (convert_result cx (expr_type e) (BaseT bt) v,ee)) qe) =
        SND (bind (eval_expr cx e) (read_result cx) qe)` by
    (gen_tac >> Cases_on `bind (eval_expr cx e) (read_result cx) qe` >>
     rename1 `_ = (res,ee)` >> Cases_on `res` >> simp[bind_def]) >>
  drule_then (fn th => once_rewrite_tac[th]) gas_prefix_full_state_cong >>
  first_assum ACCEPT_TAC
QED
