(* Request-prefix companion to bodyFullConvertScalarJoint. *)
Theory s1PrefixConvertScalarJoint
Ancestors
  s1PrefixPreds s1PrefixDefs s1PrefixOfVV
  exprSimConvert exprLowering exprLoweringProps gasShadowCompileStmtHelpers
  gasShadowState externalEntryShape vyperState

Theorem convert_scalar_vv_sim_prefix:
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  ~is_bytestring_type (expr_type e) /\
  ~is_bytestring_type dst ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  strip_tac >> drule expr_body_pre_convert >> strip_tac >> gvs[] >>
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
     pure_once_rewrite_tac[CONJUNCT1 compile_expr_raw_def] >>
     simp[compile_expr_body_def] >>
     pure_once_rewrite_tac[CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)] >>
     simp[compile_type_builtin_dispatch_body_def, exprCallBoundsTheory.expr_child_callback_def,
          exprBopLoweringTheory.lower_value_child_call, SF ETA_ss, vyperASTTheory.expr_type_def] >>
     rpt strip_tac >> Cases_on `ann` >> gvs[exprBopLoweringTheory.as_stack_val_pair] >>
     metis_tac[cj 1 compile_type_convert_labels, pairTheory.SND]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  (* convert_result changes only the result, not the request trace. *)
  ONCE_REWRITE_TAC[GSYM gas_prefix_full_bind_read_result] >>
  rewrite_tac[eval_expr_convert_action] >>
  `!qe. SND (bind (bind (eval_expr cx e) (read_result cx))
                (\v ee. (convert_result cx (expr_type e) ann v,ee)) qe) =
        SND (bind (eval_expr cx e) (read_result cx) qe)` by
    (gen_tac >> Cases_on `bind (eval_expr cx e) (read_result cx) qe` >>
     rename1 `_ = (res,ee)` >> Cases_on `res` >> simp[bind_def]) >>
  drule_then (fn th => once_rewrite_tac[th]) gas_prefix_full_state_cong >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (irule o REWRITE_RULE[expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`x`,`sa`,`sm`,`shadow_sa`,`shadow_sm`] >> simp[]
QED
