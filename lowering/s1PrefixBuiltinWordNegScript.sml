(* Request-prefix companion to bodyFullBuiltinWordNeg. *)
Theory s1PrefixBuiltinWordNeg
Ancestors
  s1PrefixPreds s1PrefixDefs s1PrefixOfVV
  exprBodyPreProps exprSimSource exprSimUnopProps exprLoweringProps
  gasShadowCompileStmtHelpers gasShadowState gasShadow fragExec
  vyperTypeSystem vyperInterpreter vyperState vyperContext list

Theorem word_neg_sim_prefix:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
  (!DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es.
       (~is_word_type (expr_type e) ==>
        !tvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) =
                SOME tvt ==> type_memory_size tvt = 0) /\
       expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx ty e es /\
       (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
       (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
       expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx ty e es) /\
  bt = Neg /\
  (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok cx args) /\
  (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin a bt args) es ==>
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `MAP expr_type args = [a]` by
    (drule expr_body_pre_static_facts >>
     simp[well_typed_expr_def, well_typed_builtin_app_def]) >>
  Cases_on `args` >> gvs[] >>
  rename1 `expr_body_pre _ _ _ (Builtin _ Neg [e]) _` >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> conj_tac
     >- metis_tac[expr_body_pre_static_facts] >>
     qexistsl [`expr_type e`, `[e]`, `Neg`, `es`] >> simp[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_x_assum `builtin_args_length_ok _ _ ==> body_exprs_prefix_ok _ _`
       mp_tac >> simp[builtin_args_length_ok_def, body_exprs_prefix_ok_def] >>
     disch_then (mp_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     metis_tac[]) >>
  conj_asm1_tac
  >- (PURE_REWRITE_TAC[expr_sim_prefix_def, expr_sim_full_pre_def] >>
      rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
      drule lower_value_neg >> strip_tac >>
      qpat_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ Neg _)) _ = _`
        (mp_tac o SIMP_RULE (srw_ss()) [gas_shadow_expr_def, gas_shadow_builtin_def]) >>
      disch_then (mp_then Any mp_tac lower_value_neg) >>
      simp[gas_shadow_expr_type] >> strip_tac >>
      rename1 `compile_neg x (expr_type e) s1 = (op,sb)` >>
      rename1 `compile_neg x' (expr_type e) s1' = (op,shadow_sb)` >>
      `cs_extends sa s1 /\ cs_extends shadow_sa s1'` by metis_tac[compile_expr_grows] >>
      `cs_extends s1 sb /\ cs_extends s1' shadow_sb` by
        metis_tac[straight_fresh_cs_extends, CONV_RULE (DEPTH_CONV ETA_CONV) straight_fresh_neg] >>
      `fn_has_code sa s1 func /\ fn_has_code shadow_sa s1' shadow_func` by
        metis_tac[fn_has_code_split] >>
      `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
         (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
           (gas_shadow_expr e))` by irule gas_shadow_stmt_lower_value_env >>
      `x' = x /\ gas_shadow_state s1 s1'` by
        (qpat_x_assum `gas_shadow_compiles _ _`
           (qspecl_then [`sa`, `shadow_sa`] mp_tac o REWRITE_RULE[gas_shadow_compiles_def]) >> simp[]) >>
      `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
        metis_tac[expr_body_pre_gas_admissible] >>
      qpat_x_assum `expr_sim_prefix _ _ _ _ e es`
        (mp_tac o REWRITE_RULE[expr_sim_prefix_def, expr_sim_full_pre_def]) >>
      disch_then (qspecl_then [`st0`, `sa`, `s1`, `shadow_sa`, `s1'`, `x`, `s0`, `G0`, `tn0`] mp_tac) >>
      simp[] >> disch_tac >>
      (* The arithmetic tail changes the result but leaves the source state intact. *)
      `!qe. SND (bind (eval_expr cx (Builtin (expr_type e) Neg [e])) (read_result cx) qe) =
            SND (bind (eval_expr cx e) (read_result cx) qe)` by
        (simp[eval_expr_unop_action] >> gen_tac >>
         Cases_on `bind (eval_expr cx e) (read_result cx) qe` >>
         rename1 `_ = (res,ee)` >> Cases_on `res` >> simp[bind_def]) >>
      drule gas_prefix_full_state_cong >> metis_tac[]) >>
  irule expr_vv_sim_stack_prefix >>
  simp[compile_neg_stack] >> metis_tac[eval_expr_builtin_value]
QED
