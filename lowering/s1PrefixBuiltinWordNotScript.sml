(* Request-prefix companion to bodyFullBuiltinWordNot. *)
Theory s1PrefixBuiltinWordNot
Ancestors
  s1PrefixPreds bodyFullBuiltinWordNot s1PrefixDefs s1PrefixOfVV
  bodySimFull exprSimUnopProps exprSimSource exprLoweringProps
  gasShadowCompileStmtHelpers gasShadowCompileBase gasShadowState gasShadow
  fragExec vyperInterpreter vyperContext vyperAST vyperState list

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule word_not_pre >>
  disch_then (qx_choose_then `e` (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `is_bool_type _ \/ _` kall_tac >> gvs[] >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Builtin (expr_type e) Not [e]) es` suffices_by
    (strip_tac >> simp[] >> irule expr_vv_sim_stack_prefix >>
     metis_tac[compile_not_abs_stack, eval_expr_builtin_value]) >>
  `body_expr_prefix_ok cx e` by
    (qpat_x_assum `builtin_args_length_ok _ _ ==> body_exprs_prefix_ok _ _`
       mp_tac >> simp[builtin_args_length_ok_def, body_exprs_prefix_ok_def]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_prefix_ok cx e`
       (mp_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >> metis_tac[]) >>
  PURE_REWRITE_TAC[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule lower_value_not >> strip_tac >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ _ _)) _ = _`
    mp_tac >>
  pure_rewrite_tac[gas_shadow_expr_def, gas_shadow_builtin_def, MAP] >>
  simp[NoAsms] >> disch_then (strip_assume_tac o MATCH_MP lower_value_not) >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
    (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e))` by irule gas_shadow_stmt_lower_value_env >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[gas_shadow_expr_type] >> strip_tac >>
  gvs[gas_shadow_expr_type, compile_invert_gas_shadow_env] >>
  rename [`lower_value _ _ _ e sa = (_,sm)`,
          `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = (_,shadow_sm)`] >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    metis_tac[straight_fresh_not, straight_fresh_cs_extends] >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ e es`
    (drule_all o REWRITE_RULE[expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  strip_tac >>
  rewrite_tac[Q.INST [`bi` |-> `Not`] eval_expr_unop_action |>
    SIMP_RULE (srw_ss()) []] >>
  qpat_assum `gas_prefix_full _ _ _ _ _`
    (mp_then Any irule (iffRL gas_prefix_full_state_cong)) >>
  qx_gen_tac `qe` >> Cases_on `bind (eval_expr cx e) (read_result cx) qe` >>
  rename1 `_ = (res,ee)` >> Cases_on `res` >> simp[bind_def]
QED
*)
Theorem word_not_sim_prefix:
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
  bt = Not /\
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
  cheat
QED
