(* Request-prefix companion to bodyFullBuiltinWordAbsCase. *)
Theory s1PrefixBuiltinWordAbsCase
Ancestors
  s1PrefixPreds bodyFullBuiltinWordAbsCase s1PrefixDefs s1PrefixOfVV
  exprSimHypsDefs vyperTypeSystem exprSimSource vyperContext exprSimUnopProps
  gasShadowCompileStmtHelpers exprSimUnopComposeProps vyperState exprLoweringProps list

Theorem word_abs_sim_prefix:
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
  bt = Abs /\
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
  `MAP expr_type args = [BaseT (IntT 256)]` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  Cases_on `args` >> gvs[] >>
  rename1 `expr_body_pre _ _ _ (Builtin _ Abs [e]) _` >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> conj_tac
     >- gvs[expr_body_pre_def] >>
     qexistsl [`a`, `[e]`, `Abs`, `es`] >> simp[]) >>
  conj_asm1_tac
  >- (`expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx ty e es` by
        (fs[builtin_args_length_ok_def, body_exprs_prefix_ok_def] >>
         fs[Once body_expr_prefix_ok_def] >> metis_tac[]) >>
      rw[expr_sim_prefix_def, expr_sim_full_pre_def] >>
      qpat_assum `lower_value compile_expr _ _ (Builtin _ Abs _) _ = _`
        (mp_then Any strip_assume_tac lower_value_abs) >>
      qpat_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ Abs _)) _ = _`
        (mp_tac o SIMP_RULE (srw_ss()) [gasShadowTheory.gas_shadow_expr_def,
           gasShadowTheory.gas_shadow_builtin_def]) >>
      disch_then (mp_then Any strip_assume_tac lower_value_abs) >>
      rename1 `lower_value compile_expr cenv ty e sa = (x,s1)` >>
      rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = (_,shadow_s1)` >>
      `gas_shadow_compiles (lower_value compile_expr cenv ty e)
          (lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e))` by
        irule gas_shadow_stmt_lower_value_env >>
      qpat_x_assum `gas_shadow_compiles _ _`
        (qspecl_then [`sa`, `shadow_sa`] mp_tac o REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >>
      simp[] >> strip_tac >> gvs[] >>
      `fn_has_code sa s1 func /\ fn_has_code shadow_sa shadow_s1 shadow_func` by
        metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows,
          straight_fresh_abs, straight_fresh_cs_extends, fragExecTheory.fn_has_code_split] >>
      `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
        (irule unop_operand_admissible >> qexistsl [`a`,`Abs`] >>
         simp[builtin_args_length_ok_def, vyperInterpreterTheory.precompile_builtin_def,
              vyperContextTheory.is_self_codesize_def]) >>
      qpat_x_assum `expr_sim_prefix _ _ _ _ e _`
        (mp_tac o REWRITE_RULE [expr_sim_prefix_def, expr_sim_full_pre_def]) >>
      disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`shadow_s1`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
      simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
      (* Even on overflow the Abs suffix leaves the source state unchanged. *)
      `!st. SND (bind (eval_expr cx (Builtin a Abs [e])) (read_result cx) st) =
            SND (bind (eval_expr cx e) (read_result cx) st)` by
        (simp[eval_expr_unop_action] >> gen_tac >>
         Cases_on `bind (eval_expr cx e) (read_result cx) st` >>
         rename1 `_ = (res,mid)` >> Cases_on `res` >> simp[bind_def]) >>
      drule gas_prefix_full_state_cong >>
      disch_then (fn th => rewrite_tac[th]) >> simp[]) >>
  irule expr_vv_sim_stack_prefix >>
  simp[compile_not_abs_stack] >> metis_tac[eval_expr_builtin_value]
QED
