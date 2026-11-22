(* Request-prefix companion to bodyFullBuiltinWordRoundingCase. *)
Theory s1PrefixBuiltinWordRoundingCase
Ancestors
  s1PrefixPreds bodyFullBuiltinWordRoundingCase s1PrefixDefs s1PrefixOfVV
  exprBodyPreProps exprSimWordBuiltins exprSimUnopComposeProps exprSimUnopProps
  exprSimSource gasShadowCompileStmtHelpers exprLoweringProps vyperState
  vyperContext vyperInterpreter vyperTyping vyperTypeSystem list

Theorem word_rounding_sim_prefix:
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
  (bt = Ceil \/ bt = Floor) /\
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
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `MAP expr_type args = [BaseT DecimalT]` by
    (drule expr_body_pre_static_facts >> strip_tac >>
     Cases_on `bt = Ceil` >> gvs[well_typed_expr_def, well_typed_builtin_app_def,
                                 LENGTH_EQ_NUM_compute]) >>
  `?e. args = [e]` by (Cases_on `args` >> gvs[]) >>
  qpat_x_assum `args = [e]` SUBST_ALL_TAC >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> conj_tac
     >- metis_tac[expr_body_pre_static_facts] >>
     qexistsl [`a`,`[e]`,`bt`,`es`] >> Cases_on `bt = Ceil` >> gvs[]) >>
  `bt <> Len /\ ~precompile_builtin bt /\ builtin_args_length_ok bt 1 /\
   ~is_self_codesize bt [e]` by
    (Cases_on `bt = Ceil` >>
     gvs[builtin_args_length_ok_def, precompile_builtin_def, is_self_codesize_def]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (qpat_x_assum `_ ==> body_exprs_prefix_ok _ _` mp_tac >>
     simp[body_exprs_prefix_ok_def] >>
     once_rewrite_tac[body_expr_prefix_ok_def] >> metis_tac[]) >>
  conj_asm1_tac
  >- (rewrite_tac[expr_sim_prefix_def, expr_sim_full_pre_def] >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      `!arg ce sc sd dst f.
         lower_value compile_expr ce ty (Builtin a bt [arg]) sc = (dst,sd) /\
         fn_has_code sc sd f ==>
         ?x sm. lower_value compile_expr ce ty arg sc = (x,sm) /\ fn_has_code sc sm f` by
        (rpt gen_tac >> strip_tac >> Cases_on `bt = Ceil` >> gvs[] >>
         (drule lower_value_ceil ORELSE drule lower_value_floor) >> strip_tac >>
         rename1 `lower_value _ _ _ arg sc = (x,sm)` >> qexistsl [`x`,`sm`] >> simp[] >>
         `cs_extends sm sd` by
           metis_tac[straight_fresh_ceil, straight_fresh_floor, straight_fresh_cs_extends] >>
         metis_tac[CONJUNCT2 compile_expr_grows, fragExecTheory.fn_has_code_split]) >>
      `?x sm. lower_value compile_expr cenv ty e sa = (x,sm) /\ fn_has_code sa sm func` by
        metis_tac[] >>
      `gas_shadow_expr (Builtin a bt [e]) = Builtin a bt [gas_shadow_expr e]` by
        (Cases_on `bt = Ceil` >>
         gvs[gasShadowTheory.gas_shadow_expr_def, gasShadowTheory.gas_shadow_builtin_def]) >>
      `?y shadow_sm. lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e)
                       shadow_sa = (y,shadow_sm) /\ fn_has_code shadow_sa shadow_sm shadow_func` by
        (qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` assume_tac >>
         gvs[] >> metis_tac[]) >>
      `y = x /\ gas_shadow_state sm shadow_sm` by
        (`gas_shadow_compiles (lower_value compile_expr cenv ty e)
            (lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e))` by
           irule gas_shadow_stmt_lower_value_env >>
         pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o
           REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >> simp[]) >>
      `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
        (irule unop_operand_admissible >> qexistsl [`a`,`bt`] >> simp[]) >>
      `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
         (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)` by
        (qpat_x_assum `expr_sim_prefix _ _ _ _ e _`
           (mp_tac o REWRITE_RULE [expr_sim_prefix_def,expr_sim_full_pre_def]) >>
         disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,
                                  `x`,`s0`,`G0`,`tn0`] mp_tac) >>
         simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
      `!qe. SND (bind (eval_expr cx e) (read_result cx) qe) =
            SND (bind (eval_expr cx (Builtin a bt [e])) (read_result cx) qe)` by
        (simp[eval_expr_unop_action_general] >> gen_tac >>
         Cases_on `bind (eval_expr cx e) (read_result cx) qe` >>
         rename1 `_ = (res,ee)` >> Cases_on `res` >> simp[Once bind_def]) >>
      drule gas_prefix_full_state_cong >> disch_then (irule o iffLR o SPEC_ALL) >>
      first_assum ACCEPT_TAC) >>
  irule expr_vv_sim_stack_prefix >> simp[] >>
  reverse conj_tac >- metis_tac[eval_expr_builtin_value] >>
  gen_tac >> Cases_on `compile_expr cenv ty (Builtin a bt [e]) sa` >>
  Cases_on `bt = Ceil` >> gvs[]
  >- (drule compile_ceil_stack >> strip_tac >> simp[] >> metis_tac[]) >>
  drule_at (Pos last) compile_word_builtin_stack >> simp[] >> metis_tac[]
QED
