(* Request-prefix companion to bodyFullBuiltinUint2Str. *)
Theory s1PrefixBuiltinUint2Str
Ancestors
  s1PrefixPreds s1PrefixDefs s1PrefixOfVV
  exprSimUint2Str exprSimHash exprSimSource exprBodyPreProps
  exprLoweringProps exprSimDefs gasShadowCompileStmtHelpers gasShadowState
  gasShadow fragExec vyperContext vyperInterpreter vyperState compileEnv

Theorem uint2str_builtin_sim_prefix:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann n args es.
  (builtin_args_length_ok (Uint2Str n) (LENGTH args) ==>
     body_exprs_full_ok cx args) /\
  (builtin_args_length_ok (Uint2Str n) (LENGTH args) ==>
     body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin ann (Uint2Str n) args) es ==>
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Uint2Str n) args) es /\
    expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Uint2Str n) args) es
Proof
  rpt gen_tac >> strip_tac >>
  `well_typed_expr env (Builtin ann (Uint2Str n) args)` by
    metis_tac[expr_body_pre_static_facts] >>
  drule uint2str_expr_types >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> simp[] >>
     metis_tac[expr_body_pre_static_facts]) >>
  `body_expr_prefix_ok cx e` by
    fs[builtin_args_length_ok_def, body_exprs_prefix_ok_def] >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty e es` by
    (qpat_assum `body_expr_prefix_ok _ _`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     first_x_assum drule_all >> simp[]) >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) es` suffices_by
    metis_tac[expr_sim_prefix_of_vv] >>
  PURE_REWRITE_TAC[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule uint2str_compile_cut >>
  disch_then (qx_choose_then `op` (qx_choose_then `sm` strip_assume_tac)) >>
  `?sx ss.
     lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e)
       shadow_sa = (sx,ss) /\
     as_ptr_val (BaseT (StringT n)) LocMemory
       (compile_uint2str sx n (type_memory_bytes cenv (BaseT (StringT n))) ss) =
         (vv,shadow_sb)` by
    (qpat_x_assum `compile_expr _ _ (gas_shadow_expr (Builtin _ _ _)) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, gas_shadow_builtin_def] >>
     disch_then (mp_tac o MATCH_MP uint2str_compile_cut) >> simp[]) >>
  `sx = op /\ gas_shadow_state sm ss` by
    (qpat_x_assum `gas_shadow_state sb shadow_sb` kall_tac >>
     drule (REWRITE_RULE[gas_shadow_compiles_def] gas_shadow_stmt_lower_value_env) >>
     disch_then (qspecl_then [`ty`, `T`, `e`, `cenv`] mp_tac) >> simp[]) >>
  qpat_x_assum `sx = op` SUBST_ALL_TAC >>
  `cs_extends sm sb /\ cs_extends ss shadow_sb` by
    (mp_tac (Q.INST [`x` |-> `op`, `ann` |-> `BaseT (StringT n)`,
      `N` |-> `type_memory_bytes cenv (BaseT (StringT n))`] uint2str_code_appends) >>
     simp[cs_appends_def] >> metis_tac[]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa ss` by
    metis_tac[cj 2 compile_expr_grows] >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa ss shadow_func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ e es`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `ss`, `op`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  `eval_expr cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v mid. ((case builtin_result cx mid.accounts (BaseT (StringT n))
        (Uint2Str n) [expr_type e] [v] of
          INL r => INL (Value r) | INR ex => INR ex),mid))` by
    (irule eval_expr_unary_builtin_action >>
     simp[precompile_builtin_def, builtin_args_length_ok_def,
       is_self_codesize_def]) >>
  `!qe. SND (eval_expr cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) qe) =
        SND (bind (eval_expr cx e) (read_result cx) qe)` by
    (gen_tac >> simp[] >> Cases_on `bind (eval_expr cx e) (read_result cx) qe` >>
     rename1 `_ = (res,mid)` >> Cases_on `res` >> simp[bind_def]) >>
  metis_tac[gas_prefix_full_state_cong]
QED
