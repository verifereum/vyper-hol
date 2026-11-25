(* Discarding an expression result preserves its storage trace. *)
Theory s1PrefixExprStmt
Ancestors
  s1PrefixDefs s1PrefixOfVV stmtSimExpr gasShadowCompileStmtHelpers gasShadow gasShadowState
  loweringPosts compileEnv stmtLowering vyperInterpreter vyperState pair

Theorem compile_expr_stmt_frag_ok_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty e es.
    expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es ==>
    stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Expr e))
      (stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (Expr e)))
      (eval_stmt cx (Expr e)) es
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (Expr e) _ = _` mp_tac >>
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
  simp[gas_shadow_stmt_def, stmt_env_def, declare_stmt_local_def,
       compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) shadow_sa` >>
  simp[] >> rpt strip_tac >> gvs[] >>
  rename1 `compile_expr _ _ e sa = (vv,sm)` >>
  rename1 `compile_expr _ _ (gas_shadow_expr _) shadow_sa = (svv,shadow_sm)` >>
  `svv = vv` by
    (`gas_shadow_compiles (compile_expr cenv (expr_type e) e)
        (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))`
       by irule gas_shadow_stmt_compile_expr_env >>
     pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_stmt_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  qpat_x_assum `expr_vv_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,
                           `s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!qe. SND (eval_stmt cx (Expr e) qe) = SND (eval_expr cx e qe)` by
    (gen_tac >> simp[Once evaluate_def] >>
     Cases_on `eval_expr cx e qe` >> rename1 `_ = (res,ee)` >>
     Cases_on `res` >>
     simp[bind_def, type_check_def, assert_def, return_def, raise_def] >>
     Cases_on `is_HashMapRef x` >> simp[bind_def, return_def, raise_def]) >>
  metis_tac[gas_prefix_full_state_cong]
QED
