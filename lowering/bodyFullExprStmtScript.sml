(*
 * The expression statement over the finite-horizon joint judgment.
 *
 * TOP-LEVEL:
 *   compile_expr_stmt_frag_ok_full
 *)
Theory bodyFullExprStmt
Ancestors
  bodySimFull gasOutcomeFullStmts gasOutcomeFullCompose gasOutcomeFull
  stmtSimExpr stmtSimProps stmtSimDefs bodyMemoryDefs bodyPtrDefs
  exprSimDefs gasShadow gasShadowState loweringPosts exprLoweringProps
  stmtLowering compileEnv loweringStateRelDefs vyperInterpreter vyperState
  vyperAST list

(* Expr e is e followed by a source-only HashMapRef check: the marks, the
   target path and its endpoint stay the expression's. *)
Theorem compile_expr_stmt_frag_ok_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty e es.
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (expr_type e) e es /\
    gas_shadow_compiles (compile_expr cenv (expr_type e) e)
      (compile_expr cenv (expr_type e) (gas_shadow_expr e)) /\
    (!gs sa vv sb tv es1.
       storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
       eval_expr cx e (es with gas_obs := gs) = (INL tv, es1) /\
       compile_expr cenv (expr_type e) e sa = (vv, sb) /\
       ~block_is_terminated sa ==> ~block_is_terminated sb) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Expr e))
      (stmt_env cenv lctx ty (Expr (gas_shadow_expr e)))
      (eval_stmt cx (Expr e)) es
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[stmt_frag_full_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (Expr e) _ = _` mp_tac >>
  qpat_x_assum `stmt_env _ _ _ (Expr (gas_shadow_expr e)) _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  Cases_on `compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  simp[] >> rpt strip_tac >> gvs[] >>
  rename1 `compile_expr _ _ e sa = (vv, sm)` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) shadow_sa = (svv, shadow_sm)` >>
  `svv = vv` by
    (qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`, `shadow_sa`] mp_tac o
        REWRITE_RULE [gas_shadow_compiles_def]) >>
     simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_stmt_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
    by fs[ret_pc_ok_def] >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`, `vv`,
                           `s0`, `G0`, `tn0`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (irule o MATCH_MP
    (REWRITE_RULE [GSYM AND_IMP_INTRO] gas_outcome_full_expr_stmt)) >>
  rpt conj_tac
  >- (rpt strip_tac >> drule_all expr_stmt_not_hashmap >> simp[])
  >- (rpt strip_tac >> gvs[] >>
      `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
        fs[vv_post_def, stmt_state_rel_def, state_rel_def] >>
      `~block_is_terminated sm` by metis_tac[] >>
      `sa.cs_next_var <= sm.cs_next_var` by metis_tac[compile_expr_grows] >>
      `return_buf_frame d cenv sm t` by
        (qpat_x_assum `return_buf_frame _ _ sa s0` mp_tac >>
         rpt (pop_assum mp_tac) >> rpt strip_tac >>
         drule_then irule return_buf_frame_frame >> fs[vv_post_def]) >>
      fs[vv_post_def, ghost_kept_at_def, stmt_lands_def, cenv_top_ext_refl]) >>
  rpt gen_tac >> strip_tac >> Cases_on `res` >> fs[expr_exit_def] >>
  simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]
QED
