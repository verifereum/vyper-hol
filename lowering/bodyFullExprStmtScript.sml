(*
 * Helpers for the expression-statement case of the full body induction
 * (bodySimFullMain): Expr e evaluates e and drops its value, so the
 * statement's joint outcome is the expression's, with the same GAS marks,
 * target execution and pointer ghosts.
 *
 * TOP-LEVEL:
 *   compile_expr_stmt_frag_ok_full -- the joint twin of stmtFragPtr's
 *     compile_expr_stmt_frag_ok_ptr, with the gas-shadow compile
 *     correspondence for e as a premise
 *
 * Helper:
 *   gas_outcome_full_expr_stmt -- the expression's joint outcome is the
 *     statement's
 *)
Theory bodyFullExprStmt
Ancestors
  bodyFullPreds bodySimFull gasOutcomeFull fragGasOriginPtr fragGasOrigin
  fragGasMode fragGasPath stmtSimExpr stmtSimProps stmtSimDefs bodyMemoryDefs
  bodyPtrDefs exprSimDefs gasShadow gasShadowState loweringPosts
  exprLoweringProps stmtLowering compileEnv
  bodyExprPreFacts bodySimStmtCases bodySim gasContext supportedStmts
  supportedStmtTraverse vyperTypeSystem vyperInterpreter vyperState vyperAST
  list

val _ = Parse.hide "body";

(* Expr e is e followed by a source-only HashMapRef check: the marks, the
   target path and its endpoint stay the expression's. *)
Theorem gas_outcome_full_expr_stmt:
  !D lo explicit ctx func PG tops cx e es s G tn Q R Q' R'.
    gas_outcome_full (D, lo, explicit, ctx, func, PG) tops (eval_expr cx e)
      (es, s, G, tn) Q R /\
    (!gs tv ee. eval_expr cx e (es with gas_obs := gs) = (INL tv, ee) ==>
                ~is_HashMapRef tv) /\
    (!gs res ee G' tn' t.
       eval_expr cx e (es with gas_obs := gs) = (res, ee) /\
       Q res ee G' tn' t /\ ~t.vs_halted ==>
       ?tv. res = INL tv /\ Q' (INL ()) ee G' tn' t) /\
    (!res ee gt r. R res ee gt r ==>
                   ?exc. res = INR exc /\ R' (INR exc) ee gt r) ==>
    gas_outcome_full (D, lo, explicit, ctx, func, PG) tops
      (eval_stmt cx (Expr e)) (es, s, G, tn) Q' R'
Proof
  rewrite_tac[gas_outcome_full_def] >> rpt strip_tac >>
  qexists_tac `marks`
  >- (disj1_tac >>
      `~t.vs_halted` by
        metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase,
                  gas_marked_path_exec, gas_path_normal] >>
      qpat_assum `!tail. eval_expr _ _ (_ with gas_obs := _ ++ tail) = _`
        (qspec_then `[]` (assume_tac o SIMP_RULE std_ss [APPEND_NIL])) >>
      qpat_x_assum `!gs res ee G' tn' t. _ /\ _ /\ _ ==> _`
        (drule_all_then strip_assume_tac) >> gvs[] >>
      qexistsl_tac [`INL ()`, `ee`, `OK t`, `G'`, `tn'`] >> simp[] >>
      gen_tac >> irule eval_expr_stmt_success >> metis_tac[])
  >- (disj1_tac >>
      qpat_x_assum `!res ee gt r. R _ _ _ _ ==> _`
        (drule_then strip_assume_tac) >> gvs[] >>
      qexistsl_tac [`INR exc`, `ee`, `r`, `G'`, `tn'`] >> simp[] >>
      metis_tac[eval_expr_stmt_exception]) >>
  disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
  simp[] >> irule expr_stmt_exempt >> simp[]
QED

(* The shadow compilation of e returns the same value as e's: Expr drops
   it, so the statement's paired compilations alone cannot say so. *)
Theorem compile_expr_stmt_frag_ok_full:
  !D lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty e es.
    expr_vv_sim_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (expr_type e) e es /\
    gas_shadow_compiles (compile_expr cenv (expr_type e) e)
      (compile_expr cenv (expr_type e) (gas_shadow_expr e)) /\
    (!gs sa vv sb tv es1.
       storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
       eval_expr cx e (es with gas_obs := gs) = (INL tv, es1) /\
       compile_expr cenv (expr_type e) e sa = (vv, sb) /\
       ~block_is_terminated sa ==> ~block_is_terminated sb) ==>
    stmt_frag_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Expr e))
      (stmt_env cenv lctx ty (Expr (gas_shadow_expr e)))
      (eval_stmt cx (Expr e)) es
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[stmt_frag_full_def] >>
  rpt gen_tac >> strip_tac >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[stmt_state_rel_def, state_rel_def] >>
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
  disch_then (qspecl_then [`sa`, `sm`, `shadow_sa`, `shadow_sm`, `vv`,
                           `s0`, `G0`, `tn0`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (irule o MATCH_MP
    (REWRITE_RULE [GSYM AND_IMP_INTRO] gas_outcome_full_expr_stmt)) >>
  rpt conj_tac
  >- (rpt strip_tac >> drule_all expr_stmt_not_hashmap >> simp[])
  >- (rpt strip_tac >> gvs[] >>
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
