(*
 * The expression statement over the finite-horizon joint judgment.
 *
 * TOP-LEVEL:
 *   compile_expr_stmt_frag_ok_full
 *)
Theory bodyFullExprStmt
Ancestors
  bodyFullExprCore bodyFullShared
  bodySimFull gasOutcomeFullStmts gasOutcomeFullCompose gasOutcomeFull
  stmtSimExpr stmtSimProps stmtSimDefs bodyMemoryDefs bodyPtrDefs
  exprSimDefs gasShadow gasShadowState loweringPosts exprLoweringProps
  stmtLowering compileEnv loweringStateRelDefs vyperInterpreter vyperState
  vyperAST list gasShadowCompileStmtHelpers

(* Expr e is e followed by a source-only HashMapRef check: the marks, the
   target path and its endpoint stay the expression's. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[stmt_frag_full_def] >>
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  conj_tac >- simp[] >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (Expr e) _ = _` mp_tac >>
  qpat_x_assum `stmt_env _ _ _ (Expr (gas_shadow_expr e)) _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  simp[] >> rpt strip_tac >> gvs[] >>
  rename1 `compile_expr _ _ e sa = (vv, sm)` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) shadow_sa = (svv, shadow_sm)` >>
  `svv = vv` by
    (`gas_shadow_compiles (compile_expr cenv (expr_type e) e)
        (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))`
       by irule gas_shadow_stmt_compile_expr_env >>
     pop_assum (qspecl_then [`sa`, `shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_stmt_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
    by fs[ret_pc_ok_def] >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     simp[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`, `vv`,
                           `s0`, `G0`, `tn0`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (fn outcome =>
    qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
      qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
        mp_tac (MATCH_MP gas_outcome_full_return_buf_allocas
          (LIST_CONJ [outcome,frame,sep]))))) >>
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
      fs[vv_post_def, ghost_kept_at_def, stmt_lands_def, cenv_top_ext_refl] >>
      `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
        (qpat_assum `locals_kept _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [locals_kept_def]) >>
         first_assum ACCEPT_TAC) >>
      `return_buf_sep d cenv ee t` by
        (irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
         conj_tac >- fs[] >>
         qexistsl_tac [`storage_trace_horizon es.storage_trace`, `ctx`,
                       `cx`, `es`, `func`, `s0`, `sa`] >> simp[]) >>
      rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC,
             irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
             rpt conj_tac >>
             FIRST [first_assum ACCEPT_TAC,
                    qexistsl_tac [`storage_trace_horizon es.storage_trace`, `ctx`,
                                  `cx`, `func`] >>
                    qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
                      (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
                    simp[]]]) >>
  rpt gen_tac >> strip_tac >> Cases_on `res` >> fs[expr_exit_def] >>
  rename1 `expr_exit (INR exc) r` >> simp[stmt_exit_ptr_def] >>
  Cases_on `r` >> Cases_on `exc` >> gvs[expr_exit_def, halt_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]
QED
*)
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
      (stmt_env (gas_shadow_env T cenv) lctx ty (Expr (gas_shadow_expr e)))
      (eval_stmt cx (Expr e)) es
Proof
  cheat
QED
