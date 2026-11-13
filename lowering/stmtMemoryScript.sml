(* Memory-safe counterparts of the statement composition rules. *)
Theory stmtMemory
Ancestors
  stmtSimZero stmtSimPass stmtSimSeqMem
  exprSimMemDefs stmtSimDefs loweringPosts gasOutcome gasSummary gasContext
  allocaHistory exprSimProps stmtSimExpr stmtSimProps
  bodyMemoryDefs fragExecMem fragExec compileEnv loweringStateRelDefs stmtLowering exprSimDefs
  vyperEvalPreservesScopes
  exprLoweringProps venomState venomExecSemantics
  vyperInterpreter vyperTypeSystem vyperState vyperExprNoControl list finite_map

Theorem compile_expr_stmt_frag_ok_mem:
  !d ctx func cx lctx RetQ cenv ty e es.
    expr_vv_sim_mem ctx func cenv cx (expr_type e) e es /\
    (!gs sa vv sb tv es1.
       storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
       eval_expr cx e (es with gas_obs := gs) = (INL tv, es1) /\
       compile_expr cenv (expr_type e) e sa = (vv, sb) /\
       ~block_is_terminated sa ==> ~block_is_terminated sb) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Expr e))
      (eval_stmt cx (Expr e)) es
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >>
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >> gvs[] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_stmt_admissible] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sb`, `vv`, `s0`] mp_tac) >>
  impl_tac >- gs[] >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> BETA_TAC >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      `eval_stmt cx (Expr e) =
       bind (eval_expr cx e)
         (\tv. type_check (~is_HashMapRef tv) "Expr HashMapRef")` by
        simp[Once evaluate_def] >>
      pop_assum SUBST1_TAC >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >>
      simp[vyperStorageTraceTheory.storage_trace_frame_checks])
  >- (qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      qpat_x_assum `r = _` SUBST_ALL_TAC >>
      Cases_on `res`
      >- (rename1 `gas_marked_exec _ _ _ _ _ (INL tv) _ _` >> qexistsl_tac [`INL ()`, `es_end`, `OK t`] >>
          conj_tac
          >- (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
                (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
              simp[gas_marked_exec_def] >> gen_tac >>
              qpat_x_assum `!tail. eval_expr _ _ _ = _`
                (qspec_then `tail` assume_tac) >>
              metis_tac[expr_stmt_not_hashmap, eval_expr_stmt_success]) >>
          disj1_tac >> qexists_tac `t` >> conj_tac >- simp[] >>
          suspend "ok") >>
      qexistsl_tac [`INR y`, `es_end`, `OK t`] >>
      conj_tac
      >- (fs[gas_marked_exec_def] >> metis_tac[eval_expr_stmt_exception]) >>
      disj1_tac >> qexists_tac `t` >> conj_tac >- simp[] >>
      rpt strip_tac >> first_x_assum drule >> simp[])
  >- (qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      Cases_on `res`
      >- (rename1 `gas_marked_exec _ _ _ _ _ (INL tv) _ _` >> qexistsl_tac [`INL ()`, `es_end`, `r`] >>
          conj_tac
          >- (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
                (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
              simp[gas_marked_exec_def] >> gen_tac >>
              qpat_x_assum `!tail. eval_expr _ _ _ = _`
                (qspec_then `tail` assume_tac) >>
              metis_tac[expr_stmt_not_hashmap, eval_expr_stmt_success]) >>
          disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
          rpt strip_tac >> first_x_assum drule >> simp[expr_exit_def]) >>
      qexistsl_tac [`INR y`, `es_end`, `r`] >>
      conj_tac
      >- (fs[gas_marked_exec_def] >> metis_tac[eval_expr_stmt_exception]) >>
      disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> first_x_assum drule >> simp[stmt_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  metis_tac[expr_stmt_exempt]
QED

Resume compile_expr_stmt_frag_ok_mem[ok]:
  rpt strip_tac >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
     strip_tac >> drule fragGasPathMemTheory.gas_path_mem_exec >>
     strip_tac >> metis_tac[fragGasPathTheory.gas_path_normal]) >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL tv, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> ?tv. _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- gs[] >> strip_tac >> gvs[] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[vv_post_def, stmt_state_rel_def, state_rel_def] >>
  `~block_is_terminated sb` by metis_tac[] >>
  `ci_mono sa sb` by
    metis_tac[cj 1 compile_expr_ci_mono, pairTheory.SND] >>
  fs[vv_post_def, stmt_lands_def, cenv_top_ext_refl, ci_mono_def] >>
  irule return_buf_frame_frame >>
  qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]
QED

Finalise compile_expr_stmt_frag_ok_mem

(* Original fixed-result proof retained for migration reference:
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >>
  strip_tac >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, type_check_def, assert_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (r1, es1)` >>
  strip_tac >>
  `expr_vv_res_ok r1` by (
    Cases_on `r1` >> gvs[stmt_res_ok_def]
    >- (rename1 `is_HashMapRef tv` >> Cases_on `tv` >>
        gvs[expr_vv_res_ok_def, expr_res_ok_def]) >>
    imp_res_tac (cj 1 eval_expr_no_control) >>
    gvs[no_control_exc_def, expr_vv_res_ok_def, expr_res_ok_def]) >>
  `r1 <> INR (Error (RuntimeError "convert empty bytes to signed"))` by
    (strip_tac >> gvs[]) >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `vv`, `r1`, `es1`, `s0`] mp_tac) >>
  impl_tac >- fs[] >>
  simp[frag_exec_mem_def] >>
  disch_then (qspec_then `func` mp_tac) >> impl_tac >- fs[] >> strip_tac
  >- (gvs[vv_post_def] >> Cases_on `is_HashMapRef tv` >>
      gvs[stmt_res_ok_def] >>
      disj1_tac >> rename1 `stmt_state_rel ctx func cenv cx _ s1` >>
      qexists_tac `s1` >>
      simp[stmt_lands_def, cenv_top_ext_refl] >>
      conj_tac >- metis_tac[] >>
      `ci_mono sa sb` by metis_tac[cj 1 compile_expr_ci_mono, pairTheory.SND] >>
      fs[ci_mono_def] >> irule return_buf_frame_frame >>
      qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]) >>
  disj2_tac >> qexists_tac `fuel` >> gvs[stmt_exit_def] >>
  Cases_on `r1` >> gvs[] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED
*)

