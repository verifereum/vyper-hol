(* Memory-safe counterparts of the statement composition rules. *)
Theory stmtMemory
Ancestors
  bodyMemoryDefs stmtSim fragExecMem compileEnv stmtLowering exprSim
  exprSimHyps exprLoweringProps venomState venomExecSemantics
  vyperInterpreter vyperTypeSystem vyperState vyperExprNoControl list finite_map

Theorem compile_pass_frag_mem:
  !d ctx func cx lctx RetQ cenv ty es.
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty Pass) es
      (INL ()) es
Proof
  rw[stmt_frag_mem_def, stmt_env_def, declare_stmt_local_def, comp_bind_def,
     comp_ignore_bind_def, compile_stmt_def, comp_return_def] >>
  disj1_tac >> qexists_tac `s0` >>
  simp[stmt_lands_def, cenv_top_ext_refl] >> metis_tac[]
QED

Theorem stmt_frag_nil_mem:
  !d ctx func cx lctx RetQ cenv ty es.
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmts_env cenv lctx ty []) es
      (INL ()) es
Proof
  rw[stmt_frag_mem_def, stmts_env_def, comp_return_def] >>
  disj1_tac >> qexists_tac `s0` >>
  simp[stmt_lands_def, cenv_top_ext_refl] >> metis_tac[]
QED

Theorem stmt_frag_cons_env_mem:
  !d ctx func cx lctx RetQ cenv ty stmt ss es res es'.
    eval_stmts cx (stmt::ss) es = (res, es') /\
    (!c. cs_mono (compile_stmt c lctx ty stmt)) /\
    (!c. cs_mono (stmts_env c lctx ty ss)) /\
    (!r1 es1. eval_stmt cx stmt es = (r1, es1) ==>
       stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty stmt)
         es r1 es1) /\
    (!es1 c sa sm. eval_stmt cx stmt es = (INL (), es1) /\
                   stmt_env cenv lctx ty stmt sa = (c, sm) /\
                   cenv_top_ext cenv c es1.scopes ==>
       stmt_frag_mem d ctx func cx lctx RetQ c (stmts_env c lctx ty ss)
         es1 res es') ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmts_env cenv lctx ty (stmt::ss))
      es res es'
Proof
  cheat
QED

Theorem compile_expr_stmt_frag_ok_mem:
  !d ctx func cx lctx RetQ cenv ty e es res es'.
    eval_stmt cx (Expr e) es = (res, es') /\
    expr_vv_sim_mem ctx func cenv cx (expr_type e) e es /\
    (!sa vv sb tv es1.
       storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
       eval_expr cx e es = (INL tv, es1) /\
       compile_expr cenv (expr_type e) e sa = (vv, sb) /\
       ~block_is_terminated sa ==> ~block_is_terminated sb) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Expr e))
      es res es'
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
