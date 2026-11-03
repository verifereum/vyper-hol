(* Memory-safe counterparts of the statement composition rules. *)
Theory stmtMemory
Ancestors
  bodyMemoryDefs stmtSim fragExecMem fragExec compileEnv stmtLowering exprSim
  vyperEvalPreservesScopes
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
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_cons, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rename1 `stmt_env cenv lctx ty stmt sa = (c, sm)` >>
  drule_all stmt_env_reserved >> strip_tac >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var` by
    (qpat_x_assum `!c. cs_mono (stmts_env _ _ _ _)` (qspec_then `c` mp_tac) >>
     simp[cs_mono_def] >> metis_tac[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  Cases_on `eval_stmt cx stmt es` >> rename1 `_ = (r1, es1)` >>
  qpat_x_assum `!r1 es1. _ ==> stmt_frag_mem _ _ _ _ _ _ _ _ _ _ _`
    (qspecl_then [`r1`, `es1`] mp_tac) >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `r1` >> simp[]
  >- (
    rename1 `eval_stmt cx stmt es = (INL u, es1)` >> Cases_on `u` >> fs[] >>
    strip_tac >> simp[stmt_frag_mem_def] >>
    disch_then (qspecl_then [`sa`, `sm`, `s0`, `c`] mp_tac) >>
    simp[stmt_res_ok_def, stmt_exit_def] >> strip_tac >>
    qpat_x_assum `stmt_lands _ _ _ _`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [stmt_lands_def]) >>
    rename1 `stmt_state_rel ctx func c cx es1 s1` >>
    `ret_pc_ok c sm s1` by
      (qspecl_then [`cenv`, `c`, `sa`, `sm`, `s0`, `s1`] mp_tac
         ret_pc_ok_frame >>
       impl_tac >- (fs[] >> drule cenv_top_ext_return_pc >> simp[]) >>
       simp[]) >>
    qpat_x_assum `!c' sa' sm'. _ ==> stmt_frag_mem _ _ _ _ _ _ _ _ _ _ _`
      (qspecl_then [`c`, `sa`, `sm`] mp_tac) >>
    simp[stmt_frag_mem_def] >>
    disch_then (qspecl_then [`sm`, `sb`, `s1`, `cenv'`] mp_tac) >>
    simp[] >> strip_tac
    >- (
      disj1_tac >> rename1 `stmt_state_rel ctx func c3 cx es' s2` >>
      qexistsl_tac [`s2`, `c3`] >> simp[] >>
      `cenv_top_ext cenv c3 es'.scopes` by
        (irule cenv_top_ext_trans >> qexistsl_tac [`c`, `es1.scopes`] >>
         simp[] >> drule eval_stmts_preserves_scopes_dom >>
         rw[preserves_scopes_dom_def] >> gvs[]) >>
      `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x s2 = SOME w` by
        (rpt strip_tac >>
         `not_fresh_at sm x` by
           (fs[not_fresh_at_def] >> rw[] >> first_x_assum irule >>
            decide_tac) >> metis_tac[]) >>
      `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP s2.vs_allocas aid = SOME b` by metis_tac[] >>
      simp[] >> rpt strip_tac >> metis_tac[]) >>
    disj2_tac >>
    `!e. run_from fuel ctx func s1 <> Error e` by
      metis_tac[exit_result_not_error] >>
    qpat_x_assum `!fuel. (!e. run_from fuel ctx func s1 <> Error e) ==> _`
      drule >> strip_tac >>
    qexists_tac `fuel'` >> asm_rewrite_tac[] >> fs[stmt_exit_def]) >>
  rpt strip_tac >> gvs[stmt_frag_mem_def] >>
  first_x_assum (qspecl_then [`sa`, `sm`, `s0`, `c`] mp_tac) >>
  simp[] >> strip_tac
  >- (disj1_tac >> rename1 `stmt_state_rel ctx func c4 cx es' s4` >>
      qexistsl_tac [`s4`, `c4`] >> fs[stmt_lands_def] >>
      irule return_buf_frame_frame >>
      qexistsl_tac [`c4`, `s4`, `sm`] >> simp[]) >>
  disj2_tac >> qexists_tac `fuel` >> simp[]
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

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_COMPOSITION_KERNEL_AUDIT OK\n"
     else raise Fail "body memory composition inherited admission"
  end) [compile_pass_frag_mem, stmt_frag_nil_mem, stmt_frag_cons_env_mem, compile_expr_stmt_frag_ok_mem];
