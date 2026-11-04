(* Counted statement-list sequencing at each actual compiled environment. *)
Theory stmtSimSeqEnv
Ancestors
  stmtSimDefs stmtSimProps loweringPosts gasOutcome gasSummary gasSummaryCompose
  gasContext gasExemptCert fragExec fragGasMode fragGasPath compileEnv loweringSlice
  stmtLowering exprLoweringProps localPtrsProps vyperInterpreter vyperState
  vyperEvalPreservesScopes list finite_map

Theorem stmt_frag_cons_env:
  !ctx func cx lctx RetQ cenv ty stmt ss es.
    (!c. cs_mono (compile_stmt c lctx ty stmt)) /\
    (!c. cs_mono (stmts_env c lctx ty ss)) /\
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty stmt)
      (eval_stmt cx stmt) es /\
    (!gs es1 c sa sm.
       eval_stmt cx stmt (es with gas_obs := gs) = (INL (), es1) /\
       stmt_env cenv lctx ty stmt sa = (c, sm) /\
       cenv_top_ext cenv c es1.scopes ==>
       stmt_frag ctx func cx lctx RetQ c (stmts_env c lctx ty ss)
         (eval_stmts cx ss) es1) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmts_env cenv lctx ty (stmt::ss)) (eval_stmts cx (stmt::ss)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
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
  qpat_x_assum `!r1 es1. _ ==> stmt_frag _ _ _ _ _ _ _ _ _ _`
    (qspecl_then [`r1`, `es1`] mp_tac) >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `r1` >> simp[]
  >- (
    (* the head completes: go on with the tail at c *)
    rename1 `eval_stmt cx stmt es = (INL u, es1)` >> Cases_on `u` >> fs[] >>
    strip_tac >> simp[stmt_frag_def] >>
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
    qpat_x_assum `!c' sa' sm'. _ ==> stmt_frag _ _ _ _ _ _ _ _ _ _`
      (qspecl_then [`c`, `sa`, `sm`] mp_tac) >>
    simp[stmt_frag_def] >>
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
            decide_tac) >>
         `lookup_var x s1 = SOME w` by res_tac >> res_tac) >>
      `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP s2.vs_allocas aid = SOME b` by
        (rpt strip_tac >> res_tac >> res_tac) >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func s2 <> Error e) ==> _`
        (qspec_then `fuel` mp_tac) >> simp[] >> strip_tac >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func s1 <> Error e) ==> _`
        (qspec_then `fuel'` mp_tac) >> impl_tac >- metis_tac[] >>
      strip_tac >> metis_tac[]) >>
    disj2_tac >>
    `!e. run_from fuel ctx func s1 <> Error e` by
      metis_tac[exit_result_not_error] >>
    qpat_x_assum `!fuel. (!e. run_from fuel ctx func s1 <> Error e) ==> _`
      drule >> strip_tac >>
    qexists_tac `fuel'` >> asm_rewrite_tac[] >> fs[stmt_exit_def]) >>
  (* the head exits, breaks or continues: the list does the same *)
  rpt strip_tac >> gvs[stmt_frag_def] >>
  first_x_assum (qspecl_then [`sa`, `sm`, `s0`, `c`] mp_tac) >>
  simp[] >> strip_tac
  >- (disj1_tac >> rename1 `stmt_state_rel ctx func c4 cx es' s4` >>
      qexistsl_tac [`s4`, `c4`] >> fs[stmt_lands_def]) >>
  disj2_tac >> qexists_tac `fuel` >> simp[]
QED
