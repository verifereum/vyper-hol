(* Counted pointer-safe statement composition over stmt_frag_ptr: an
 * expression statement, and a statement list, the head's ghost post
 * feeding the tail's pre.
 *
 * TOP-LEVEL:
 *   compile_expr_stmt_frag_ok_ptr -- the twin of stmtSimExpr's
 *     compile_expr_stmt_frag_ok
 *   stmt_frag_cons_env_ptr -- the twin of stmtSimSeqEnv's
 *     stmt_frag_cons_env
 *   ghost_inv_jump_to -- the ghost ignores the control position
 *)
Theory stmtFragPtr
Ancestors
  bodyPtrDefs gasSummaryComposePtr fragGasPathPtr
  stmtSimDefs stmtSimSeqEnv stmtSimExpr stmtSimProps loweringPosts exprSimDefs
  gasOutcome gasSummary gasSummaryCompose gasContext gasExemptCert
  fragGasMode fragGasPath fragExec compileEnv loweringSlice stmtLowering
  exprLoweringProps localPtrsProps vyperInterpreter vyperState
  vyperEvalPreservesScopes venomState list finite_map

(* The ghost invariant ignores the control position (jump_to, say). *)
Theorem ghost_inv_jump_to:
  ghost_inv d cenv cx es G tn
    (s with <| vs_prev_bb := p; vs_current_bb := l; vs_inst_idx := i |>) <=>
  ghost_inv d cenv cx es G tn s
Proof
  simp[ghost_inv_def, ptr_covers_def, stor_taint_ok_def, lookup_var_def] >>
  Cases_on `d` >> TRY (PairCases_on `x`) >>
  simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem cenv_top_ext_return_buf:
  !cenv c sc. cenv_top_ext cenv c sc ==> c.ce_return_buf = cenv.ce_return_buf
Proof
  rw[cenv_top_ext_def] >>
  qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem cenv_top_ext_is_ctor:
  !cenv c sc. cenv_top_ext cenv c sc ==> (c.ce_is_ctor <=> cenv.ce_is_ctor)
Proof
  rw[cenv_top_ext_def] >>
  qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem not_fresh_at_mono:
  not_fresh_at sa x /\ sa.cs_next_var <= sm.cs_next_var ==>
  not_fresh_at sm x
Proof
  rw[not_fresh_at_def] >> first_x_assum irule >> simp[]
QED

Theorem ghost_inv_gas_obs:
  ghost_inv d cenv cx (es with gas_obs := gs) G tn s <=>
  ghost_inv d cenv cx es G tn s
Proof
  simp[ghost_inv_def]
QED

Theorem stmt_frag_cons_env_ptr:
  !d ctx PG func cx lctx RetQ cenv ty stmt ss es.
    (!c. cs_mono (compile_stmt c lctx ty stmt)) /\
    (!c. cs_mono (stmts_env c lctx ty ss)) /\
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ty stmt) (eval_stmt cx stmt) es /\
    (!gs es1 c sa sm.
       eval_stmt cx stmt (es with gas_obs := gs) = (INL (), es1) /\
       stmt_env cenv lctx ty stmt sa = (c, sm) /\
       cenv_top_ext cenv c es1.scopes ==>
       stmt_frag_ptr d ctx PG func cx lctx RetQ c (stmts_env c lctx ty ss)
         (eval_stmts cx ss) es1) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmts_env cenv lctx ty (stmt::ss)) (eval_stmts cx (stmt::ss)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_cons, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rename1 `stmt_env cenv lctx ty stmt sa = (c, sm)` >>
  drule_all stmt_env_reserved >> strip_tac >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var` by
    (qpat_x_assum `!c. cs_mono (stmts_env _ _ _ _)` (qspec_then `c` mp_tac) >>
     simp[cs_mono_def] >> metis_tac[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_stmt cx stmt) (stmt_res_ok lctx) es` by
    (irule gas_admissible_stmts_head >> qexists_tac `ss` >> simp[]) >>
  qpat_x_assum `stmt_frag_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_ptr_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `s0`, `G0`, `tn0`, `c`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_outcome_ptr_def] >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- (gvs[gas_summary_ptr_at_marked]
      >- (Cases_on `res = INL ()`
          >- (gvs[] >> suspend "normal") >>
          suspend "exception") >>
      suspend "exit") >>
  suspend "exempt"
QED

Resume stmt_frag_cons_env_ptr[normal]:
  `c.ce_return_pc = cenv.ce_return_pc` by
    (irule cenv_top_ext_return_pc >> metis_tac[]) >>
  `c.ce_return_buf = cenv.ce_return_buf` by
    (irule cenv_top_ext_return_buf >> metis_tac[]) >>
  `ret_pc_ok c sm t` by
    (irule ret_pc_ok_frame >> metis_tac[]) >>
  `!tail. eval_stmt cx stmt
      (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ tail) =
      (INL (), es_end with gas_obs := tail)` by
    gvs[gas_marked_exec_ptr_def] >>
  `gas_admissible (eval_stmts cx ss) (stmt_res_ok lctx)
      (es_end with gas_obs := [])` by
    (irule gas_admissible_stmts_tail >> metis_tac[]) >>
  gvs[stmt_lands_def] >>
  `~c.ce_is_ctor` by metis_tac[cenv_top_ext_is_ctor] >>
  qpat_x_assum `!gs es1 c sa sm. _` (qspec_then
    `gas_explicit left s0.vs_gas_readings` mp_tac) >>
  simp[] >> disch_then (qspecl_then
    [`es_end with gas_obs := []`, `c`, `sa`, `sm`] mp_tac) >>
  (impl_tac >- (first_x_assum (qspec_then `[]` mp_tac) >> simp[])) >>
  simp[stmt_frag_ptr_def] >>
  disch_then (qspecl_then [`sm`, `sb`, `t`, `G`, `tn`, `cenv'`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >> irule not_fresh_at_mono >>
      qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ (eval_stmts _ _) _ _ _` mp_tac >>
  simp[gas_outcome_ptr_def] >>
  disch_then (qx_choose_then `right` strip_assume_tac)
  >- (gvs[gas_summary_ptr_at_marked]
      >- suspend "tail_normal" >> suspend "tail_exit") >>
  suspend "tail_exempt"
QED

Resume stmt_frag_cons_env_ptr[exception]:
  Cases_on `res`
  >- (rename1 `INL u` >> Cases_on `u` >> gvs[]) >>
  rename1 `INR exc` >> qexists_tac `left` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INR exc`, `es_end`, `G`, `tn`, `OK t`] >>
  conj_tac
  >- (simp[Once evaluate_def, ignore_bind_def] >>
      irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
  simp[fragExecTheory.exit_result_def] >>
  qexists_tac `cenv''` >> gvs[stmt_lands_def]
QED

Resume stmt_frag_cons_env_ptr[exit]:
  Cases_on `res`
  >- (rename1 `gas_marked_exec_ptr _ _ _ _ _ _ (INL u) _ _ _ _` >>
      Cases_on `u` >>
      qpat_x_assum `!tail. stmt_exit_ptr _ _ _ _ _` (qspec_then `[]` mp_tac) >>
      Cases_on `r` >> simp[stmt_exit_ptr_def, expr_exit_def]) >>
  rename1 `INR exc` >> qexists_tac `left` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INR exc`, `es_end`, `G`, `tn`, `r`] >> simp[] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gas_marked_exec_ptr_bind_exception >> simp[]
QED

Resume stmt_frag_cons_env_ptr[exempt]:
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err, ee) (leaf, target)` >>
  qexists_tac `left` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
  simp[Once evaluate_def, ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule (cj 3 gas_exempt_cert_rules) >> simp[ignore_bind_def]
QED

Resume stmt_frag_cons_env_ptr[tail_normal]:
  qexists_tac `left ++ right` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`res`, `es_end'`, `G'`, `tn'`, `OK t'`] >> conj_tac
  >- (simp[Once evaluate_def, ignore_bind_def] >>
      irule gas_marked_exec_ptr_bind_normal >> metis_tac[]) >>
  simp[fragExecTheory.exit_result_def] >>
  qpat_x_assum `gas_marked_exec_ptr _ _ _ (eval_stmts _ _) _ _ _ _ _ _ _`
    mp_tac >>
  simp[gas_marked_exec_ptr_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
  disch_then (assume_tac o MATCH_MP eval_stmts_preserves_scopes_dom) >>
  fs[preserves_scopes_dom_def] >>
  rename1 `cenv_top_ext c cfin _` >>
  `cenv_top_ext cenv cfin es_end'.scopes` by
    (irule cenv_top_ext_trans >>
     qexistsl_tac [`c`, `es_end.scopes`] >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x t' = SOME w` by metis_tac[] >>
  `!x. not_fresh_at sa x ==>
       FLOOKUP G' x = FLOOKUP G0 x /\ op_taint tn' (Var x) = op_taint tn0 (Var x)`
    by metis_tac[] >>
  qexists_tac `cfin` >> gvs[stmt_lands_def]
QED

Resume stmt_frag_cons_env_ptr[tail_exit]:
  qexists_tac `left ++ right` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`res`, `es_end'`, `G'`, `tn'`, `r`] >> simp[] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gas_marked_exec_ptr_bind_normal >> metis_tac[]
QED

Resume stmt_frag_cons_env_ptr[tail_exempt]:
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err, ee) (leaf, target)` >>
  qexists_tac `left ++ right` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
  simp[Once evaluate_def, ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule (cj 2 gas_exempt_cert_rules) >>
  qexistsl_tac [`es_end`, `t`, `()`] >>
  simp[GSYM ignore_bind_def] >>
  irule gas_marked_exec_ptr_exec >> metis_tac[]
QED

Finalise stmt_frag_cons_env_ptr

Theorem compile_expr_stmt_frag_ok_ptr:
  !d ctx PG func cx lctx RetQ cenv ty e es.
    expr_vv_sim_ptr d ctx PG func cenv cx (expr_type e) e es /\
    (!gs sa vv sb tv es1.
       storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
       eval_expr cx e (es with gas_obs := gs) = (INL tv, es1) /\
       compile_expr cenv (expr_type e) e sa = (vv, sb) /\
       ~block_is_terminated sa ==> ~block_is_terminated sb) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Expr e)) (eval_stmt cx (Expr e)) es
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_ptr_def] >> rpt gen_tac >>
  strip_tac >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >> gvs[] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_stmt_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
    by fs[ret_pc_ok_def] >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_ptr_def]) >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`s0`, `G0`, `tn0`] mp_tac) >> simp[] >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `?res es_end G tn r. _` strip_assume_tac >> gvs[]
      >- (qexistsl_tac [`INL ()`, `es_end`, `G`, `tn`, `OK t`] >>
          qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
          simp[gas_marked_exec_ptr_def] >> strip_tac >>
          `~is_HashMapRef tv` by
            (qpat_x_assum `!tail. eval_expr _ _ _ = _`
               (qspec_then `[]` assume_tac) >>
             fs[] >> metis_tac[expr_stmt_not_hashmap]) >>
          conj_tac >- metis_tac[eval_expr_stmt_success] >>
          simp[fragExecTheory.exit_result_def] >>
          `~t.vs_halted` by
            (drule gas_path_ptr_erase >> strip_tac >>
             metis_tac[fragGasPathTheory.gas_path_normal]) >>
          `~block_is_terminated sb` by
            (qpat_x_assum `!tail. eval_expr _ _ _ = _`
               (qspec_then `[]` assume_tac) >> fs[] >> metis_tac[]) >>
          fs[vv_post_def, stmt_lands_def, cenv_top_ext_refl, ghost_kept_def]) >>
      Cases_on `res` >- fs[expr_exit_def] >>
      qexistsl_tac [`INR y`, `es_end`, `G`, `tn`, `r`] >>
      conj_tac
      >- (fs[gas_marked_exec_ptr_def] >> metis_tac[eval_expr_stmt_exception]) >>
      disj2_tac >> simp[stmt_exit_ptr_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qexists_tac `marks` >> disj2_tac >>
  metis_tac[expr_stmt_exempt]
QED
