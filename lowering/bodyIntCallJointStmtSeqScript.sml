(* Full joint statement-list sequencing: normalization and composition. *)
Theory bodyIntCallJointStmtSeq
Ancestors
  bodyIntCallJointContract bodyIntCallJointStmtBoundary bodyIntCallJointStmtZero
  stmtSimSeqEnv stmtSimProps loweringPosts stmtLowering compileEnv
  vyperInterpreter vyperState vyperTypeSystem bodyExprPreFacts
  supportedStmts supportedStmtTraverse supportedExprTraverse vyperTypeCallGraph
  vyperTypeCallStackSoundness exprLoweringProps freshWrites
  gasOutcome gasSummary gasSummaryCompose gasContext gasExemptCert
  fragGasMode fragGasPath vyperEvalPreservesScopes list finite_map
  stmtLoweringMono loweringSlice fragExec

Theorem eval_stmts_singleton:
  !cx st. eval_stmts cx [st] = eval_stmt cx st
Proof
  rpt gen_tac >> simp[Once evaluate_def, Once evaluate_def, FUN_EQ_THM] >>
  gen_tac >> Cases_on `eval_stmt cx st x` >>
  rename1 `_ = (res,ee)` >> Cases_on `res` >>
  simp[ignore_bind_def, bind_def, return_def] >>
  rename1 `INL u` >> Cases_on `u` >> simp[]
QED

Theorem stmts_env_singleton:
  !ce lctx ty st sa.
    ~block_is_terminated sa ==>
    stmts_env ce lctx ty [st] sa = stmt_env ce lctx ty st sa
Proof
  simp[stmts_env_cons, stmts_env_def, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `stmt_env ce lctx ty st sa` >> simp[]
QED

(* Successful typing only extends locals at an AnnAssign.  In particular,
   restricting immutable assignment cannot change the resulting local maps. *)
Theorem type_stmt_assignable_result:
  !env ret st env' m restricted.
    type_stmt env ret st = SOME env' /\
    type_stmt (env with bare_global_assignable := m) ret st = SOME restricted ==>
    restricted = env' with bare_global_assignable := m
Proof
  rpt gen_tac >> Cases_on `?id typ e. st = AnnAssign id typ e`
  >- (gvs[] >> simp[Once type_stmt_def] >> simp[Once type_stmt_def] >>
      rpt strip_tac >> gvs[extend_local_def]) >>
  metis_tac[type_stmt_other]
QED

Theorem intcall_stmts_producer_cons:
  !fp stmt ss.
    intcall_stmts_producer fp [stmt] /\ intcall_stmts_producer fp ss ==>
    intcall_stmts_producer fp (stmt::ss)
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once intcall_stmts_producer_def] >> rpt gen_tac >> strip_tac >>
  gvs[supported_stmt_def, Once type_stmt_def, AllCaseEqs(),
      int_calls_stmt_def, supported_stmt_expr_exists_def] >>
  rename1 `type_stmt env fp.jc_ret_ty stmt = SOME env1` >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_cons, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rename1 `stmt_env ce lctx _ stmt sa = (c,sm)` >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    (drule stmt_env_reserved >>
     simp[cj 1 compile_stmt_cs_mono] >>
     fs[intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]) >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var` by
    (mp_tac (Q.SPECL [`c`, `lctx`,
       `if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty`, `ss`]
       stmts_env_cs_mono) >> simp[cs_mono_def] >> metis_tac[]) >>
  `fn_has_code sa sm fp.jc_func /\ fn_has_code sm sb fp.jc_func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_stmt fp.jc_cx stmt) (stmt_res_ok lctx) es` by
    metis_tac[gas_admissible_stmts_head] >>
  Cases_on `type_stmt (env with bare_global_assignable := FEMPTY)
    fp.jc_ret_ty stmt` >> gvs[Once type_stmt_def] >>
  `IS_SOME (type_stmts (env1 with bare_global_assignable := FEMPTY)
     fp.jc_ret_ty ss)` by
    (drule_all type_stmt_assignable_result >> strip_tac >> gvs[]) >>
  `IS_SOME (type_stmt (env with bare_global_assignable := FEMPTY)
     fp.jc_ret_ty stmt)` by simp[] >>
  qpat_x_assum `intcall_stmts_producer fp [stmt]` mp_tac >>
  csimp[intcall_stmts_producer_def, eval_stmts_singleton,
       supported_stmt_def, supported_stmt_expr_exists_def, SF ETA_ss,
       type_stmt_def, stmts_env_singleton, int_calls_stmt_def] >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[gas_outcome_def] >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- (gvs[gas_summary_at_def]
      >- (Cases_on `res = INL ()`
          >- (gvs[] >> suspend "normal") >>
          suspend "exception") >>
      suspend "exit") >>
  suspend "exempt"
QED

Resume intcall_stmts_producer_cons[normal]:
  `same_frame ce c` by
    metis_tac[bodySimTheory.cenv_top_ext_same_frame] >>
  `body_inv fp.jc_tops fp.jc_ctx c fp.jc_cx` by
    metis_tac[body_inv_same_frame] >>
  `EVERY (stmt_exprs_ok c) ss` by
    metis_tac[stmt_exprs_ok_same_frame] >>
  `!tail. eval_stmt fp.jc_cx stmt
      (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
      (INL (), es_end with gas_obs := tail)` by
    gvs[gas_marked_exec_def] >>
  `gas_admissible (eval_stmts fp.jc_cx ss) (stmt_res_ok lctx)
      (es_end with gas_obs := [])` by
    (irule gas_admissible_stmts_tail >> metis_tac[]) >>
  qpat_x_assum `stmt_lands _ _ _ _` mp_tac >>
  simp[stmt_lands_def] >> strip_tac >>
  qpat_x_assum `intcall_stmts_producer fp ss` mp_tac >>
  simp[intcall_stmts_producer_def] >>
  disch_then drule_all >>
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[gas_outcome_def] >>
  disch_then (qx_choose_then `right` strip_assume_tac)
  >- (gvs[gas_summary_at_def]
      >- suspend "tail_normal" >> suspend "tail_exit") >>
  suspend "tail_exempt"
QED

Resume intcall_stmts_producer_cons[exception]:
  Cases_on `res` >- (rename1 `INL v` >> Cases_on `v` >> gvs[]) >>
  rename1 `INR exc` >> qexists_tac `left` >> disj1_tac >>
  qexistsl_tac [`INR exc`, `es_end`, `OK u`] >> conj_tac
  >- (simp[Once evaluate_def, ignore_bind_def] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  simp[] >> disj1_tac >>
  qexistsl_tac [`ce''`, `env''`] >>
  conj_tac >- gvs[stmt_lands_def] >>
  simp[] >> irule intcall_joint_res_next_var >> metis_tac[]
QED
Resume intcall_stmts_producer_cons[exit]:
  Cases_on `res`
  >- (rename1 `INL v` >> Cases_on `v` >>
      fs[intcall_stmt_exit_def, exprSimDefsTheory.expr_exit_def]) >>
  rename1 `INR exc` >> qexists_tac `left` >> disj1_tac >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >> simp[] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gas_marked_exec_bind_exception >> simp[]
QED
Resume intcall_stmts_producer_cons[exempt]:
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err, ee) (leaf, target)` >>
  qexists_tac `left` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
  simp[Once evaluate_def, ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule (cj 3 gas_exempt_cert_rules) >> simp[ignore_bind_def]
QED
Resume intcall_stmts_producer_cons[tail_normal]:
  rename1 `gas_marked_exec _ _ (eval_stmts _ ss) _ right rr ee (OK v)` >>
  qexists_tac `left ++ right` >> disj1_tac >>
  qexistsl_tac [`rr`, `ee`, `OK v`] >> conj_tac
  >- (simp[Once evaluate_def, ignore_bind_def] >>
      irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`es_end`, `u`, `()`] >> simp[]) >>
  simp[] >> disj1_tac >>
  `preserves_scopes_dom (es_end with gas_obs := []) ee` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_stmts _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
     disch_then (mp_tac o MATCH_MP eval_stmts_preserves_scopes_dom) >>
     simp[preserves_scopes_dom_def]) >>
  rename1 `intcall_joint_res fp postce postenv (ee with gas_obs := []) sb v` >>
  qexistsl_tac [`postce`, `postenv`] >>
  conj_tac >- fs[stmt_lands_def] >>
  simp[] >> conj_tac
  >- (irule cenv_top_ext_trans >>
      qexists_tac `c` >> gvs[preserves_scopes_dom_def] >>
      qexists_tac `es_end.scopes` >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!x w. not_fresh_at sm x /\ _ ==> _`
    irule >>
  conj_tac >- metis_tac[] >>
  fs[not_fresh_at_def]
QED
Resume intcall_stmts_producer_cons[tail_exit]:
  qexists_tac `left ++ right` >> disj1_tac >>
  qexistsl_tac [`res`, `es_end'`, `r`] >> simp[] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gas_marked_exec_bind_normal >> metis_tac[]
QED
Resume intcall_stmts_producer_cons[tail_exempt]:
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err, ee) (leaf, target)` >>
  qexists_tac `left ++ right` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
  simp[Once evaluate_def, ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule (cj 2 gas_exempt_cert_rules) >>
  qexistsl_tac [`es_end`, `u`, `()`] >>
  simp[GSYM ignore_bind_def]
QED
Finalise intcall_stmts_producer_cons
