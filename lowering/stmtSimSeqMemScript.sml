(* Counted memory-safe statement-list sequencing, retaining caller buffers,
   allocation history and the allocation frontier at every normal landing. *)
Theory stmtSimSeqMem
Ancestors
  stmtSimDefs stmtSimSeqEnv stmtSimProps bodyMemoryDefs loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasContext gasExemptCert
  fragGasMode fragGasPath fragGasPathMem fragExec fragExecMem
  compileEnv loweringSlice stmtLowering exprLoweringProps localPtrsProps
  vyperInterpreter vyperState vyperEvalPreservesScopes
  venomState venomExecSemantics list finite_map

Theorem stmt_frag_cons_env_mem:
  !d ctx func cx lctx RetQ cenv ty stmt ss es.
    (!c. cs_mono (compile_stmt c lctx ty stmt)) /\
    (!c. cs_mono (stmts_env c lctx ty ss)) /\
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty stmt)
      (eval_stmt cx stmt) es /\
    (!gs es1 c sa sm.
       eval_stmt cx stmt (es with gas_obs := gs) = (INL (), es1) /\
       stmt_env cenv lctx ty stmt sa = (c, sm) /\
       cenv_top_ext cenv c es1.scopes ==>
       stmt_frag_mem d ctx func cx lctx RetQ c (stmts_env c lctx ty ss)
         (eval_stmts cx ss) es1) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmts_env cenv lctx ty (stmt::ss)) (eval_stmts cx (stmt::ss)) es
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
  `gas_admissible (eval_stmt cx stmt) (stmt_res_ok lctx) es` by
    (irule gas_admissible_stmts_head >> qexists_tac `ss` >> simp[]) >>
  qpat_x_assum `stmt_frag_mem _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_mem_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `s0`, `c`] mp_tac) >>
  simp[] >> strip_tac >>
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

Resume stmt_frag_cons_env_mem[normal]:
  `stmt_post_core ctx func cx lctx cenv c sa sm s0 (INL ()) (es_end with gas_obs := []) t` by
    (simp[stmt_post_core_def] >> metis_tac[]) >>
  drule_all stmt_post_core_normal_entry >> strip_tac >>
  `!tail. eval_stmt cx stmt
      (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ tail) =
      (INL (), es_end with gas_obs := tail)` by
    gvs[gas_marked_exec_def] >>
  `gas_admissible (eval_stmts cx ss) (stmt_res_ok lctx)
      (es_end with gas_obs := [])` by
    (irule gas_admissible_stmts_tail >> metis_tac[]) >>
  qpat_x_assum `!gs es1 c sa sm. _` (qspec_then
    `gas_explicit left s0.vs_gas_readings` mp_tac) >>
  simp[] >> disch_then (qspecl_then
    [`es_end with gas_obs := []`, `c`, `sa`, `sm`] mp_tac) >>
  (impl_tac >- (first_x_assum (qspec_then `[]` mp_tac) >> simp[])) >>
  simp[stmt_frag_mem_def] >>
  disch_then (qspecl_then [`sm`, `sb`, `t`, `cenv'`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[gas_outcome_def] >>
  disch_then (qx_choose_then `right` strip_assume_tac)
  >- (gvs[gas_summary_at_def]
      >- suspend "tail_normal" >> suspend "tail_exit") >>
  suspend "tail_exempt"
QED

Resume stmt_frag_cons_env_mem[exception]:
  Cases_on `res`
  >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ (INL _) _ _` mp_tac >>
      rename1 `INL u` >> Cases_on `u` >> gvs[]) >>
  rename1 `INR exc` >> qexists_tac `left` >> disj1_tac >>
  qexistsl_tac [`INR exc`, `es_end`, `OK t`] >>
  conj_tac
  >- (simp[Once evaluate_def, ignore_bind_def] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  simp[] >> disj1_tac >> suspend "exception_post"
QED
Resume stmt_frag_cons_env_mem[exit]:
  Cases_on `res`
  >- (rename1 `gas_marked_exec _ _ _ _ _ (INL u) _ _` >>
      Cases_on `u` >> metis_tac[stmt_exit_loop_ctl]) >>
  rename1 `INR exc` >> qexists_tac `left` >> disj1_tac >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >> simp[] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gas_marked_exec_bind_exception >> simp[]
QED
Resume stmt_frag_cons_env_mem[exempt]:
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err, ee) (leaf, target)` >>
  qexists_tac `left` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
  simp[Once evaluate_def, ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule (cj 3 gas_exempt_cert_rules) >> simp[ignore_bind_def]
QED
Resume stmt_frag_cons_env_mem[tail_normal]:
  qexists_tac `left ++ right` >> disj1_tac >>
  qexistsl_tac [`res`, `es_end'`, `OK t'`] >> conj_tac
  >- (simp[Once evaluate_def, ignore_bind_def] >>
      irule gas_marked_exec_bind_normal >> metis_tac[]) >>
  simp[] >> disj1_tac >> suspend "sequence_post"
QED
Resume stmt_frag_cons_env_mem[tail_exit]:
  qexists_tac `left ++ right` >> disj1_tac >>
  qexistsl_tac [`res`, `es_end'`, `r`] >> simp[] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gas_marked_exec_bind_normal >> metis_tac[]
QED
Resume stmt_frag_cons_env_mem[tail_exempt]:
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err, ee) (leaf, target)` >>
  qexists_tac `left ++ right` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
  simp[Once evaluate_def, ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule (cj 2 gas_exempt_cert_rules) >>
  qexistsl_tac [`es_end`, `t`, `()`] >>
  simp[GSYM ignore_bind_def]
QED
Resume stmt_frag_cons_env_mem[exception_post]:
  `stmt_post_core ctx func cx lctx cenv c sa sm s0 (INR exc)
      (es_end with gas_obs := []) t` by
    (simp[stmt_post_core_def] >> qexists_tac `cenv''` >> simp[]) >>
  `stmt_post_core ctx func cx lctx cenv cenv' sa sb s0 (INR exc)
      (es_end with gas_obs := []) t` by
    (irule stmt_post_core_exception_endpoint >> metis_tac[]) >>
  qexists_tac `cenv''` >> simp[] >> conj_tac
  >- (gvs[stmt_post_core_def] >> metis_tac[]) >>
  irule return_buf_frame_frame >>
  qexistsl_tac [`cenv''`, `t`, `sm`] >> simp[]
QED
Resume stmt_frag_cons_env_mem[sequence_post]:
  `stmt_post_core ctx func cx lctx c cenv' sm sb t res
      (es_end' with gas_obs := []) t'` by
    (simp[stmt_post_core_def] >> qexists_tac `cenv''` >> simp[]) >>
  qpat_x_assum `gas_marked_exec _ _ (eval_stmts _ _) _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
  disch_then (assume_tac o MATCH_MP eval_stmts_preserves_scopes_dom) >>
  `stmt_post_core ctx func cx lctx cenv cenv' sa sb s0 res
      (es_end' with gas_obs := []) t'` by
    (irule stmt_post_core_sequence >>
     qexistsl_tac [`c`, `es_end with gas_obs := []`, `sm`, `t`] >>
     gvs[preserves_scopes_dom_def]) >>
  qexists_tac `cenv''` >> simp[] >> conj_tac
  >- (irule cenv_top_ext_trans >>
      qexistsl_tac [`c`, `es_end.scopes`] >>
      gvs[preserves_scopes_dom_def]) >>
  gvs[stmt_post_core_def]
QED
Finalise stmt_frag_cons_env_mem

