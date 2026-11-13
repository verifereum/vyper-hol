(* Counted memory-safe statement-list sequencing, retaining caller buffers,
   allocation history and the allocation frontier at every normal landing. *)
Theory stmtSimSeqMem
Ancestors
  stmtSimDefs stmtSimSeqEnv stmtSimProps bodyMemoryDefs loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasContext gasExemptCert
  fragGasMode fragGasPath fragGasPathMem fragExec fragExecMem
  compileEnv loweringSlice stmtLowering exprLoweringProps localPtrsProps
  vyperInterpreter vyperState vyperEvalPreservesScopes
  gasStorage vyperStorageTrace vyperStorageFootprint
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
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `s0`, `c`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- suspend "bad"
  >- (gvs[gas_summary_at_def]
      >- (Cases_on `res = INL ()`
          >- (gvs[] >> suspend "normal") >>
          suspend "exception") >>
      suspend "exit") >>
  suspend "exempt"
QED

(* The head statement left the storage domain: the whole sequence is a
   bad-storage run under the head's marks. *)
val head_out_of_domain_tac =
  qexists_tac `left` >> disj1_tac >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gasStorageTheory.gas_bad_storage_at_bind_left >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  irule gasStorageTheory.gas_bad_storage_at_counted_prefix >>
  qpat_assum `gas_marked_exec _ _ (eval_stmt _ _) _ _ _ _ _` (irule_at Any) >>
  simp[];

Resume stmt_frag_cons_env_mem[bad]:
  qexists_tac `left` >> disj1_tac >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gasStorageTheory.gas_bad_storage_at_bind_left >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]
QED

Resume stmt_frag_cons_env_mem[normal]:
  Cases_on `storage_trace_domain cx st0 es_end.storage_trace`
  >- suspend "in_domain" >>
  head_out_of_domain_tac
QED

Resume stmt_frag_cons_env_mem[in_domain]:
  `?H0. valid_horizon cx st0 H0 es_end.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_post_core H0 ctx func cx lctx cenv c sa sm s0 (INL ())
      (es_end with gas_obs := []) t` by
    (simp[stmt_post_core_def] >> metis_tac[]) >>
  `return_buf_frame d c sm t /\ alloca_history func t /\
   s0.vs_alloca_next <= t.vs_alloca_next` by metis_tac[] >>
  `cenv_top_ext cenv c es_end.scopes /\ ~block_is_terminated sm /\
   ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ret_pc_ok c sm t` by
    (drule_all stmt_post_core_normal_entry >> simp[]) >>
  `!HH. valid_horizon cx st0 HH es_end.storage_trace ==>
     stmt_state_rel HH ctx func c cx (es_end with gas_obs := []) t /\
     storage_well_formed_on cx (es_end with gas_obs := []) (FST HH)` by
    (qx_gen_tac `HH` >> strip_tac >> metis_tac[]) >>
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
  disch_then (qspecl_then [`st0`, `sm`, `sb`, `t`, `cenv'`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `right` strip_assume_tac)
  >- suspend "tail_bad"
  >- (gvs[gas_summary_at_def]
      >- suspend "tail_normal" >> suspend "tail_exit") >>
  suspend "tail_exempt"
QED

Resume stmt_frag_cons_env_mem[exception]:
  Cases_on `res`
  >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ (INL _) _ _` mp_tac >>
      rename1 `INL u` >> Cases_on `u` >> gvs[]) >>
  rename1 `INR exc` >> qexists_tac `left` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR exc`, `es_end`, `OK t`] >>
  conj_tac
  >- (simp[Once evaluate_def, ignore_bind_def] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  simp[] >> disj1_tac >> suspend "exception_post"
QED
Resume stmt_frag_cons_env_mem[exit]:
  Cases_on `res`
  >- (rename1 `INL u` >> Cases_on `u` >>
      Cases_on `storage_trace_domain cx st0 es_end.storage_trace`
      >- (`?H0. valid_horizon cx st0 H0 es_end.storage_trace` by
            metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
          qpat_x_assum `!H. valid_horizon _ _ H _ ==> !tail. _`
            (qspec_then `H0` mp_tac) >> impl_tac >- gs[] >>
          simp[stmt_exit_loop_ctl]) >>
      head_out_of_domain_tac) >>
  rename1 `INR exc` >> qexists_tac `left` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >> simp[] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gas_marked_exec_bind_exception >> simp[]
QED
Resume stmt_frag_cons_env_mem[exempt]:
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err, ee) (leaf, target)` >>
  qexists_tac `left` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
  simp[Once evaluate_def, ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule (cj 3 gas_exempt_cert_rules) >> simp[ignore_bind_def]
QED
Resume stmt_frag_cons_env_mem[tail_bad]:
  qexists_tac `left ++ right` >> disj1_tac >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gasStorageTheory.gas_bad_storage_at_bind_right >>
  qpat_assum `gas_marked_exec _ _ (eval_stmt _ _) _ _ _ _ _` (irule_at Any) >>
  simp[]
QED
Resume stmt_frag_cons_env_mem[tail_normal]:
  qexists_tac `left ++ right` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`, `es_end'`, `OK t'`] >> conj_tac
  >- (simp[Once evaluate_def, ignore_bind_def] >>
      irule gas_marked_exec_bind_normal >> metis_tac[]) >>
  simp[] >> disj1_tac >> suspend "sequence_post"
QED
Resume stmt_frag_cons_env_mem[tail_exit]:
  qexists_tac `left ++ right` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`, `es_end'`, `r`] >> simp[] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gas_marked_exec_bind_normal >> metis_tac[]
QED
Resume stmt_frag_cons_env_mem[tail_exempt]:
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err, ee) (leaf, target)` >>
  qexists_tac `left ++ right` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
  simp[Once evaluate_def, ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule (cj 2 gas_exempt_cert_rules) >>
  qexistsl_tac [`es_end`, `t`, `()`] >>
  simp[GSYM ignore_bind_def]
QED
Resume stmt_frag_cons_env_mem[exception_post]:
  qx_gen_tac `HH` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  rename1 `return_buf_frame d cenv1 sm t` >>
  `stmt_lands lctx sb (INR exc) t` by gvs[stmt_lands_def] >>
  `return_buf_frame d cenv1 sb t` by
    (irule return_buf_frame_frame >>
     qexistsl_tac [`cenv1`, `t`, `sm`] >> simp[]) >>
  qexists_tac `cenv1` >> simp[]
QED
Resume stmt_frag_cons_env_mem[sequence_post]:
  qx_gen_tac `HH` >> strip_tac >>
  `valid_horizon cx st0 HH es_end.storage_trace` by
    (qpat_assum `gas_marked_exec _ _ (eval_stmts _ _) _ _ _ _ _`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                             gas_marked_exec_valid_prefix)) >>
     impl_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
     disch_then (qspecl_then [`cx`, `st0`, `HH`] mp_tac) >> simp[]) >>
  `stmt_post_core HH ctx func cx lctx cenv c sa sm s0 (INL ())
      (es_end with gas_obs := []) t` by
    (simp[stmt_post_core_def] >> metis_tac[]) >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by metis_tac[] >>
  qpat_x_assum `!H. valid_horizon _ _ H es_end'.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  rename1 `return_buf_frame d cenv1 sb t'` >>
  `stmt_post_core HH ctx func cx lctx c cenv' sm sb t res
      (es_end' with gas_obs := []) t'` by
    (simp[stmt_post_core_def] >> qexists_tac `cenv1` >> simp[]) >>
  `s0.vs_alloca_next <= t'.vs_alloca_next` by
    metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  qpat_x_assum `gas_marked_exec _ _ (eval_stmts _ _) _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
  disch_then (assume_tac o MATCH_MP eval_stmts_preserves_scopes_dom) >>
  `stmt_post_core HH ctx func cx lctx cenv cenv' sa sb s0 res
      (es_end' with gas_obs := []) t'` by
    (irule stmt_post_core_sequence >>
     qexistsl_tac [`c`, `es_end with gas_obs := []`, `sm`, `t`] >>
     gvs[preserves_scopes_dom_def]) >>
  qexists_tac `cenv1` >> simp[] >> conj_tac
  >- (irule cenv_top_ext_trans >>
      qexistsl_tac [`c`, `es_end.scopes`] >>
      gvs[preserves_scopes_dom_def]) >>
  gvs[stmt_post_core_def]
QED
Finalise stmt_frag_cons_env_mem
