(* Counted statement-list sequencing at each actual compiled environment. *)
Theory stmtSimSeqEnv
Ancestors
  stmtSimDefs stmtSimProps loweringPosts gasOutcome gasSummary gasSummaryCompose
  gasContext gasExemptCert fragExec fragGasMode fragGasPath compileEnv loweringStateRelDefs loweringSlice
  stmtLowering exprLoweringProps localPtrsProps vyperInterpreter vyperState
  vyperEvalPreservesScopes stmtLoweringMono list finite_map

Theorem gas_admissible_stmts_head:
  gas_admissible (eval_stmts cx (stmt::ss)) (stmt_res_ok lctx) es ==>
  gas_admissible (eval_stmt cx stmt) (stmt_res_ok lctx) es
Proof
  rw[gas_admissible_def] >>
  Cases_on `res` >- (rename1 `INL u` >> Cases_on `u` >> simp[stmt_res_ok_def]) >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def] >>
  metis_tac[]
QED

Theorem gas_admissible_stmts_tail:
  gas_admissible (eval_stmts cx (stmt::ss)) (stmt_res_ok lctx) es /\
  (!tail. eval_stmt cx stmt (es with gas_obs := xs ++ tail) =
    (INL (), mid with gas_obs := tail)) ==>
  gas_admissible (eval_stmts cx ss) (stmt_res_ok lctx)
    (mid with gas_obs := [])
Proof
  rw[gas_admissible_def] >>
  qpat_x_assum `!gs res ee. _` (qspec_then `xs ++ gs` mp_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def] >>
  metis_tac[]
QED

(* stmt_post without its allocation frame: the post the counted
   memory-safe sequencing (stmtSimSeqMem) composes, whose fragments make
   no claim about older allocations' bytes. *)
Definition stmt_post_core_def:
  stmt_post_core ctx func cx lctx cenv cenv' sa sb s0 res ee t <=>
    ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel ctx func cenv'' cx ee t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
End

Theorem stmt_post_core_normal_entry:
  stmt_post_core ctx func cx lctx cenv c sa sm s0 (INL ()) mid t /\
  ret_pc_ok cenv sa s0 /\ sa.cs_next_var <= sm.cs_next_var ==>
  cenv_top_ext cenv c mid.scopes /\
  stmt_state_rel ctx func c cx mid t /\ ~block_is_terminated sm /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ret_pc_ok c sm t
Proof
  rw[stmt_post_core_def, stmt_lands_def] >>
  irule ret_pc_ok_frame >>
  metis_tac[cenv_top_ext_return_pc]
QED

Theorem stmt_post_core_exception_endpoint:
  res <> INL () /\
  stmt_post_core ctx func cx lctx cenv c sa sm s0 res ee t ==>
  stmt_post_core ctx func cx lctx cenv c' sa sb s0 res ee t
Proof
  rw[stmt_post_core_def] >> qexists_tac `cenv''` >>
  gvs[stmt_lands_def] >> metis_tac[]
QED

Theorem stmt_post_core_sequence:
  stmt_post_core ctx func cx lctx cenv c sa sm s0 (INL ()) mid t /\
  stmt_post_core ctx func cx lctx c c' sm sb t res ee u /\
  sa.cs_next_var <= sm.cs_next_var /\
  (mid.scopes = [] <=> ee.scopes = []) /\
  MAP FDOM (TL mid.scopes) = MAP FDOM (TL ee.scopes) ==>
  stmt_post_core ctx func cx lctx cenv c' sa sb s0 res ee u
Proof
  rw[stmt_post_core_def] >> qexists_tac `cenv''` >> simp[] >>
  conj_tac >- (irule cenv_top_ext_trans >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[not_fresh_at_def, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem stmt_post_core:
  stmt_post ctx func cx lctx cenv c sa sb es s0 res ee t ==>
  stmt_post_core ctx func cx lctx cenv c sa sb s0 res ee t
Proof
  rw[stmt_post_def, stmt_post_core_def] >> qexists_tac `cenv''` >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem stmt_post_normal_entry:
  stmt_post ctx func cx lctx cenv c sa sm es0 s0 (INL ()) mid t /\
  ret_pc_ok cenv sa s0 /\ sa.cs_next_var <= sm.cs_next_var ==>
  cenv_top_ext cenv c mid.scopes /\
  stmt_state_rel ctx func c cx mid t /\ ~block_is_terminated sm /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ret_pc_ok c sm t
Proof
  strip_tac >> irule stmt_post_core_normal_entry >>
  metis_tac[stmt_post_core]
QED

Theorem stmt_post_exception_endpoint:
  res <> INL () /\
  stmt_post ctx func cx lctx cenv c sa sm es0 s0 res ee t ==>
  stmt_post ctx func cx lctx cenv c' sa sb es0 s0 res ee t
Proof
  rw[stmt_post_def] >> qexists_tac `cenv''` >>
  gvs[stmt_lands_def] >> metis_tac[]
QED

Theorem stmt_post_sequence:
  stmt_post ctx func cx lctx cenv c sa sm es0 s0 (INL ()) mid t /\
  stmt_post ctx func cx lctx c c' sm sb mid t res ee u /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (mid.scopes = [] <=> ee.scopes = []) /\
  MAP FDOM (TL mid.scopes) = MAP FDOM (TL ee.scopes) ==>
  stmt_post ctx func cx lctx cenv c' sa sb es0 s0 res ee u
Proof
  rw[stmt_post_def] >> qexists_tac `cenv''` >> simp[] >>
  `alloca_frame cenv es0 sa s0 cenv'' ee u` by
    (irule alloca_frame_trans >> metis_tac[]) >>
  simp[] >> conj_tac >- (irule cenv_top_ext_trans >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[not_fresh_at_def, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem declare_stmt_local_next_id:
  !cenv stmt st c st'.
    declare_stmt_local cenv stmt st = (c, st') ==> st'.cs_next_id = st.cs_next_id
Proof
  Cases_on `stmt` >>
  simp[declare_stmt_local_def, declare_local_def, comp_return_def,
       comp_bind_def, fresh_var_def, LET_THM] >>
  rw[] >> gvs[comp_return_def, comp_bind_def, fresh_var_def]
QED

Theorem stmt_env_next_id:
  !cenv lctx ty stmt sa c sb.
    stmt_env cenv lctx ty stmt sa = (c, sb) ==> sa.cs_next_id <= sb.cs_next_id
Proof
  rpt gen_tac >>
  simp[stmt_env_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule declare_stmt_local_next_id >> strip_tac >>
  qmatch_asmsub_rename_tac `compile_stmt c1 lctx ty stmt s1 = (_, s2)` >>
  qspecl_then [`c1`, `lctx`, `ty`, `stmt`, `s1`] mp_tac
    (cj 1 stmtLoweringMonoTheory.compile_stmt_ci_mono) >>
  gvs[exprLoweringPropsTheory.ci_mono_def]
QED

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
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_cons, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rename1 `stmt_env cenv lctx ty stmt sa = (c, sm)` >>
  drule_all stmt_env_reserved >> strip_tac >>
  drule stmt_env_next_id >> strip_tac >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var` by
    (qpat_x_assum `!c. cs_mono (stmts_env _ _ _ _)` (qspec_then `c` mp_tac) >>
     simp[cs_mono_def] >> metis_tac[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_stmt cx stmt) (stmt_res_ok lctx) es` by
    (irule gas_admissible_stmts_head >> qexists_tac `ss` >> simp[]) >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >>
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

Resume stmt_frag_cons_env[normal]:
  drule_all stmt_post_normal_entry >> strip_tac >>
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
  simp[stmt_frag_def, stmt_framed_frag_def] >>
  disch_then (qspecl_then [`sm`, `sb`, `t`, `cenv'`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[gas_outcome_def] >>
  disch_then (qx_choose_then `right` strip_assume_tac)
  >- (gvs[gas_summary_at_def]
      >- suspend "tail_normal" >> suspend "tail_exit") >>
  suspend "tail_exempt"
QED

Resume stmt_frag_cons_env[exception]:
  Cases_on `res` >- (rename1 `INL u` >> Cases_on `u` >> gvs[]) >>
  rename1 `INR exc` >> qexists_tac `left` >> disj1_tac >>
  qexistsl_tac [`INR exc`, `es_end`, `OK t`] >>
  conj_tac
  >- (simp[Once evaluate_def, ignore_bind_def] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  simp[] >> disj1_tac >> irule stmt_post_exception_endpoint >> metis_tac[]
QED
Resume stmt_frag_cons_env[exit]:
  Cases_on `res`
  >- (rename1 `INL u` >> Cases_on `u` >>
      metis_tac[stmt_exit_loop_ctl]) >>
  rename1 `INR exc` >> qexists_tac `left` >> disj1_tac >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >> simp[] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gas_marked_exec_bind_exception >> simp[]
QED
Resume stmt_frag_cons_env[exempt]:
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err, ee) (leaf, target)` >>
  qexists_tac `left` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
  simp[Once evaluate_def, ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule (cj 3 gas_exempt_cert_rules) >> simp[ignore_bind_def]
QED
Resume stmt_frag_cons_env[tail_normal]:
  qexists_tac `left ++ right` >> disj1_tac >>
  qexistsl_tac [`res`, `es_end'`, `OK t'`] >> conj_tac
  >- (simp[Once evaluate_def, ignore_bind_def] >>
      irule gas_marked_exec_bind_normal >> metis_tac[]) >>
  simp[] >> disj1_tac >>
  qpat_x_assum `gas_marked_exec _ _ (eval_stmts _ _) _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
  disch_then (assume_tac o MATCH_MP eval_stmts_preserves_scopes_dom) >>
  irule stmt_post_sequence >>
  qexistsl_tac [`c`, `es_end with gas_obs := []`, `sm`, `t`] >>
  gvs[preserves_scopes_dom_def]
QED
Resume stmt_frag_cons_env[tail_exit]:
  qexists_tac `left ++ right` >> disj1_tac >>
  qexistsl_tac [`res`, `es_end'`, `r`] >> simp[] >>
  simp[Once evaluate_def, ignore_bind_def] >>
  irule gas_marked_exec_bind_normal >> metis_tac[]
QED
Resume stmt_frag_cons_env[tail_exempt]:
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err, ee) (leaf, target)` >>
  qexists_tac `left ++ right` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
  simp[Once evaluate_def, ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule (cj 2 gas_exempt_cert_rules) >>
  qexistsl_tac [`es_end`, `t`, `()`] >>
  simp[GSYM ignore_bind_def]
QED
Finalise stmt_frag_cons_env

