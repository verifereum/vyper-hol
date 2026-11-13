Theory bodyIfExpRootSelection
Ancestors
  exprSimDefs exprSimMemDefs exprSimProps loweringPosts exprSimIfExp
  gasOutcome gasStorage vyperStorageFootprint gasExemptCert gasSummary gasContext fragGasMode fragGasPath
  gasSummaryCompose fragExec
  fragGasPathMem vyperState vyperInterpreter vyperAST allocaHistoryFragment
  vyperEvalExprPreservesScopesDom exprLoweringProps allocaHistory venomState

Theorem ifexp_condition_exit_mem:
  gas_marked_exec T (ctx,func)
    (vyperState$bind (eval_expr cx c) (read_result cx))
    (es,s0) marks res mid r /\ expr_exit res r ==>
  gas_outcome T tops (ctx,func) cx st0 (eval_expr cx (IfExp t c a b)) (es,s0) Q
    (\H res ee r. expr_exit res r)
Proof
  Cases_on `res` >> simp[] >> strip_tac >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR y`,`mid`,`r`] >> simp[] >>
  conj_tac
  >- (rewrite_tac[ifexp_root_eval_forced] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >>
  Cases_on `r` >> fs[expr_exit_def, exit_result_def] >>
  Cases_on `y` >> fs[expr_exit_def] >>
  rename1 `Error er` >> Cases_on `er` >> fs[expr_exit_def]
QED

Theorem ifexp_root_condition_dispatch_mem:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  gas_outcome T tops (ctx,func) cx st0
    (bind (eval_expr cx c) (read_result cx)) (es,s0) P
    (\H res ee r. expr_exit res r) /\
  (!H res ee u. P H res ee u ==> ?v. res = INL v) /\
  (!marks sel mid u.
    gas_marked_exec T (ctx,func) (bind (eval_expr cx c) (read_result cx))
      (es,s0) marks (INL (BoolV sel)) mid (OK u) /\
    (?H. valid_horizon cx st0 H mid.storage_trace) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
         P H (INL (BoolV sel)) (mid with gas_obs := []) u) ==>
    gas_outcome T tops (ctx,func) cx st0 (eval_expr cx (IfExp t c a b)) (es,s0) Q
      (\H res ee r. expr_exit res r)) ==>
  gas_outcome T tops (ctx,func) cx st0 (eval_expr cx (IfExp t c a b)) (es,s0) Q
    (\H res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def, gas_summary_at_def])
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[ifexp_root_eval_forced] >>
      irule gas_bad_storage_at_bind_left >> simp[ifexp_root_cont_frame])
  >- (qpat_x_assum `r = OK _` SUBST_ALL_TAC >>
      qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
      reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
      >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
          rewrite_tac[ifexp_root_eval_forced] >>
          irule gas_bad_storage_at_bind_left >> simp[ifexp_root_cont_frame] >>
          irule gas_bad_storage_at_counted_prefix >> metis_tac[]) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def] >>
      `?v. res = INL v` by metis_tac[] >>
      qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
      `!tail. bind (eval_expr cx c) (read_result cx)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL v,es_end with gas_obs := tail)` by fs[gas_marked_exec_def] >>
      `?sel. v = BoolV sel` by (irule ifexp_root_condition_bool >> metis_tac[]) >>
      qpat_x_assum `v = BoolV sel` SUBST_ALL_TAC >>
      qpat_x_assum `!marks sel mid u. _` (qspecl_then
        [`marks`,`sel`,`es_end`,`t`] mp_tac) >>
      impl_tac
      >- (rpt conj_tac
          >- first_assum ACCEPT_TAC
          >- (qexists_tac `storage_trace_horizon es_end.storage_trace` >> simp[])
          >- (rpt strip_tac >> metis_tac[])) >>
      simp[])
  >- (qpat_x_assum `(\res ee r. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
      reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
      >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
          rewrite_tac[ifexp_root_eval_forced] >>
          irule gas_bad_storage_at_bind_left >> simp[ifexp_root_cont_frame] >>
          irule gas_bad_storage_at_counted_prefix >> metis_tac[]) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def] >>
      `expr_exit res r` by metis_tac[] >>
      irule ifexp_condition_exit_mem >> metis_tac[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  metis_tac[ifexp_root_condition_cert]
QED

Theorem ifexp_selected_entry_facts_mem:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  gas_marked_exec T (ctx,func) (bind (eval_expr cx c) (read_result cx))
    (es,s0) marks (INL (BoolV sel)) mid (OK u) /\
  expr_post H ctx func ce cx c es sa sc s0 (mid with gas_obs := [])
    (BoolV sel) cop u /\
  alloca_history func u /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
  sc.cs_next_var <= se.cs_next_var /\ sc.cs_next_id <= se.cs_next_id /\
  (!gs v ee. bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := gs) = (INL v,ee) ==>
      expr_sim_mem ctx func ce cx ty a ee /\ expr_sim_mem ctx func ce cx ty b ee /\
      expr_vv_sim_mem ctx func ce cx ty a ee /\ expr_vv_sim_mem ctx func ce cx ty b ee) ==>
  gas_admissible (bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
    expr_vv_res_ok (mid with gas_obs := []) /\
  expr_sim_mem ctx func ce cx ty (if sel then a else b) (mid with gas_obs := []) /\
  expr_vv_sim_mem ctx func ce cx ty (if sel then a else b) (mid with gas_obs := []) /\
  stmt_state_rel H ctx func ce cx (mid with gas_obs := []) (jump_to lbl u) /\
  alloca_history func (jump_to lbl u) /\
  MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes /\
  sa.cs_next_var <= se.cs_next_var /\ sa.cs_next_id <= se.cs_next_id
Proof
  strip_tac >>
  `!tail. bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL (BoolV sel),mid with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL (BoolV sel),mid with gas_obs := [])` by metis_tac[listTheory.APPEND_NIL] >>
  `expr_sim_mem ctx func ce cx ty (if sel then a else b) (mid with gas_obs := []) /\
   expr_vv_sim_mem ctx func ce cx ty (if sel then a else b) (mid with gas_obs := [])` by
    (qpat_x_assum `!gs v ee. _` drule >> Cases_on `sel` >> simp[]) >>
  conj_tac
  >- (irule ifexp_root_branch_admissible >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any)) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- fs[expr_post_def, stmt_state_rel_jump_to] >>
  conj_tac
  >- (irule alloca_history_jump >> simp[venomStateTheory.jump_to_def] >>
      qexists_tac `u` >> simp[]) >>
  conj_tac >- (irule ifexp_root_condition_scopes >> goal_assum (drule_at Any)) >>
  decide_tac
QED
