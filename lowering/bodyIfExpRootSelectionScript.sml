Theory bodyIfExpRootSelection
Ancestors
  exprSimDefs exprSimMemDefs exprSimProps loweringPosts exprSimIfExp
  gasOutcome gasExemptCert gasSummary gasContext fragGasMode fragGasPath
  gasSummaryCompose fragExec
  fragGasPathMem vyperState vyperInterpreter vyperAST allocaHistoryFragment
  vyperEvalExprPreservesScopesDom exprLoweringProps allocaHistory venomState

Theorem ifexp_root_eval_forced:
  eval_expr cx (IfExp t c a b) =
  vyperState$bind (vyperState$bind (eval_expr cx c) (read_result cx))
    (\v. if v = BoolV T then vyperState$bind (eval_expr cx a) (conditional_result cx)
         else if v = BoolV F then vyperState$bind (eval_expr cx b) (conditional_result cx)
         else raise (Error (TypeError "not BoolV")))
Proof
  simp[Once evaluate_def, switch_BoolV_def, vyperStateTheory.bind_assoc] >>
  simp[FUN_EQ_THM, vyperStateTheory.bind_def] >> gen_tac >>
  Cases_on `eval_expr cx c x` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw` >> simp[] >>
  rename1 `read_result cx captured st` >>
  Cases_on `read_result cx captured st` >> rename1 `_ = (forced,sf)` >>
  Cases_on `forced` >> simp[] >> rpt IF_CASES_TAC >>
  simp[raise_def, vyperStateTheory.bind_def]
QED

Theorem ifexp_root_condition_admissible:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es ==>
  gas_admissible (vyperState$bind (eval_expr cx c) (read_result cx)) expr_res_ok es
Proof
  rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  qpat_x_assum `!gs res ee. _` (qspec_then `gs` mp_tac) >>
  simp[ifexp_root_eval_forced, vyperStateTheory.bind_def] >>
  fs[expr_vv_res_ok_def, expr_res_ok_def] >> metis_tac[]
QED

Theorem ifexp_root_branch_admissible:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  (!tail. vyperState$bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := xs ++ tail) = (INL (BoolV sel),mid with gas_obs := tail)) ==>
  gas_admissible
    (vyperState$bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
    expr_vv_res_ok (mid with gas_obs := [])
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `!gs res ee. _` (qspec_then `xs ++ gs` mp_tac) >>
  simp[ifexp_root_eval_forced, vyperStateTheory.bind_def] >>
  Cases_on `sel` >> gvs[]
QED

Theorem ifexp_root_condition_bool:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  vyperState$bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := gs) = (INL v,mid) ==>
  ?sel. v = BoolV sel
Proof
  strip_tac >>
  Cases_on `v = BoolV T` >- metis_tac[] >>
  Cases_on `v = BoolV F` >- metis_tac[] >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def, ifexp_root_eval_forced] >>
  disch_then (qspec_then `gs` mp_tac) >>
  simp[vyperStateTheory.bind_def, raise_def, expr_vv_res_ok_def]
QED

Theorem ifexp_root_condition_cert:
  gas_exempt_cert memory tops (ctx,func)
    (vyperState$ignore_bind
      (vyperState$bind (eval_expr cx c) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,finalst) ==>
  gas_exempt_cert memory tops (ctx,func)
    (vyperState$ignore_bind (eval_expr cx (IfExp t c a b)) (return ()))
    (es,s0) marks (err,ee) (leaf,finalst)
Proof
  strip_tac >> rewrite_tac[ifexp_root_eval_forced] >>
  pure_once_rewrite_tac[vyperStateTheory.ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem ifexp_condition_exit_mem:
  gas_marked_exec T (ctx,func)
    (vyperState$bind (eval_expr cx c) (read_result cx))
    (es,s0) marks res mid r /\ expr_exit res r ==>
  gas_outcome T tops (ctx,func) (eval_expr cx (IfExp t c a b)) (es,s0) Q
    (\res ee r. expr_exit res r)
Proof
  Cases_on `res` >> simp[] >> strip_tac >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR y`,`mid`,`r`] >> simp[] >>
  conj_tac
  >- (rewrite_tac[ifexp_root_eval_forced] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >>
  Cases_on `r` >> fs[expr_exit_def, exit_result_def] >>
  Cases_on `y` >> fs[expr_exit_def] >>
  rename1 `Error er` >> Cases_on `er` >> fs[expr_exit_def]
QED

Theorem ifexp_root_condition_scopes:
  vyperState$bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := gs) = (INL v,mid) ==>
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  simp[vyperStateTheory.bind_def] >>
  Cases_on `eval_expr cx c (es with gas_obs := gs)` >>
  rename1 `_ = (raw,st)` >> Cases_on `raw` >> simp[] >> strip_tac >>
  drule read_result_state >> strip_tac >> gvs[] >>
  drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]
QED

Theorem ifexp_root_condition_dispatch_mem:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  gas_outcome T tops (ctx,func)
    (bind (eval_expr cx c) (read_result cx)) (es,s0) P
    (\res ee r. expr_exit res r) /\
  (!res ee u. P res ee u ==> ?v. res = INL v) /\
  (!marks sel mid u.
    gas_marked_exec T (ctx,func) (bind (eval_expr cx c) (read_result cx))
      (es,s0) marks (INL (BoolV sel)) mid (OK u) /\
    P (INL (BoolV sel)) (mid with gas_obs := []) u ==>
    gas_outcome T tops (ctx,func) (eval_expr cx (IfExp t c a b)) (es,s0) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome T tops (ctx,func) (eval_expr cx (IfExp t c a b)) (es,s0) Q
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (gvs[] >>
      `?sel. res = INL (BoolV sel)` by
        (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
         simp[gas_marked_exec_def] >> strip_tac >>
         first_x_assum (qspec_then `[]` assume_tac) >>
         Cases_on `res` >- metis_tac[ifexp_root_condition_bool] >>
         first_x_assum drule >> simp[]) >>
      gvs[] >> qpat_x_assum `!marks sel mid u. _` mp_tac >>
      simp[gas_outcome_def, gas_summary_at_def] >>
      disch_then drule_all >> simp[])
  >- (simp[] >> irule (SRULE [gas_outcome_def, gas_summary_at_def] ifexp_condition_exit_mem) >>
      goal_assum (drule_at Any) >> fs[]) >>
  simp[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule ifexp_root_condition_cert >> simp[]
QED

Theorem ifexp_selected_entry_facts_mem:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  gas_marked_exec T (ctx,func) (bind (eval_expr cx c) (read_result cx))
    (es,s0) marks (INL (BoolV sel)) mid (OK u) /\
  expr_post ctx func ce cx c es sa sc s0 (mid with gas_obs := [])
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
  stmt_state_rel ctx func ce cx (mid with gas_obs := []) (jump_to lbl u) /\
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
