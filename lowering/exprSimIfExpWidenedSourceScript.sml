Theory exprSimIfExpWidenedSource
Ancestors
  exprSimIfExpWidenedAdapter exprSimHypsDefs exprSimDefs gasContext
  gasSummary loweringPosts vyperState exprSimProps stmtReasonVvMemory exprSimMemorySource
  stmtSimIfProps vyperInterpreter
Libs
  monadsyntax

Theorem conditional_raw_admissible:
  gas_admissible (bind a (conditional_result cx)) expr_vv_res_ok es ==>
  gas_admissible a expr_vv_res_ok es
Proof
  rw[gas_admissible_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  simp[bind_def] >>
  Cases_on `res` >> simp[expr_vv_res_ok_def] >>
  rename1 `INL raw` >> Cases_on `raw` >>
  simp[conditional_result_def, raise_def, expr_vv_res_ok_def]
QED

Theorem conditional_marked_read_success:
  gas_marked_exec memory (ctx,func) a (es,s0) marks (INL raw) mid (OK t) /\
  gas_admissible (bind a (conditional_result cx)) expr_vv_res_ok es /\
  vv_post ctx semantic_func ce cx e es sa sb s0 mid raw vv t ==>
  ?tv v.
    conditional_result cx raw (mid with gas_obs := []) =
      (INL tv,mid with gas_obs := []) /\
    read_result cx tv (mid with gas_obs := []) =
      (INL v,mid with gas_obs := [])
Proof
  rpt strip_tac >>
  drule_all gas_marked_continuation_admissible >> strip_tac >>
  drule vv_post_read_ok >> strip_tac >>
  drule read_result_gas_obs >> disch_then (qspec_then `[]` assume_tac) >>
  Cases_on `conditional_result cx raw (mid with gas_obs := [])` >>
  `expr_vv_res_ok q` by
    (qpat_x_assum `gas_admissible (conditional_result cx raw) _ _` mp_tac >>
     simp[gas_admissible_def] >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all conditional_readable_admissible >> strip_tac >>
  metis_tac[]
QED

Theorem ifexp_forced_source:
  eval_expr cx (IfExp ann c a b) =
  vyperState$bind (vyperState$bind (eval_expr cx c) (read_result cx))
    (\v. if v = BoolV T then vyperState$bind (eval_expr cx a) (conditional_result cx)
         else if v = BoolV F then vyperState$bind (eval_expr cx b) (conditional_result cx)
         else raise (Error (TypeError "not BoolV")))
Proof
  simp[Once evaluate_def, switch_BoolV_def, bind_assoc] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >>
  rpt IF_CASES_TAC >> simp[SF ETA_ss] >>
  simp[FUN_EQ_THM, vyperStateTheory.bind_def, raise_def]
QED

Theorem ifexp_forced_condition_admissible:
  gas_admissible (eval_expr cx (IfExp ann c a b)) expr_vv_res_ok es ==>
  gas_admissible (vyperState$bind (eval_expr cx c) (read_result cx))
    (\r. expr_res_ok r /\ (!v. r = INL v ==> ?sel. v = BoolV sel)) es
Proof
  simp[ifexp_forced_source, gas_admissible_def] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `gs` mp_tac) >> simp[bind_def] >>
  Cases_on `r` >> simp[expr_res_ok_def, expr_vv_res_ok_def] >>
  rename1 `INL v` >> Cases_on `v` >>
  simp[raise_def, expr_vv_res_ok_def] >> metis_tac[]
QED

Theorem ifexp_marked_branch_admissible:
  gas_admissible (eval_expr cx (IfExp ann c a b)) expr_vv_res_ok es /\
  gas_marked_exec memory (ctx,func)
    (vyperState$bind (eval_expr cx c) (read_result cx))
    (es,s0) marks (INL (BoolV sel)) mid (OK t) ==>
  gas_admissible
    (vyperState$bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
    expr_vv_res_ok (mid with gas_obs := [])
Proof
  rewrite_tac[ifexp_forced_source] >> strip_tac >>
  drule_all gas_marked_continuation_admissible >>
  Cases_on `sel` >> simp[]
QED
