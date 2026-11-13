(* Immediate-read source glue; prefix reach and replay are reused unchanged. *)
Theory exprExtRequestSnapshotSource
Ancestors
  exprExtRequestKwargs exprExtRequestReplay exprExtRequestGasBind
  exprSimWordArgs exprSimHypsDefs gasSummary vyperState vyperInterpreter
  gasContext exprSimDefs

Theorem extrequest_snapshot_source_tail_admissible:
  gas_admissible (bind (eval_exprs cx (e::xs)) k) expr_vv_res_ok es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := used ++ tail) = (INL v,mid with gas_obs := tail)) ==>
  gas_admissible (bind (eval_exprs cx xs) (\vs. k (v::vs)))
    expr_vv_res_ok (mid with gas_obs := [])
Proof
  simp[eval_exprs_cons_action, bind_assoc, bind_return] >>
  once_rewrite_tac[GSYM bind_assoc] >> strip_tac >>
  drule_all stmtSimForRoundsTheory.gas_admissible_bind_tail >> simp[]
QED

Theorem extrequest_snapshot_source_head_admissible:
  gas_admissible (bind (eval_exprs cx (e::xs)) k) expr_vv_res_ok es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  simp[eval_exprs_cons_action, bind_assoc, bind_return] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  simp[bind_def, expr_vv_res_ok_def, expr_res_ok_def]
QED

Theorem extrequest_snapshot_source_tail_case:
  exprs_case nocalls ctx func ce cx (e::xs) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
  exprs_case nocalls ctx func ce cx xs
Proof
  simp[exprs_case_def, bind_def, AllCaseEqs()] >> metis_tac[]
QED
