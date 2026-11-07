Theory exprSimIfExpWidenedSource
Ancestors
  exprSimIfExpWidenedAdapter exprSimHypsDefs exprSimDefs gasContext
  gasSummary loweringPosts vyperState exprSimProps stmtReasonVvMemory exprSimMemorySource

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
