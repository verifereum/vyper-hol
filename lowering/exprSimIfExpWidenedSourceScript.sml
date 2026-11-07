Theory exprSimIfExpWidenedSource
Ancestors
  exprSimIfExpWidenedAdapter exprSimHypsDefs exprSimDefs gasContext
  gasSummary loweringPosts vyperState exprSimProps

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
