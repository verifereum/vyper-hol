Theory exprBodyPreCallSafetyProps
Ancestors exprSimHypsDefs

Theorem expr_body_pre_mods_call_evaluation_safe:
  expr_body_pre_mods mods cenv cx env e es ==>
  call_evaluation_safe cx (int_calls_expr e)
Proof
  simp[expr_body_pre_mods_def]
QED

Theorem expr_body_pre_call_evaluation_safe:
  expr_body_pre cenv cx env e es ==> call_evaluation_safe cx (int_calls_expr e)
Proof
  simp[expr_body_pre_split_def] >>
  metis_tac[expr_body_pre_mods_call_evaluation_safe]
QED
