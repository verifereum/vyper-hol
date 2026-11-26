Theory createSizeRawGasAdmissibleMods
Ancestors
  gasContext createSizeRawEvalTypingMods createSizeRawResultShapeMods

Theorem create_raw_gas_admissible_mods:
  expr_body_pre_mods mods ce cx env e es ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  rw[gas_admissible_def] >>
  drule_all create_raw_eval_typing_at_obs_mods >> strip_tac >>
  drule_all create_raw_eval_vv_ok >> simp[]
QED

