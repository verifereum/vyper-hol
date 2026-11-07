Theory exprSimIfExpWidenedMarked
Ancestors
  exprSimIfExpWidenedArm exprSimAbiGasBridge exprSimHash
  loweringPosts exprLoweringProps compileEnv venomState venomExecSemantics

Theorem expr_post_returndata:
  expr_post ctx func ce cx e es sa sb s0 ee v op
    (s with vs_returndata := rd) <=>
  expr_post ctx func ce cx e es sa sb s0 ee v op s
Proof
  Cases_on `op` >> simp[expr_post_def, hash_returndata_state_rel, expr_val_rel_def,
    expr_val_at_def, expr_val_own_def, locals_kept_def,
    eval_operand_def, lookup_var_def, local_region_def]
QED
