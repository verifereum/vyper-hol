Theory extRetPostInputsPtr
Ancestors
  bodyPtrDefs loweringPosts stmtSimDefs ptrDiscipline venomExecSemantics

Theorem expr_post_value_ptr_return_inputs:
  !ctx fn cenv cx e es sa sb s0 es' v op s d G tn.
    expr_post ctx fn cenv cx e es sa sb s0 es' v op s /\
    ghost_inv d cenv cx es' G tn s /\
    ptr_val_ok cx (post_value_type cenv e) v op G tn s ==>
    stmt_state_rel ctx fn cenv cx es' s /\
    (?w. eval_operand op s = SOME w) /\ op_taint tn op = {} /\
    stor_taint_ok cx tn s
Proof
  simp[expr_post_def, expr_val_rel_def, ghost_inv_def, ptr_val_ok_def] >>
  metis_tac[]
QED
