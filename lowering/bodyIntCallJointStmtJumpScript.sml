(* Control-only transport for the joint statement resource invariant. *)
Theory bodyIntCallJointStmtJump
Ancestors
  bodyIntCallJointContract bodyIntCallJointStmtBoundary exprLoweringProps
  stmtSimProps bodyMemoryDefs intCallFrame compileEnv loweringStateRelDefs venomState venomExecSemantics

Theorem intcall_joint_res_jump_to:
  intcall_joint_res fp ce env es sa (jump_to lbl s) <=>
  intcall_joint_res fp ce env es sa s
Proof
  simp[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_jump_to, ret_pc_ok_jump_to,
       return_buf_frame_jump_to, allocas_above_def, local_region_def,
       jump_to_def, eval_operand_def, lookup_var_def]
QED
