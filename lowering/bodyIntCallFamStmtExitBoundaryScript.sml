(* Joint reason endpoints: abort consumes no resource continuation. *)
Theory bodyIntCallFamStmtExitBoundary
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtExitReason stmtReasonVvMemory
  loweringPosts exprSimDefs exprLoweringProps exprLowering compileEnv bodySim context
  stmtSimReasonExpr stmtSimReasonStorage exprReasonOperand bodySimStmtCases

Theorem intcall_expr_endpoint_vv_post:
  intcall_expr_cont fp ce env es sa s ee sb u /\
  vv_holds ce fp.jc_cx (post_value_type ce e) tv vv ee u /\
  vv_at ce fp.jc_cx (post_value_type ce e) sa sb ee tv vv u /\
  (post_value_type ce e <> expr_type e ==>
    vv_own ce fp.jc_cx (post_value_type ce e) sa sb ee tv vv u) /\
  (~expr_has_effect e ==> vv_storage_live fp.jc_cx vv ee u) ==>
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sb s ee tv vv u
Proof
  simp[intcall_expr_cont_def, intcall_joint_res_def, intcall_expr_res_def, vv_post_def] >>
  metis_tac[]
QED

Theorem intcall_reason_abort_path:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env ee sa s /\
  vv_holds ce fp.jc_cx ty tv vv ee s /\
  (reason_vv_ok vv \/ reason_storage_vv vv \/ reason_code_vv vv) /\
  compile_revert_with_reason ce vv mt ms sa = ((),sb) /\
  fn_has_code sa sb fp.jc_func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path fp.jc_ctx fp.jc_func s 0 (Abort Revert_abort t)
Proof
  strip_tac >>
  `?a. eval_operand (vv_operand vv) s = SOME a` by
    (Cases_on `vv` >>
     fs[vv_holds_def, vv_operand_def, expr_val_rel_def]) >>
  irule reason_encoder_abort_path >>
  goal_assum (drule_at Any) >> simp[] >>
  fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_def] >>
  fs[intcall_frame_ok_def, same_frame_def, compile_env_component_equality] >>
  metis_tac[]
QED

Theorem supported_reason_encoder_shape:
  expr_sim_inv ce cx env es /\ supported_string_reason tops e /\
  well_typed_expr env e /\ compile_expr ce (expr_type e) e sa = (vv,sb) ==>
  reason_vv_ok vv \/ reason_storage_vv vv \/ reason_code_vv vv
Proof
  strip_tac >> Cases_on `reason_covered ce e`
  >- (fs[reason_covered_def] >> metis_tac[]) >>
  drule_all supported_reason_code >> simp[]
QED
