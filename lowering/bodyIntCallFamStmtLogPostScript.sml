(* Ordinary post projection from a joint forced-result endpoint. *)
Theory bodyIntCallFamStmtLogPost
Ancestors
  bodyIntCallJointContract loweringPosts

Theorem intcall_forced_expr_post:
  intcall_expr_cont fp ce env es sa s ee sb u /\
  expr_val_rel fp.jc_cx (post_value_type ce e) v op u /\
  expr_val_at ce fp.jc_cx (post_value_type ce e) sa sb ee v op u /\
  (post_value_type ce e <> expr_type e ==>
   expr_val_own ce fp.jc_cx (post_value_type ce e) sa sb ee v op u) ==>
  expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sb s ee v op u
Proof
  simp[expr_post_def, intcall_expr_cont_def, intcall_joint_res_def, intcall_expr_res_def] >>
  metis_tac[]
QED
