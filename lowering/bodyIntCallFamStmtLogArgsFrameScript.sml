(* Resource and ordinary frames for the Log argument traversal. *)
Theory bodyIntCallFamStmtLogArgsFrame
Ancestors
  bodyIntCallJointContract exprSimWordArgs wordArgsPtr loweringPosts

Theorem intcall_expr_cont_frame:
  intcall_expr_cont fp ce env es sa s ee sb u <=>
  intcall_expr_res fp ce env ee sb u /\ ~u.vs_halted /\
  u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  wb_frame ce es sa s u /\ s.vs_alloca_next <= u.vs_alloca_next
Proof
  simp[intcall_expr_cont_def, wb_frame_def] >> metis_tac[]
QED

Theorem intcall_expr_cont_trans:
  intcall_expr_res fp ce env es sa s /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  intcall_expr_cont fp ce env es sa s mid sm t /\
  intcall_expr_cont fp ce env mid sm t ee sb u ==>
  intcall_expr_cont fp ce env es sa s ee sb u
Proof
  rpt strip_tac >>
  `wb_frame ce es sa s t /\ wb_frame ce mid sm t u` by
    fs[intcall_expr_cont_frame] >>
  `wb_frame ce es sa s u` by
    (fs[intcall_joint_res_def, intcall_expr_res_def] >> drule_all wb_frame_trans >> simp[]) >>
  fs[intcall_expr_cont_frame]
QED
