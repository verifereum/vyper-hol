(* Projection of the joint forced producer to the public sequencing post. *)
Theory bodyIntCallFamAggSubscriptForcedOutcome
Ancestors
  bodyIntCallJointContract exprSimSubscriptMap loweringPosts

Theorem intcall_forced_post_outcome:
  intcall_forced_producer fp e /\
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env e es /\
  supportedExprs$supported_expr fp.jc_tops e /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  lower_value compile_expr ce ty e sa = (op,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  gas_admissible (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
    expr_res_ok es /\
  intcall_joint_res fp ce env es sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) (es,s)
    (\res ee u. ?v. res = INL v /\
      expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sb s ee v op u /\
      intcall_expr_cont fp ce env es sa s ee sb u)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `intcall_forced_producer _ _` mp_tac >>
  rewrite_tac[intcall_forced_producer_def] >>
  disch_then drule_all >> strip_tac >>
  irule gas_outcome_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> qexists_tac `v` >>
  fs[expr_post_def, intcall_expr_cont_def, intcall_joint_res_def] >>
  metis_tac[]
QED
