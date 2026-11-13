(* A small forced-value interface for target index sequencing. *)
Theory bodyIntCallFamStmtMutationAugIndexOutcome
Ancestors
  bodyIntCallJointContract gasOutcome gasSummary
  exprSimAggregateLoops exprSimHypsDefs exprSimDefs loweringPosts
  supportedExprs vyperInterpreter vyperState exprLowering compileEnv

Theorem intcall_forced_index_outcome:
  intcall_forced_producer fp e /\
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env e es /\
  supported_expr fp.jc_tops e /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  lower_value compile_expr ce (expr_type e) e sm = (ix,sn) /\
  fn_has_code sm sn fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  gas_admissible (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
    expr_res_ok es /\
  intcall_expr_res fp ce env es sm t /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) (es,t)
    (\res ee u. ?key. res = INL key /\
      expr_val_rel fp.jc_cx (post_value_type ce e) key ix u /\
      (!x. ix = Var x ==> not_fresh_at sn x) /\
      intcall_expr_cont fp ce env es sm t ee sn u)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `intcall_forced_producer fp e` mp_tac >>
  rewrite_tac[intcall_forced_producer_def] >>
  disch_then (qspecl_then [`ce`, `env`, `es`, `sm`, `sn`, `t`,
    `expr_type e`, `ix`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  irule aggregate_tuple_gas_outcome_mono >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED
