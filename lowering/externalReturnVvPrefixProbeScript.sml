Theory externalReturnVvPrefixProbe
Ancestors
  exprSimDefs loweringPosts gasOutcome gasSummary exprLowering
  stmtSimReturn exprSimMemorySource vyperAST

Theorem return_vv_located_tag:
  vv_post ctx func ce cx e es sa sb s0 es' tv (LocatedValue ty p) s ==>
  ty = expr_type e
Proof
  simp[vv_post_def, vv_holds_def]
QED

(* Exercise the universal simulation at its actual compile_expr prefix,
   not by aligning an independent lower_value execution. *)
Theorem return_vv_located_prefix:
  expr_vv_sim ctx func ce cx ct e es /\
  compile_expr ce ct e sa = (LocatedValue ty p, sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee s. ?tv. res = INL tv /\ ty = expr_type e /\
      vv_post ctx func ce cx e es sa sb s0 ee tv (LocatedValue ty p) s /\
      s.vs_current_bb = sb.cs_current_bb /\
      s.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_def] >> disch_then drule_all >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  metis_tac[return_vv_located_tag]
QED

Theorem return_site_vv_admissible:
  gas_admissible (eval_stmt cx (Return (SOME e))) (stmt_res_ok lctx) es ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  strip_tac >> drule return_forced_admissible >>
  metis_tac[forced_expr_admissible_raw]
QED

Theorem return_intcall_vv_prefix:
  expr_vv_sim ctx func ce cx ct (Call ann (IntCall fid) args drv) es /\
  compile_expr ce ct (Call ann (IntCall fid) args drv) sa =
    (LocatedValue (ce.ce_func_return_type (nsid_to_string fid)) p, sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (eval_stmt cx (Return (SOME (Call ann (IntCall fid) args drv))))
    (stmt_res_ok lctx) es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_expr cx (Call ann (IntCall fid) args drv)) (es,s0)
    (\res ee s. ?tv. res = INL tv /\
      ce.ce_func_return_type (nsid_to_string fid) = ann /\
      vv_post ctx func ce cx (Call ann (IntCall fid) args drv) es sa sb s0 ee tv
        (LocatedValue (ce.ce_func_return_type (nsid_to_string fid)) p) s /\
      s.vs_current_bb = sb.cs_current_bb /\
      s.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule return_site_vv_admissible >> strip_tac >>
  drule_all return_vv_located_prefix >> simp[expr_type_def]
QED
