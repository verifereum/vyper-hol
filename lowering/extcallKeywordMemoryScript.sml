(* Counted forced keywords: value, gas, and a word default. *)
Theory extcallKeywordMemory
Ancestors
  exprSimMemDefs stmtReasonVvMemory exprSimDefs exprLowering
  exprSimProps gasOutcome loweringPosts vyperState compileEnv

Theorem extcall_word_keyword_mem_cps:
  compile_ext_call_kwarg compile_expr ce rt key e sa = ((op,rt),sb) /\
  (key <> EKDefault \/ is_word_type rt) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  stmt_state_rel ctx func ce cx es s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  expr_sim_mem ctx func ce cx
    (if key = EKDefault then rt else BaseT (UintT 256)) e es /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  (!v mid t.
     expr_post ctx func ce cx e es sa sb s mid v op t /\
     expr_store_bound cx (expr_type e) v op t /\
     t.vs_current_bb = sb.cs_current_bb /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts /\
     alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next ==>
     gas_outcome T (cx_tops cx) (ctx,func) (next v) (mid,t) Q
       (\res ee r. expr_exit res r)) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx)) next)
    (es,s) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `lower_value compile_expr ce
     (if key = EKDefault then rt else BaseT (UintT 256)) e sa = (op,sb)` by
    (gvs[compile_ext_call_kwarg_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `op`, `s`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  irule gas_outcome_bind_value >>
  goal_assum (drule_at Any) >> conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def] >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED
