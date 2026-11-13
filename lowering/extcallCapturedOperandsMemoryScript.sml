(* Target evaluation followed by unread positional captures. *)
Theory extcallCapturedOperandsMemory
Ancestors
  extcallPositionalMemory exprSimMemDefs exprSimDefs exprSimSubscriptMap
  exprLoweringProps exprSimWordArgs gasOutcome gasSummaryCompose
  vyperInterpreter vyperState fragExec allocaHistory stmtReasonVvMemory

Theorem extcall_target_positional_mem_cps:
  lower_value compile_expr ce (BaseT AddressT) target sa = (addr,sm) /\
  compile_multi_vvs compile_expr ce pos sm = (vvs,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  stmt_state_rel ctx func ce cx es s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  expr_sim_mem ctx func ce cx (BaseT AddressT) target es /\
  gas_admissible (bind (eval_expr cx target) (read_result cx)) expr_res_ok es /\
  (!tv mid t.
     expr_post ctx func ce cx target es sa sm s mid tv addr t /\
     expr_store_bound cx (expr_type target) tv addr t /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts /\
     alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next ==>
     Capture tv [] [] mid t sm) /\
  (!tv rs vs st t sc.
     Capture tv rs vs st t sc ==>
     local_ptrs_reserved ce sc /\ stmt_state_rel ctx func ce cx st t /\
     alloca_history func t /\ ~t.vs_halted /\
     t.vs_current_bb = sc.cs_current_bb /\
     t.vs_inst_idx = LENGTH sc.cs_current_insts) /\
  (!tv e rs vs st t sc.
     MEM e pos /\ Capture tv rs vs st t sc ==>
     expr_vv_sim_mem ctx func ce cx (expr_type e) e st /\
     gas_admissible (eval_expr cx e) expr_vv_res_ok st) /\
  (!tv e rs vs st t sc sn vv r fin u.
     MEM e pos /\ Capture tv rs vs st t sc /\
     compile_expr ce (expr_type e) e sc = (vv,sn) /\
     vv_post ctx func ce cx e st sc sn t fin r vv u /\
     vv_store_bound cx (expr_type e) (lowered_value_type ce e) fin r vv u /\
     u.vs_current_bb = sn.cs_current_bb /\
     u.vs_inst_idx = LENGTH sn.cs_current_insts /\
     alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next ==>
     Capture tv (rs ++ [r]) (vs ++ [vv]) fin u sn) /\
  (!tv rs vs st t.
     Capture tv rs vs st t sb ==>
     gas_outcome T (cx_tops cx) (ctx,func) (next tv rs vs) (st,t) Q
       (\res ee r. expr_exit res r)) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx target) (read_result cx))
      (\tv. bind (eval_expr_results cx pos) (\rs. next tv rs vvs)))
    (es,s) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `addr`, `s`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  irule gas_outcome_bind_value >>
  goal_assum (drule_at Any) >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      `Capture v [] [] (mid with gas_obs := []) t sm` by metis_tac[] >>
      qspecl_then [`pos`, `sm`, `vvs`, `sb`, `[]`, `[]`,
                   `mid with gas_obs := []`, `t`] mp_tac
        (Q.INST [`P` |-> `Capture (v:value)`, `k` |-> `next (v:value)`]
          extcall_positional_mem_cps) >>
      simp[] >> disch_then irule >> rpt conj_tac >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def] >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED
