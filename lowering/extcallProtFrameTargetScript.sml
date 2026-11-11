(* Word forcing keeps its memory resources at the semantic endpoint. *)
Theory extcallProtFrameTarget
Ancestors
  bodyIntCallForcingReadOnly exprSimUnwrapProps exprSimUnwrap
  exprExtRequestTargetCps exprExtRequestGasBind exprSimHyps
  exprLoweringProps loweringPosts fragGasMode vyperInterpreter vyperState
  compileEnv venomState finite_map exprLowering gasSummary exprSimMemorySource

Theorem word_unwrap_readonly_post:
  post_value_type ce e = expr_type e /\ is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  unwrap_value ce vv sm = (op,sb) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_exec F (ctx,func) (read_result cx raw) (ee,s)
        [] (INL v) ee (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `vv_post ctx func ce cx e es sa sm s0 ee (Value v) vv s` by
    metis_tac[vv_post_read_result] >>
  Cases_on `vv`
  >- (gvs[unwrap_value_def, comp_return_def] >> qexists `s` >>
      simp[] >> conj_tac
      >- (simp[gas_marked_exec_def, gas_marked_path_def] >>
          metis_tac[read_result_gas_obs, fragGasPathTheory.gas_path_rules]) >>
      gvs[vv_post_def, vv_holds_def, vv_at_def, expr_post_def,
          read_result_def, return_def] >> metis_tac[]) >>
  rename1 `LocatedValue ann p` >>
  `vv_holds ce cx (expr_type e) (Value v) (LocatedValue ann p) ee s /\
   stmt_state_rel ctx func ce cx ee s` by gvs[vv_post_def] >>
  drule protected_word_value_forcing >>
  disch_then (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >> simp[] >>
  disch_then (qspecl_then [`ee.scopes`, `\q. ?x. q = Var x /\ not_fresh_at sm x`, `func`, `ctx`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next` by
    (rpt conj_tac >> qpat_assum `u = _` (fn th => simp[Once th])) >>
  qexists `u` >> simp[] >> conj_tac
  >- (simp[gas_marked_exec_def] >> metis_tac[read_result_gas_obs]) >>
  irule expr_post_of_vv_post_load >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- gvs[expr_val_rel_def] >>
  qexistsl [`p`, `s`, `sm`, `ann`] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!q. _ ==> eval_operand q u = eval_operand q s`
    (qspec_then `Var x` mp_tac) >> simp[eval_operand_def]
QED
