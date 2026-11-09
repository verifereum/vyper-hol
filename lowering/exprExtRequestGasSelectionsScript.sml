(* Carry the captured operands and selected keywords through optional GAS. *)
Theory exprExtRequestGasSelections
Ancestors
  exprExtRequestKwargs exprExtRequestOptionalGas exprExtRequestHistoryCompose
  exprExtRequestHistory exprExtRequestStrongCapture exprExtRequestRetained
  exprLoweringProps loweringPosts compileEnv

Theorem extrequest_kwargs_gas_endpoint:
  extrequest_kwargs_post ctx func ce cx rt opts kwargs es sa s0 sm
    value_op gas_op default_op old_es old_rs old_vvs vs ee s /\
  (case gas_op of SOME g => (g,sm) | NONE => emit_op GAS [] sm) = (gas,sn) /\
  fn_has_code sm sn func ==>
  ?t gw.
    gas_marked_path F ctx func s (if IS_NONE gas_op then 1 else 0) (OK t) /\
    eval_operand gas t = SOME gw /\ safe_operand sn gas /\
    stmt_state_rel ctx func ce cx ee t /\
    extrequest_history_frame ce cx ee sm s ee sn t /\
    wb_frame ce ee sm s t /\ ci_mono sm sn /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    (!op w. safe_operand sm op /\ eval_operand op s = SOME w ==>
       eval_operand op t = SOME w) /\
    extrequest_strong_captures ctx func ce cx old_es old_rs old_vvs ee sn t /\
    extrequest_kwarg_selection ce cx rt EKValue
      (ext_call_kwarg EKValue opts vs) (OPTION_MAP (\op. (op,rt)) value_op) ee sn t /\
    extrequest_kwarg_selection ce cx rt EKGas
      (ext_call_kwarg EKGas opts vs) (OPTION_MAP (\op. (op,rt)) gas_op) ee sn t /\
    extrequest_kwarg_selection ce cx rt EKDefault
      (ext_call_kwarg EKDefault opts vs) default_op ee sn t
Proof
  strip_tac >>
  `!g. gas_op = SOME g ==> safe_operand sm g /\ IS_SOME (eval_operand g s)` by
    (rpt strip_tac >> fs[extrequest_kwargs_post_def] >>
     qpat_x_assum `extrequest_kwarg_selection _ _ _ EKGas _ _ _ _ _` mp_tac >>
     simp[extrequest_kwarg_selection_def] >> strip_tac >>
     Cases_on `ext_call_kwarg EKGas opts vs` >> gvs[] >>
     fs[extrequest_retained_value_def, expr_val_rel_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce sm /\
   ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
   s.vs_inst_idx = LENGTH sm.cs_current_insts` by fs[extrequest_kwargs_post_def] >>
  drule_all extrequest_optional_gas_endpoint >> strip_tac >>
  qexistsl_tac [`t`,`gw`] >> simp[] >>
  fs[extrequest_kwargs_post_def] >>
  conj_tac >- (irule extrequest_strong_captures_history >> metis_tac[]) >>
  rpt conj_tac >> irule extrequest_kwarg_selection_transport >> metis_tac[]
QED
