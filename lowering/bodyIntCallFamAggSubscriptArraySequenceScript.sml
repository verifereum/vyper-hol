(* Counted index sequencing retaining the resource continuation. *)
Theory bodyIntCallFamAggSubscriptArraySequence
Ancestors
  bodyIntCallFamAggSubscriptForcedOutcome bodyIntCallJointContract
  exprSimSubscriptArrayCompose exprSimSubscriptArraySource exprSimDefs
  exprSimHypsDefs

Theorem intcall_framed_array_after_base:
  gas_marked_exec F (fp.jc_ctx,fp.jc_func) (eval_expr fp.jc_cx obj)
    (es,s0) left (INL captured) mid (OK t) /\
  intcall_forced_producer fp idx /\
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env idx (mid with gas_obs := []) /\
  supportedExprs$supported_expr fp.jc_tops idx /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr idx) /\
  lower_value compile_expr ce ty idx sm = (iop,si) /\
  fn_has_code sm si fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  gas_admissible (bind (eval_expr fp.jc_cx idx) (read_result fp.jc_cx)) expr_res_ok
    (mid with gas_obs := []) /\
  intcall_expr_res fp ce env (mid with gas_obs := []) sm t /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!imarks raw v u.
     gas_marked_exec F (fp.jc_ctx,fp.jc_func)
       (bind (eval_expr fp.jc_cx idx) (read_result fp.jc_cx))
       (mid with gas_obs := [],t) imarks (INL v) raw (OK u) /\
     expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx idx (mid with gas_obs := []) sm si t
       (raw with gas_obs := []) v iop u /\
     intcall_expr_cont fp ce env (mid with gas_obs := []) sm t
       (raw with gas_obs := []) si u ==>
     gas_summary_at F (fp.jc_ctx,fp.jc_func) []
       (select_result fp.jc_cx (expr_type obj) captured (ValueSubscript v))
       (raw with gas_obs := [],u) Q (\res ee out. expr_exit res out)) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_expr fp.jc_cx (Subscript ann obj idx)) (es,s0)
    Q (\res ee out. expr_exit res out)
Proof
  strip_tac >>
  drule_all intcall_forced_post_outcome >> strip_tac >>
  pure_once_rewrite_tac[eval_expr_subscript_bind] >>
  irule (BETA_RULE (Q.ISPEC `\r v. select_result fp.jc_cx (expr_type obj) r (ValueSubscript v)`
    (Q.GEN `k` framed_array_index_outcome_compose))) >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  qexists_tac `\v ee u.
    expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx idx (mid with gas_obs := []) sm si t ee v iop u /\
    intcall_expr_cont fp ce env (mid with gas_obs := []) sm t ee si u` >> simp[] >>
  `(!res out. (?exc. res = (INR exc : value + exception) /\
        expr_exit (INR exc : eval_result + exception) out) = expr_exit res out)` by
    (gen_tac >> Cases_on `res` >> simp[] >> rename1 `INR exc` >>
     qspec_then `Value` (mp_tac o REWRITE_RULE [FUN_EQ_THM]) expr_exit_success_map >>
     disch_then (qspec_then `INR exc : value + exception` mp_tac) >> simp[]) >>
  simp[] >> first_assum ACCEPT_TAC
QED
