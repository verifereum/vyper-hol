(* Counted sequencing after the copied base has been captured as a Value. *)
Theory exprSimCopiedCompose
Ancestors
  exprSimSubscriptArrayCompose exprSimSubscriptArraySource
  exprSimDefs vyperInterpreter vyperState gasOutcome gasSummary
  gasSummaryCompose gasExemptCert

Theorem eval_expr_subscript_copied_bind:
  subscript_reads_base cx obj idx ==>
  eval_expr cx (Subscript ann obj idx) =
  bind (bind (eval_expr cx obj) (\r.
          bind (read_result cx r) (\v. return (Value v)))) (\captured.
    bind (bind (eval_expr cx idx) (read_result cx)) (\v.
      select_result cx (expr_type obj) captured (ValueSubscript v)))
Proof
  strip_tac >> simp[Once evaluate_def, bind_assoc, bind_return]
QED

Theorem copied_array_after_capture:
  subscript_reads_base cx obj idx /\
  gas_marked_exec F (ctx,func)
    (bind (eval_expr cx obj) (\r. bind (read_result cx r) (\v. return (Value v))))
    (es,s0) left (INL captured) mid (OK t) /\
  expr_sim ctx func ce cx ty idx (mid with gas_obs := []) /\
  lower_value compile_expr ce ty idx sm = (iop,si) /\
  fn_has_code sm si func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\
  gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok
    (mid with gas_obs := []) /\
  stmt_state_rel ctx func ce cx (mid with gas_obs := []) t /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!imarks raw v u.
     gas_marked_exec F (ctx,func) (bind (eval_expr cx idx) (read_result cx))
       (mid with gas_obs := [],t) imarks (INL v) raw (OK u) /\
     expr_post ctx func ce cx idx (mid with gas_obs := []) sm si t
       (raw with gas_obs := []) v iop u /\
     u.vs_current_bb = si.cs_current_bb /\
     u.vs_inst_idx = LENGTH si.cs_current_insts ==>
     gas_summary_at F (ctx,func) []
       (select_result cx (expr_type obj) captured (ValueSubscript v))
       (raw with gas_obs := [],u) Q (\res ee out. expr_exit res out)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_expr cx (Subscript ann obj idx)) (es,s0)
    Q (\res ee out. expr_exit res out)
Proof
  strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sm`,`si`,`iop`,`t`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule eval_expr_subscript_copied_bind >> disch_then (qspec_then `ann` SUBST1_TAC) >>
  irule (BETA_RULE (Q.ISPEC `\r v. select_result cx (expr_type obj) r (ValueSubscript v)`
    (Q.GEN `k` framed_array_index_outcome_compose))) >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  qexists `\v ee u.
    expr_post ctx func ce cx idx (mid with gas_obs := []) sm si t ee v iop u /\
    u.vs_current_bb = si.cs_current_bb /\
    u.vs_inst_idx = LENGTH si.cs_current_insts` >> simp[] >>
  `(!res out. (?exc. res = (INR exc : value + exception) /\
        expr_exit (INR exc : eval_result + exception) out) = expr_exit res out)` by
    (gen_tac >> Cases_on `res` >> simp[] >> rename1 `INR exc` >>
     qspec_then `Value` (mp_tac o REWRITE_RULE [FUN_EQ_THM]) expr_exit_success_map >>
     disch_then (qspec_then `INR exc : value + exception` mp_tac) >> simp[]) >>
  simp[] >> first_assum ACCEPT_TAC
QED
