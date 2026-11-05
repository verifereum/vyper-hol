(* Counted sequencing for the captured captured, index, and readonly suffix. *)
Theory exprSimSubscriptArrayCompose
Ancestors
  exprSimSubscriptArraySuffix gasOutcome gasSummary gasSummaryCompose gasExemptCert
  exprSimDefs exprSimSubscriptArraySource vyperState list

Theorem framed_array_summary_after_prefix[local]:
  gas_marked_exec memory (ctx,func) a (es,s0) left (INL v) mid (OK t) /\
  gas_summary_at memory (ctx,func) right (k v)
    (mid with gas_obs := [],t) Q R ==>
  gas_summary_at memory (ctx,func) (left ++ right) (bind a k) (es,s0) Q R
Proof
  simp[gas_summary_at_def] >> rpt strip_tac >>
  qexistsl_tac [`res`,`es_end`,`r`] >>
  simp[] >> metis_tac[gas_marked_exec_bind_normal]
QED

Theorem framed_array_index_outcome_compose:
  gas_marked_exec F (ctx,func) (a : evaluation_state -> eval_result evaluation_result)
    (es,s0) left (INL captured) mid (OK t) /\
  gas_outcome F tops (ctx,func) (b : evaluation_state -> value evaluation_result)
    (mid with gas_obs := [],t)
    (\res ee u. ?v. res = INL v /\ V v ee u)
    (\res ee out. ?exc. res = INR exc /\ R (INR exc) ee out) /\
  (!imarks raw v u.
     gas_marked_exec F (ctx,func) b (mid with gas_obs := [],t)
       imarks (INL v) raw (OK u) /\ V v (raw with gas_obs := []) u ==>
     gas_summary_at F (ctx,func) [] (k captured v) (raw with gas_obs := [],u) Q R) ==>
  gas_outcome F tops (ctx,func) (bind a (\r. bind b (k r))) (es,s0) Q R
Proof
  strip_tac >> fs[gas_outcome_def] >>
  qexists_tac `left ++ marks`
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o PURE_ONCE_REWRITE_RULE [gas_summary_at_def])
      >- suspend "normal"
      >> suspend "exit")
  >> suspend "exempt"
QED

Resume framed_array_index_outcome_compose[normal]:
  gvs[] >> disj1_tac >>
  irule framed_array_summary_after_prefix >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  pure_once_rewrite_tac[GSYM APPEND_NIL] >>
  irule framed_array_summary_after_prefix >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
Resume framed_array_index_outcome_compose[exit]:
  gvs[] >> disj1_tac >>
  irule framed_array_summary_after_prefix >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`,`es_end`,`r`] >> simp[] >>
  irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC
QED
Resume framed_array_index_outcome_compose[exempt]:
  disj2_tac >> qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_bind_result >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  pure_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >>
  first_assum ACCEPT_TAC
QED
Finalise framed_array_index_outcome_compose

(* The suffix callback retains the static Code-or-Fixed provenance and
   captured-base post; neither is inferred from the runtime operand. *)
Theorem framed_array_after_base:
  gas_marked_exec F (ctx,func) (eval_expr cx obj)
    (es,s0) left (INL captured) mid (OK t) /\
  expr_sim ctx func cenv cx ty idx (mid with gas_obs := []) /\
  lower_value compile_expr cenv ty idx sm = (iop,si) /\
  fn_has_code sm si func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\
  gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok
    (mid with gas_obs := []) /\
  stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!imarks raw v u.
     gas_marked_exec F (ctx,func) (bind (eval_expr cx idx) (read_result cx))
       (mid with gas_obs := [],t) imarks (INL v) raw (OK u) /\
     expr_post ctx func cenv cx idx (mid with gas_obs := []) sm si t
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
  pure_once_rewrite_tac[eval_expr_subscript_bind] >>
  irule (BETA_RULE (Q.ISPEC `\r v. select_result cx (expr_type obj) r (ValueSubscript v)`
    (Q.GEN `k` framed_array_index_outcome_compose))) >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  qexists_tac `\v ee u.
    expr_post ctx func cenv cx idx (mid with gas_obs := []) sm si t ee v iop u /\
    u.vs_current_bb = si.cs_current_bb /\
    u.vs_inst_idx = LENGTH si.cs_current_insts` >> simp[] >>
  `(!res out. (?exc. res = (INR exc : value + exception) /\
        expr_exit (INR exc : eval_result + exception) out) = expr_exit res out)` by
    (gen_tac >> Cases_on `res` >> simp[] >> rename1 `INR exc` >>
     qspec_then `Value` (mp_tac o REWRITE_RULE [FUN_EQ_THM]) expr_exit_success_map >>
     disch_then (qspec_then `INR exc : value + exception` mp_tac) >> simp[]) >>
  simp[] >> first_assum ACCEPT_TAC
QED
