(* Counted source sequencing for body-aware aggregate loops. *)
Theory exprSimAggregateBodySource
Ancestors
  gasOutcome gasSummary gasSummaryCompose gasExemptCert
  vyperInterpreter vyperState

Theorem aggregate_body_cons_outcome:
  gas_outcome F tops (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?tv. res = INL tv /\ P tv ee t)
    (\res ee r. ?exc. res = INR exc /\ R (INR exc) ee r) /\
  (!marks tv mid t.
    gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
      marks (INL tv) mid (OK t) /\ P tv (mid with gas_obs := []) t ==>
    gas_outcome F tops (ctx,func)
      (bind (read_result cx tv)
        (\v. bind (eval_exprs cx args) (\vs. return (v::vs))))
      (mid with gas_obs := [],t) Q R) ==>
  gas_outcome F tops (ctx,func) (eval_exprs cx (e::args)) (es,s0) Q R
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "normal"
      >> suspend "exit") >>
  suspend "exempt"
QED

Resume aggregate_body_cons_outcome[normal]:
  gvs[] >> first_x_assum drule >> simp[] >>
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      rewrite_tac[gas_outcome_def] >> qexists_tac `marks ++ marks'` >>
      disj1_tac >> simp[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end'`, `r`] >> simp[] >>
      irule gas_marked_exec_bind_normal >> goal_assum (drule_at Any) >>
      gvs[])
  >> (rewrite_tac[gas_outcome_def] >> qexists_tac `marks ++ marks'` >>
      disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
      pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_result >> goal_assum (drule_at Any) >>
      simp[GSYM ignore_bind_def])
QED
Resume aggregate_body_cons_outcome[exit]:
  gvs[] >> rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >>
  disj1_tac >> simp[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >> simp[] >>
  irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC
QED
Resume aggregate_body_cons_outcome[exempt]:
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >> first_assum ACCEPT_TAC
QED
Finalise aggregate_body_cons_outcome
