(* Counted interfaces for the topic-success path of raw_log. *)
Theory exprSimRawLogSimCompose
Ancestors
  gasOutcome gasSummary gasSummaryCompose gasExemptCert stmtSimDeclCompose
  vyperInterpreter vyperState

Theorem raw_log_topics_outcome:
  gas_marked_exec F (ctx,func) (eval_exprs cx topics) (es,s0)
    left (INL vs) mid (OK t) /\
  gas_outcome F tops (ctx,func) (k vs)
    (mid with gas_obs := [],t) Q R ==>
  gas_outcome F tops (ctx,func) (bind (eval_exprs cx topics) k)
    (es,s0) Q R
Proof
  rewrite_tac[gas_outcome_def] >> strip_tac >>
  qexists_tac `left ++ marks`
  >- (disj1_tac >> fs[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      metis_tac[gas_marked_exec_bind_normal]) >>
  disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_bind_values >>
  goal_assum (drule_at Any) >> simp[GSYM ignore_bind_def]
QED

(* Empty-mark administration before topics also preserves an exempt
   continuation. Reuse the general zero-prefix theorem rather than restate it. *)
Theorem raw_log_prefix_topics_outcome[local]:
  gas_marked_path F ctx func s0 0 (OK s1) /\
  gas_marked_exec F (ctx,func) (eval_exprs cx topics) (es,s1)
    left (INL vs) mid (OK t) /\
  gas_outcome F tops (ctx,func) (k vs)
    (mid with gas_obs := [],t) Q R ==>
  gas_outcome F tops (ctx,func) (bind (eval_exprs cx topics) k)
    (es,s0) Q R
Proof
  strip_tac >> drule_all raw_log_topics_outcome >>
  metis_tac[gas_outcome_zero_prefix]
QED
