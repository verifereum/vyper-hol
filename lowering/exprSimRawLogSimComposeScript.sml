(* Counted interfaces for the topic-success path of raw_log. *)
Theory exprSimRawLogSimCompose
Ancestors
  gasOutcome gasSummary gasSummaryCompose gasExemptCert stmtSimDeclCompose
  vyperInterpreter vyperState

Theorem raw_log_topics_outcome[local]:
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

(* Eliminate the topic outcome once, preserving topic errors and the
   continuation's exempt alternative. *)
Theorem raw_log_topics_bind:
  gas_outcome F tops (ctx,func) (eval_exprs cx topics) (es,s0)
    (\rr ee t. ?vs. rr = INL vs /\ P vs ee t)
    (\rr ee r. ?exc. rr = INR exc /\ R (INR exc) ee r) /\
  (!vs mid t marks.
     gas_marked_exec F (ctx,func) (eval_exprs cx topics) (es,s0)
       marks (INL vs) mid (OK t) /\ P vs (mid with gas_obs := []) t ==>
     gas_outcome F tops (ctx,func) (k vs)
       (mid with gas_obs := [],t) Q R) ==>
  gas_outcome F tops (ctx,func) (bind (eval_exprs cx topics) k)
    (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (fs[gas_summary_at_def]
      >- (irule raw_log_topics_outcome >>
          gvs[] >> metis_tac[]) >>
      simp[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >> simp[] >>
      metis_tac[gas_marked_exec_bind_exception]) >>
  simp[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_values >> simp[GSYM ignore_bind_def]
QED
