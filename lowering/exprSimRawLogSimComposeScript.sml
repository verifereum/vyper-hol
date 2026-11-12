(* Counted interfaces for the topic-success path of raw_log. *)
Theory exprSimRawLogSimCompose
Ancestors
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasStorage
  vyperStorageTrace vyperStorageFootprint stmtSimDeclCompose
  vyperInterpreter vyperState

Theorem raw_log_topics_outcome[local]:
  gas_marked_exec F (ctx,func) (eval_exprs cx topics) (es,s0)
    left (INL vs) mid (OK t) /\
  gas_outcome F tops (ctx,func) cx st0 (k vs)
    (mid with gas_obs := [],t) Q R ==>
  gas_outcome F tops (ctx,func) cx st0 (bind (eval_exprs cx topics) k)
    (es,s0) Q R
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `right` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >> qexists_tac `left ++ right` >> disj1_tac >>
      irule gas_bad_storage_at_bind_right >> metis_tac[]) >>
  disch_then (DISJ_CASES_THEN mp_tac)
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `out` (qx_choose_then `fin`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
      qexists_tac `left ++ right` >> disj2_tac >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`out`, `fin`, `r`] >>
      conj_tac >- metis_tac[gas_marked_exec_bind_normal] >>
      first_assum ACCEPT_TAC) >>
  strip_tac >>
  qexists_tac `left ++ right` >> disj2_tac >> disj2_tac >>
  rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
  irule_at Any gas_exempt_cert_bind_values >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED

(* Empty-mark administration before topics also preserves an exempt
   continuation. Reuse the general zero-prefix theorem rather than restate it. *)
Theorem raw_log_prefix_topics_outcome[local]:
  gas_marked_path F ctx func s0 0 (OK s1) /\
  gas_marked_exec F (ctx,func) (eval_exprs cx topics) (es,s1)
    left (INL vs) mid (OK t) /\
  gas_outcome F tops (ctx,func) cx st0 (k vs)
    (mid with gas_obs := [],t) Q R ==>
  gas_outcome F tops (ctx,func) cx st0 (bind (eval_exprs cx topics) k)
    (es,s0) Q R
Proof
  strip_tac >> drule_all raw_log_topics_outcome >>
  metis_tac[gas_outcome_zero_prefix]
QED

(* Eliminate the topic outcome once, preserving topic errors and the
   continuation's exempt alternative. The continuation receives the topic
   post at every valid horizon of its trace, and one such horizon. *)
Theorem raw_log_topics_bind:
  gas_outcome F tops (ctx,func) cx st0 (eval_exprs cx topics) (es,s0)
    (\H rr ee t. ?vs. rr = INL vs /\ P H vs ee t)
    (\H rr ee r. ?exc. rr = INR exc /\ R H (INR exc) ee r) /\
  (!vs mid t marks.
     gas_marked_exec F (ctx,func) (eval_exprs cx topics) (es,s0)
       marks (INL vs) mid (OK t) /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
        P H vs (mid with gas_obs := []) t) /\
     (?H. valid_horizon cx st0 H mid.storage_trace) ==>
     gas_outcome F tops (ctx,func) cx st0 (k vs)
       (mid with gas_obs := [],t) Q R) /\
  (!vs. storage_trace_frame (k vs)) ==>
  gas_outcome F tops (ctx,func) cx st0 (bind (eval_exprs cx topics) k)
    (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ (eval_exprs _ _) _ _ _`
    (mp_tac o BETA_RULE o REWRITE_RULE [gas_outcome_def]) >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >> rewrite_tac[gas_outcome_def] >>
      qexists_tac `marks` >> disj1_tac >>
      irule gas_bad_storage_at_bind_left >> simp[]) >>
  disch_then (DISJ_CASES_THEN mp_tac)
  >- (rewrite_tac[gas_summary_at_def] >> BETA_TAC >>
      disch_then (qx_choose_then `res` (qx_choose_then `mid`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
      reverse (Cases_on `storage_trace_domain cx st0 mid.storage_trace`)
      >- (disch_then kall_tac >> rewrite_tac[gas_outcome_def] >>
          qexists_tac `marks` >> disj1_tac >>
          irule gas_bad_storage_at_bind_left >> simp[] >>
          irule gas_bad_storage_at_counted_prefix >>
          metis_tac[]) >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
         mid.storage_trace` by fs[storage_trace_domain_def] >>
      disch_then (DISJ_CASES_THEN strip_assume_tac)
      >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
            (assume_tac o SIMP_RULE (srw_ss()) []) >>
          `?vs. res = INL vs` by metis_tac[] >> gvs[] >>
          irule raw_log_topics_outcome >>
          goal_assum (drule_at Any) >>
          first_x_assum irule >> simp[] >> rpt conj_tac >>
          TRY (metis_tac[] >> NO_TAC) >> rpt strip_tac >>
          `?vs'. INL vs = INL vs' /\ P H vs' (mid with gas_obs := []) t` by
            metis_tac[] >> gvs[]) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (assume_tac o SIMP_RULE (srw_ss()) []) >>
      `?ex. res = INR ex` by metis_tac[] >> gvs[] >>
      rewrite_tac[gas_outcome_def] >>
      qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR ex`, `mid`, `r`] >>
      conj_tac >- metis_tac[gas_marked_exec_bind_exception] >>
      BETA_TAC >> simp[] >> rpt strip_tac >>
      `?ex'. INR ex = INR ex' /\ R H (INR ex') (mid with gas_obs := []) r` by
        metis_tac[] >>
      gvs[]) >>
  strip_tac >>
  rewrite_tac[gas_outcome_def] >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
  irule_at Any gas_exempt_cert_error_values >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED
