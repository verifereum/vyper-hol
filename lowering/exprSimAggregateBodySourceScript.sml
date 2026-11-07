(* Counted source sequencing for body-aware aggregate loops. *)
Theory exprSimAggregateBodySource
Ancestors
  gasOutcome gasSummary gasSummaryCompose gasExemptCert
  vyperInterpreter vyperState exprSimMemorySource

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

Theorem aggregate_body_read_cons_outcome:
  read_result cx tv es = (INL v,es) /\
  gas_marked_path F ctx func t 0 (OK q) /\
  gas_outcome F tops (ctx,func) (eval_exprs cx args)
    (es with gas_obs := [],q)
    (\res ee r. ?vs. res = INL vs /\ P vs ee r)
    (\res ee r. ?exc. res = INR exc /\ R (INR exc) ee r) /\ 
  (!vs ee r. P vs ee r ==> Q (INL (v::vs)) ee r) ==>
  gas_outcome F tops (ctx,func)
    (bind (read_result cx tv)
      (\v. bind (eval_exprs cx args) (\vs. return (v::vs))))
    (es,t) Q R
Proof
  strip_tac >>
  `gas_marked_exec F (ctx,func) (read_result cx tv) (es,t)
      [] (INL v) es (OK q)` by
    (simp[gas_marked_exec_def] >> metis_tac[read_result_gas_obs]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "normal"
      >> suspend "exit") >>
  suspend "exempt"
QED

Resume aggregate_body_read_cons_outcome[normal]:
  gvs[] >>
  `gas_marked_exec F (ctx,func)
      (bind (eval_exprs cx args) (\vs. return (v::vs)))
      (es with gas_obs := [],q) marks (INL (v::vs)) es_end (OK t')` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     simp[bind_def, return_def]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (v::vs)`, `es_end`, `OK t'`] >> simp[] >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`] (SPEC_ALL gas_marked_exec_bind_normal))) >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume aggregate_body_read_cons_outcome[exit]:
  gvs[] >>
  `gas_marked_exec F (ctx,func)
      (bind (eval_exprs cx args) (\vs. return (v::vs)))
      (es with gas_obs := [],q) marks (INR exc) es_end r` by
    (irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >> simp[] >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`] (SPEC_ALL gas_marked_exec_bind_normal))) >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume aggregate_body_read_cons_outcome[exempt]:
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
  simp[bind_assoc, bind_return] >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`] (SPEC_ALL gas_exempt_cert_bind_value))) >>
  goal_assum (drule_at Any) >> simp[GSYM ignore_bind_def]
QED
Finalise aggregate_body_read_cons_outcome

Theorem gas_outcome_source_invariant:
  gas_outcome memory tops (ctx,func) source (es,s0) Q R /\
  (!si res sf. source si = (res,sf) ==> Inv res) ==>
  gas_outcome memory tops (ctx,func) source (es,s0)
    (\res ee t. Q res ee t /\ Inv res) R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def]) >>
  simp[gas_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_summary_at_def] >>
  `Inv res` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` assume_tac) >> metis_tac[]) >>
  metis_tac[]) >>
  disj2_tac >> metis_tac[]
QED

(* Map a source constructor while exposing its concrete successful run. *)
Theorem gas_outcome_map_source_run:
  gas_outcome memory tops (ctx,func) source (es,s) Q R /\
  (!res ee t. Q res ee t /\
     (?gs. source (es with gas_obs := gs) = (res,ee)) ==>
     Q' (SUM_MAP f I res) ee t) /\
  (!res ee r. R res ee r ==> R' (SUM_MAP f I res) ee r) ==>
  gas_outcome memory tops (ctx,func) (bind source (return o f)) (es,s) Q' R'
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "normal"
      >> suspend "exit") >>
  suspend "exempt"
QED

Resume gas_outcome_map_source_run[normal]:
  `gas_marked_exec memory (ctx,func) (bind source (return o f))
     (es,s) marks (SUM_MAP f I res) es_end (OK t)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     simp[bind_def, return_def] >> gen_tac >>
     Cases_on `res` >> simp[]) >>
  `?gs. source (es with gas_obs := gs) = (res,es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ source _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> metis_tac[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`SUM_MAP f I res`, `es_end`, `OK t`] >> simp[] >>
  metis_tac[]
QED

Resume gas_outcome_map_source_run[exit]:
  `gas_marked_exec memory (ctx,func) (bind source (return o f))
     (es,s) marks (SUM_MAP f I res) es_end r` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     simp[bind_def, return_def] >> gen_tac >>
     Cases_on `res` >> simp[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`SUM_MAP f I res`, `es_end`, `r`] >> simp[]
QED

Resume gas_outcome_map_source_run[exempt]:
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
  simp[bind_return] >>
  simp[GSYM ignore_bind_def]
QED
Finalise gas_outcome_map_source_run
