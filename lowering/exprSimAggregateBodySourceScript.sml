(* Counted source sequencing for body-aware aggregate loops. *)
Theory exprSimAggregateBodySource
Ancestors
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasStorage
  vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState exprSimMemorySource

Theorem aggregate_body_cons_outcome:
  gas_outcome F tops (ctx,func) cx st0 (eval_expr cx e) (es,s0)
    (\H res ee t. ?tv. res = INL tv /\ P H tv ee t)
    (\H res ee r. ?exc. res = INR exc /\ R H (INR exc) ee r) /\
  (!marks tv mid t.
    gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
      marks (INL tv) mid (OK t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      P H tv (mid with gas_obs := []) t) ==>
    gas_outcome F tops (ctx,func) cx st0
      (bind (read_result cx tv)
        (\v. bind (eval_exprs cx args) (\vs. return (v::vs))))
      (mid with gas_obs := [],t) Q R) ==>
  gas_outcome F tops (ctx,func) cx st0 (eval_exprs cx (e::args)) (es,s0) Q R
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >>
  `!tv. storage_trace_frame
          (bind (read_result cx tv)
             (\v. bind (eval_exprs cx args) (\vs. return (v::vs))))` by
    (rw[] >> irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_read_result] >> rw[] >>
     irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
      irule gas_bad_storage_at_bind_left >> simp[])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
       >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
           irule gas_bad_storage_at_bind_left >> simp[] >>
           irule gas_bad_storage_at_counted_prefix >>
           qexistsl_tac [`ctx`, `es_end`, `func`, `F`, `r`, `res`] >>
           simp[])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def]
      >- suspend "normal"
      >> suspend "exit") >>
  suspend "exempt"
QED

Resume aggregate_body_cons_outcome[normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `?tv. res = INL tv` by
    (first_assum (qspec_then `storage_trace_horizon es_end.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `!marks tv mid t. _`
    (qspecl_then [`marks`, `tv`, `es_end`, `t`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks ++ marks'` >>
      disj1_tac >> irule gas_bad_storage_at_bind_right >> simp[] >>
      metis_tac[])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      rewrite_tac[gas_outcome_def] >> qexists_tac `marks ++ marks'` >>
      disj2_tac >> disj1_tac >> simp[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end'`, `r`] >> simp[] >>
      (conj_tac
       >- (irule gas_marked_exec_bind_normal >> goal_assum (drule_at Any) >>
           gvs[])) >>
      fs[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks ++ marks'` >>
  disj2_tac >> disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_bind_result >> goal_assum (drule_at Any) >>
  simp[GSYM ignore_bind_def]
QED
Resume aggregate_body_cons_outcome[exit]:
  qpat_x_assum `(\res ee r. _) _ _ _` (assume_tac o BETA_RULE) >>
  first_assum (drule_then strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  gvs[] >> rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >> simp[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >> simp[] >>
  irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC
QED
Resume aggregate_body_cons_outcome[exempt]:
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >> first_assum ACCEPT_TAC
QED
Finalise aggregate_body_cons_outcome

Theorem aggregate_body_read_cons_outcome:
  read_result cx tv es = (INL v,es) /\
  gas_marked_path F ctx func t 0 (OK q) /\
  gas_outcome F tops (ctx,func) cx st0 (eval_exprs cx args)
    (es with gas_obs := [],q)
    (\H res ee r. ?vs. res = INL vs /\ P H vs ee r)
    (\H res ee r. ?exc. res = INR exc /\ R H (INR exc) ee r) /\
  (!H vs ee r. P H vs ee r ==> Q H (INL (v::vs)) ee r) ==>
  gas_outcome F tops (ctx,func) cx st0
    (bind (read_result cx tv)
      (\v. bind (eval_exprs cx args) (\vs. return (v::vs))))
    (es,t) Q R
Proof
  strip_tac >>
  `gas_marked_exec F (ctx,func) (read_result cx tv) (es,t)
      [] (INL v) es (OK q)` by
    (simp[gas_marked_exec_def] >> metis_tac[read_result_gas_obs]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
      irule (SRULE [] (Q.INST [`left` |-> `[]`]
        (SPEC_ALL gas_bad_storage_at_bind_right))) >>
      goal_assum (drule_at Any) >> simp[] >>
      irule gas_bad_storage_at_bind_left >>
      simp[storage_trace_frame_return])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
       >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
           irule (SRULE [] (Q.INST [`left` |-> `[]`]
             (SPEC_ALL gas_bad_storage_at_bind_right))) >>
           goal_assum (drule_at Any) >> simp[] >>
           irule gas_bad_storage_at_bind_left >>
           simp[storage_trace_frame_return] >>
           irule gas_bad_storage_at_counted_prefix >>
           qexistsl_tac [`ctx`, `es_end`, `func`, `F`, `r`, `res`] >>
           simp[])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def]
      >- suspend "normal"
      >> suspend "exit") >>
  suspend "exempt"
QED

Resume aggregate_body_read_cons_outcome[normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o BETA_RULE) >>
  first_assum (drule_then strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  gvs[] >>
  `gas_marked_exec F (ctx,func)
      (bind (eval_exprs cx args) (\vs. return (v::vs)))
      (es with gas_obs := [],q) marks (INL (v::vs)) es_end (OK t')` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     simp[bind_def, return_def]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (v::vs)`, `es_end`, `OK t'`] >> simp[] >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`] (SPEC_ALL gas_marked_exec_bind_normal))) >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume aggregate_body_read_cons_outcome[exit]:
  qpat_x_assum `(\res ee r. _) _ _ _` (assume_tac o BETA_RULE) >>
  first_assum (drule_then strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  gvs[] >>
  `gas_marked_exec F (ctx,func)
      (bind (eval_exprs cx args) (\vs. return (v::vs)))
      (es with gas_obs := [],q) marks (INR exc) es_end r` by
    (irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >> simp[] >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`] (SPEC_ALL gas_marked_exec_bind_normal))) >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume aggregate_body_read_cons_outcome[exempt]:
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
  simp[bind_assoc, bind_return] >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`] (SPEC_ALL gas_exempt_cert_bind_value))) >>
  goal_assum (drule_at Any) >> simp[GSYM ignore_bind_def]
QED
Finalise aggregate_body_read_cons_outcome

Theorem gas_outcome_source_invariant:
  gas_outcome memory tops (ctx,func) cx st0 source (es,s0) Q R /\
  (!si res sf. source si = (res,sf) ==> Inv res) ==>
  gas_outcome memory tops (ctx,func) cx st0 source (es,s0)
    (\H res ee t. Q H res ee t /\ Inv res) R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def]) >>
  simp[gas_outcome_def] >> qexists_tac `marks`
  >- simp[]
  >- (disj2_tac >> disj1_tac >> fs[gas_summary_at_def] >>
  `Inv res` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` assume_tac) >> metis_tac[]) >>
  metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

(* Map a source constructor while exposing its concrete successful run. *)
Theorem gas_outcome_map_source_run:
  gas_outcome memory tops (ctx,func) cx st0 source (es,s) Q R /\
  (!H res ee t. Q H res ee t /\
     (?gs. source (es with gas_obs := gs) = (res,ee)) ==>
     Q' H (SUM_MAP f I res) ee t) /\
  (!H res ee r. R H res ee r ==> R' H (SUM_MAP f I res) ee r) ==>
  gas_outcome memory tops (ctx,func) cx st0 (bind source (return o f)) (es,s)
    Q' R'
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
      irule gas_bad_storage_at_bind_left >>
      simp[combinTheory.o_DEF, storage_trace_frame_return])
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
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`SUM_MAP f I res`, `es_end`, `OK t`] >> simp[] >>
  disj1_tac >> fs[] >> metis_tac[]
QED

Resume gas_outcome_map_source_run[exit]:
  `gas_marked_exec memory (ctx,func) (bind source (return o f))
     (es,s) marks (SUM_MAP f I res) es_end r` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     simp[bind_def, return_def] >> gen_tac >>
     Cases_on `res` >> simp[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`SUM_MAP f I res`, `es_end`, `r`] >> simp[] >>
  disj2_tac >> fs[] >> metis_tac[]
QED

Resume gas_outcome_map_source_run[exempt]:
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
  simp[bind_return] >>
  simp[GSYM ignore_bind_def]
QED
Finalise gas_outcome_map_source_run
