Theory bodyIntCallArgCounted
Ancestors
  gasOutcome gasSummary gasSummaryCompose gasExemptCert vyperState vyperInterpreter

(* The prefix is the very witness on which the continuation is invoked. *)
Theorem marked_result_then_outcome:
  gas_marked_exec memory (ctx,func)
    (a : evaluation_state -> eval_result evaluation_result)
    (es,s0) left (INL v) mid (OK t) /\
  gas_outcome memory tops (ctx,func)
    (k v : evaluation_state -> 'b evaluation_result)
    (mid with gas_obs := [],t) Q R ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      disch_tac >> qexists_tac `left ++ marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_summary_at_def] >>
      metis_tac[gas_marked_exec_bind_normal]) >>
  qexists_tac `left ++ marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_bind_result >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED

Theorem gas_outcome_bind_result_marked:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> eval_result evaluation_result) (es,s0) P
    (\res ee r. ?exc. res = INR exc /\ E exc ee r) /\
  (!left v mid t.
    gas_marked_exec memory (ctx,func) a (es,s0) left (INL v) mid (OK t) /\
    P (INL v) (mid with gas_obs := []) t ==>
    gas_outcome memory tops (ctx,func)
      (k v : evaluation_state -> 'b evaluation_result)
      (mid with gas_obs := [],t) Q
      (\res ee r. ?exc. res = INR exc /\ E exc ee r)) /\
  (!res ee t. P res ee t ==> ?v. res = INL v) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q
    (\res ee r. ?exc. res = INR exc /\ E exc ee r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  disch_then (strip_assume_tac o
    REWRITE_RULE[gas_outcome_def, gas_summary_at_def])
  >- (gvs[] >>
      `?v. res = INL v` by metis_tac[] >> gvs[] >>
      irule marked_result_then_outcome >>
      qexistsl_tac [`marks`, `es_end`, `t`, `v`] >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      first_x_assum irule >> metis_tac[]) 
  >- (gvs[] >> rewrite_tac[gas_outcome_def] >>
      qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      metis_tac[]) >>
  rewrite_tac[gas_outcome_def] >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >>
  simp[GSYM ignore_bind_def]
QED
