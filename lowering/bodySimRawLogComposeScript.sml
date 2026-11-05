(* Counted sequencing boundary, isolated from legacy branch proofs. *)
Theory bodySimRawLogCompose
Ancestors gasOutcome gasSummary gasSummaryCompose gasExemptCert vyperInterpreter vyperState

Theorem raw_log_outcome_bind_core[local]:
  gas_outcome memory tops (ctx,func) a (es,s0) P E /\
  (!marks rr mid t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks rr mid (OK t) /\
    P rr (mid with gas_obs := []) t ==>
    ?v. rr = INL v /\ gas_outcome memory tops (ctx,func) (k v)
      (mid with gas_obs := [],t) Q R) /\
  (!rr mid r. E rr mid r ==> ?exc. rr = INR exc /\ R (INR exc) mid r) /\
  (!marks err ee leaf finish.
    gas_exempt_cert memory tops (ctx,func) (ignore_bind a (return ()))
      (es,s0) marks (err,ee) (leaf,finish) ==>
    gas_exempt_cert memory tops (ctx,func) (ignore_bind (bind a k) (return ()))
      (es,s0) marks (err,ee) (leaf,finish)) /\
  (!left v mid t right err ee leaf finish.
    gas_marked_exec memory (ctx,func) a (es,s0) left (INL v) mid (OK t) /\
    gas_exempt_cert memory tops (ctx,func) (ignore_bind (k v) (return ()))
      (mid with gas_obs := [],t) right (err,ee) (leaf,finish) ==>
    gas_exempt_cert memory tops (ctx,func) (ignore_bind (bind a k) (return ()))
      (es,s0) (left ++ right) (err,ee) (leaf,finish)) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ a _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
  strip_tac
  >- suspend "completed"
  >- (qpat_x_assum `!rr mid r. _` drule >> strip_tac >> gvs[] >>
      drule gas_marked_exec_bind_exception >> metis_tac[])
  >> metis_tac[]
QED

Resume raw_log_outcome_bind_core[completed]:
  gvs[] >>
  qpat_x_assum `!marks rr mid t. _` (drule_all_then strip_assume_tac) >>
  gvs[] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (drule_all gas_marked_exec_bind_normal >> metis_tac[])
  >- (drule_all gas_marked_exec_bind_normal >> metis_tac[])
  >> metis_tac[]
QED
Finalise raw_log_outcome_bind_core

Theorem raw_log_unitize_bind[local]:
  ignore_bind (bind a k) (return ()) =
  bind a (\v. ignore_bind (k v) (return ()))
Proof
  simp[ignore_bind_def, bind_assoc]
QED

Theorem raw_log_outcome_bind_values:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> (value list) evaluation_result) (es,s0) P E /\
  (!marks rr mid t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks rr mid (OK t) /\
    P rr (mid with gas_obs := []) t ==>
    ?v. rr = INL v /\ gas_outcome memory tops (ctx,func) (k v)
      (mid with gas_obs := [],t) Q R) /\
  (!rr mid r. E rr mid r ==> ?exc. rr = INR exc /\ R (INR exc) mid r) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >> irule raw_log_outcome_bind_core >>
  conj_tac
  >- (simp[raw_log_unitize_bind] >> rpt strip_tac >>
      irule gas_exempt_cert_bind_values >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (simp[raw_log_unitize_bind] >> rpt strip_tac >>
      irule gas_exempt_cert_error_values >> simp[]) >>
  qexistsl_tac [`E`, `P`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem raw_log_outcome_bind_value:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> value evaluation_result) (es,s0) P E /\
  (!marks rr mid t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks rr mid (OK t) /\
    P rr (mid with gas_obs := []) t ==>
    ?v. rr = INL v /\ gas_outcome memory tops (ctx,func) (k v)
      (mid with gas_obs := [],t) Q R) /\
  (!rr mid r. E rr mid r ==> ?exc. rr = INR exc /\ R (INR exc) mid r) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >> irule raw_log_outcome_bind_core >>
  conj_tac
  >- (simp[raw_log_unitize_bind] >> rpt strip_tac >>
      irule gas_exempt_cert_bind_value >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (simp[raw_log_unitize_bind] >> rpt strip_tac >>
      irule gas_exempt_cert_error_value >> simp[]) >>
  qexistsl_tac [`E`, `P`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem raw_log_outcome_bind_unit:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> unit evaluation_result) (es,s0) P E /\
  (!marks rr mid t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks rr mid (OK t) /\
    P rr (mid with gas_obs := []) t ==>
    ?v. rr = INL v /\ gas_outcome memory tops (ctx,func) (k v)
      (mid with gas_obs := [],t) Q R) /\
  (!rr mid r. E rr mid r ==> ?exc. rr = INR exc /\ R (INR exc) mid r) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >> irule raw_log_outcome_bind_core >>
  conj_tac
  >- (simp[raw_log_unitize_bind] >> rpt strip_tac >>
      irule gas_exempt_cert_bind_unit >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (simp[raw_log_unitize_bind] >> rpt strip_tac >>
      irule gas_exempt_cert_error_unit >> simp[]) >>
  qexistsl_tac [`E`, `P`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!marks rr mid t. _` (drule_all_then strip_assume_tac) >>
  gvs[]
QED
