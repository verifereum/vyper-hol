(* Counted outcome audit for the code-compatible immutable fixture. *)
Theory immutableDeployEmptyAssignedOutcome
Ancestors
  immutableDeployEmptyAssignedSource gasOutcome gasExemptCert gasSummary
  vyperState

Theorem assigned_immutable_no_exempt_outcome:
  !memory tops ctx func s0 marks err ee leaf finish.
    ~gas_exempt_cert memory tops (ctx,func)
      (ignore_bind (eval_stmt assigned_immutable_cx assigned_immutable_stmt)
                   (return ()))
      (empty_immutable_es,s0) marks (err,ee) (leaf,finish)
Proof
  rpt strip_tac >> drule gas_exempt_cert_execution >>
  simp[ignore_bind_def, bind_def, assigned_immutable_eval_stmt, return_def]
QED

Theorem assigned_immutable_outcome_summary:
  !memory tops ctx func s0 Q R.
    gas_outcome memory tops (ctx,func)
      (eval_stmt assigned_immutable_cx assigned_immutable_stmt)
      (empty_immutable_es,s0) Q R <=>
    ?marks. gas_summary_at memory (ctx,func) marks
      (eval_stmt assigned_immutable_cx assigned_immutable_stmt)
      (empty_immutable_es,s0) Q R
Proof
  simp[gas_outcome_def, assigned_immutable_no_exempt_outcome]
QED

Theorem assigned_immutable_summary_source_result:
  !memory ctx func s0 marks res ee r.
    gas_marked_exec memory (ctx,func)
      (eval_stmt assigned_immutable_cx assigned_immutable_stmt)
      (empty_immutable_es,s0) marks res ee r ==>
    res = INL () /\ ee with gas_obs := [] = empty_immutable_es with gas_obs := []
Proof
  rpt gen_tac >> simp[gas_marked_exec_def, assigned_immutable_eval_stmt] >>
  strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >>
  strip_tac >> simp[] >>
  qpat_x_assum `_ = ee with gas_obs := []`
    (mp_tac o Q.AP_TERM `\st. st with gas_obs := []`) >> simp[]
QED
