(* Source-side admissibility audit for a corrected related entry. *)
Theory augAssignNestedRelatedEntryProbe
Ancestors
  augAssignNestedApplicabilityProbe compileEnv

Theorem nested_initial_transaction_invalid:
  ~tx_env_ok nested_initial_cx.txn
Proof
  EVAL_TAC
QED

Theorem nested_initial_no_call_context:
  !cc tc bc. ~call_ctx_rel nested_initial_cx.txn cc tc bc
Proof
  simp[call_ctx_rel_def, nested_initial_transaction_invalid]
QED
