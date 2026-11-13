Theory concretizePtrSharedFields
Ancestors venomExecSemantics venomState venomInst finite_map list words

(* No memory, variables, parameters, cursor, or allocation bookkeeping. *)
Definition ptr_shared_fields_def:
  ptr_shared_fields s t <=>
    s.vs_transient = t.vs_transient /\
    s.vs_accounts = t.vs_accounts /\
    s.vs_returndata = t.vs_returndata /\
    s.vs_logs = t.vs_logs /\
    s.vs_outcomes = t.vs_outcomes /\
    s.vs_requests = t.vs_requests /\
    s.vs_pending_deletions = t.vs_pending_deletions /\
    s.vs_gas_readings = t.vs_gas_readings /\
    s.vs_immutables = t.vs_immutables /\
    s.vs_call_ctx = t.vs_call_ctx /\
    s.vs_tx_ctx = t.vs_tx_ctx /\
    s.vs_block_ctx = t.vs_block_ctx /\
    s.vs_data_section = t.vs_data_section /\
    s.vs_labels = t.vs_labels /\
    s.vs_code = t.vs_code /\
    s.vs_prev_hashes = t.vs_prev_hashes /\
    s.vs_fmp = t.vs_fmp /\
    s.vs_call_entry_fmp = t.vs_call_entry_fmp /\
    s.vs_initial_fmp = t.vs_initial_fmp /\
    s.vs_return_pc_token = t.vs_return_pc_token /\
    s.vs_halted = t.vs_halted
End

Theorem ptr_shared_fields_refl[simp]:
  ptr_shared_fields s s
Proof simp[ptr_shared_fields_def]
QED

Theorem ptr_shared_fields_update_var[simp]:
  ptr_shared_fields (update_var x a s) (update_var y b t) <=> ptr_shared_fields s t
Proof simp[ptr_shared_fields_def, update_var_def]
QED

Theorem ptr_shared_fields_setup:
  ptr_shared_fields s t /\
  (NULL f.fn_blocks <=> NULL g.fn_blocks) /\
  (if NULL args then 0w else LAST args) =
    (if NULL argst then 0w else LAST argst) /\
  setup_callee g argst t = SOME t' ==>
  ?s'. setup_callee f args s = SOME s' /\ ptr_shared_fields s' t'
Proof
  simp[setup_callee_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  simp[ptr_shared_fields_def] >> gvs[ptr_shared_fields_def]
QED

Theorem ptr_shared_fields_merge:
  ptr_shared_fields s t /\ ptr_shared_fields u v ==>
  ptr_shared_fields (merge_callee_state s u) (merge_callee_state t v)
Proof simp[ptr_shared_fields_def, merge_callee_state_def]
QED

Theorem ptr_shared_fields_adopt_none:
  ptr_shared_fields s t /\ r.iret_adopt_fmp = NONE /\ rt.iret_adopt_fmp = NONE ==>
  ptr_shared_fields (adopt_return_fmp r s) (adopt_return_fmp rt t)
Proof simp[adopt_return_fmp_def]
QED
