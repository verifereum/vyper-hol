Theory concretizePtrRequestHistory
Ancestors concretizePtrTaintContent concretizePtrOpaqueRetpc concretizePtrSharedFields
  extCallOracle list relation

(* Historical snapshots have no constraint from the current byte masks. *)
Definition ptr_request_shell_def:
  ptr_request_shell r q <=>
    (r with <| cr_accounts := q.cr_accounts; cr_tStorage := q.cr_tStorage |>) = q
End

Definition ptr_request_history_def:
  ptr_request_history hs ht <=> LIST_REL ptr_request_shell hs ht
End

Definition ptr_history_content_def:
  ptr_history_content tn s t <=>
    ptr_taint_content tn (s with vs_requests := t.vs_requests) t /\
    ptr_request_history s.vs_requests t.vs_requests
End

Theorem ptr_request_shell_refl[simp]:
  ptr_request_shell r r
Proof simp[ptr_request_shell_def]
QED

Theorem ptr_request_history_refl[simp]:
  ptr_request_history hs hs
Proof Induct_on `hs` >> gvs[ptr_request_history_def]
QED

Theorem ptr_request_history_length:
  ptr_request_history hs ht ==> LENGTH hs = LENGTH ht
Proof simp[ptr_request_history_def] >> metis_tac[LIST_REL_LENGTH]
QED

Theorem ptr_history_content_refl[simp]:
  ptr_history_content tn s s
Proof simp[ptr_history_content_def]
QED

Theorem ptr_history_content_current:
  ptr_history_content tn s t ==>
  ptr_taint_content tn (s with vs_requests := t.vs_requests) t
Proof simp[ptr_history_content_def]
QED

Theorem ptr_request_shell_classification:
  ptr_request_shell r q ==> (computed_precompile r <=> computed_precompile q)
Proof
  simp[ptr_request_shell_def] >> strip_tac >>
  qpat_x_assum `_ = q` (SUBST1_TAC o SYM) >>
  simp[computed_precompile_def]
QED

Theorem ptr_request_record:
  ptr_request_shell r q /\ ptr_request_history hs ht ==>
  ptr_request_history (record_request r hs) (record_request q ht)
Proof
  strip_tac >> drule ptr_request_shell_classification >> strip_tac >>
  Cases_on `computed_precompile q` >>
  gvs[record_request_def, ptr_request_history_def, LIST_REL_APPEND_EQ]
QED

Theorem ptr_request_record_change:
  ptr_request_shell r q /\ ptr_request_history hs ht ==>
  (record_request r hs = hs <=> record_request q ht = ht)
Proof
  strip_tac >> drule ptr_request_shell_classification >> strip_tac >>
  Cases_on `computed_precompile q` >> gvs[record_request_def] >>
  metis_tac[LENGTH_APPEND, LENGTH, DECIDE ``!n:num. n + 1 <> n``]
QED

Theorem ptr_request_selector_observations:
  ptr_request_shell r q ==>
  SND (take_outcome r os) = SND (take_outcome q os) /\
  (FST (take_outcome r os)).co_success =
    (FST (take_outcome q os)).co_success /\
  (FST (take_outcome r os)).co_returnData =
    (FST (take_outcome q os)).co_returnData
Proof
  simp[ptr_request_shell_def] >> strip_tac >>
  qpat_x_assum `_ = q` (SUBST1_TAC o SYM) >>
  Cases_on `os` >> simp[take_outcome_def, failed_outcome_def,
                        computed_precompile_def] >>
  Cases_on `computed_precompile r` >>
  gvs[GSYM computed_precompile_def] >>
  Cases_on `precompile_result r.cr_target r.cr_data` >>
  gvs[failed_outcome_def] >>
  rename1 `SOME result` >> Cases_on `result` >>
  gvs[failed_outcome_def] >>
  Cases_on `h.co_success` >> simp[failed_outcome_def]
QED

(* Empty-oracle observations agree, but the full outcomes need not. *)
Theorem ptr_request_empty_oracle_snapshots:
  (FST (take_outcome r [])).co_accounts = r.cr_accounts /\
  (FST (take_outcome r [])).co_tStorage = r.cr_tStorage
Proof simp[take_outcome_def, failed_outcome_def]
QED

(* Control observations survive both historical and current storage masking. *)
Theorem ptr_history_content_labels:
  ptr_history_content tn s t ==> s.vs_labels = t.vs_labels
Proof
  simp[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
       ptr_core_shared_def, ptr_shared_fields_def]
QED

Theorem ptr_history_content_call_ctx:
  ptr_history_content tn s t ==> s.vs_call_ctx = t.vs_call_ctx
Proof
  strip_tac >> drule ptr_history_content_current >> strip_tac >>
  drule ptr_taint_content_control >> strip_tac >>
  drule ptr_taint_control_call_ctx >> simp[]
QED

Theorem ptr_history_content_returndata:
  ptr_history_content tn s t ==> s.vs_returndata = t.vs_returndata
Proof
  simp[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
       ptr_core_shared_def, ptr_shared_fields_def]
QED

Theorem ptr_history_content_tx_ctx:
  ptr_history_content tn s t ==> s.vs_tx_ctx = t.vs_tx_ctx
Proof
  simp[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
       ptr_core_shared_def, ptr_shared_fields_def]
QED

Theorem ptr_history_content_block_ctx:
  ptr_history_content tn s t ==> s.vs_block_ctx = t.vs_block_ctx
Proof
  simp[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
       ptr_core_shared_def, ptr_shared_fields_def]
QED

Theorem ptr_history_content_data_section:
  ptr_history_content tn s t ==> s.vs_data_section = t.vs_data_section
Proof
  simp[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
       ptr_core_shared_def, ptr_shared_fields_def]
QED

Theorem ptr_history_content_code:
  ptr_history_content tn s t ==> s.vs_code = t.vs_code
Proof
  simp[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
       ptr_core_shared_def, ptr_shared_fields_def]
QED

Theorem ptr_history_content_prev_hashes:
  ptr_history_content tn s t ==> s.vs_prev_hashes = t.vs_prev_hashes
Proof
  simp[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
       ptr_core_shared_def, ptr_shared_fields_def]
QED

Theorem ptr_history_content_request_lengths:
  ptr_history_content tn s t ==> LENGTH s.vs_requests = LENGTH t.vs_requests
Proof
  simp[ptr_history_content_def] >> metis_tac[ptr_request_history_length]
QED
