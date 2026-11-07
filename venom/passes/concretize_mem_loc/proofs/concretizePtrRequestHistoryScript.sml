Theory concretizePtrRequestHistory
Ancestors concretizePtrTaintContent extCallOracle list relation

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
