(* Current mutable observations, separate from saved caller-local state. *)
Theory o1LowerDloadShared
Ancestors
  ptrDiscipline venomState venomExecSemantics venomInstProofs1
  finite_map list pred_set

Definition ld_shared_agree_def:
  ld_shared_agree D A tn s t <=>
    (!a. (s.vs_accounts a with storage := (t.vs_accounts a).storage) = t.vs_accounts a) /\
    (!a key. word_agree_except {j | a = A /\ (key,j) IN tn.t_stor}
      ((s.vs_accounts a).storage key) ((t.vs_accounts a).storage key)) /\
    (!a key. word_agree_except {j | a = A /\ (key,j) IN tn.t_trans}
      (s.vs_transient a key) (t.vs_transient a key)) /\
    FDOM s.vs_immutables = FDOM t.vs_immutables /\
    (!key. key IN FDOM s.vs_immutables ==>
      word_agree_except {j | (key,j) IN tn.t_imm}
        (s.vs_immutables ' key) (t.vs_immutables ' key)) /\
    s.vs_logs = t.vs_logs /\ s.vs_outcomes = t.vs_outcomes /\
    s.vs_pending_deletions = t.vs_pending_deletions /\
    LIST_REL (request_agree_except D) s.vs_requests t.vs_requests
End

Theorem ld_shared_agree_refl:
  ld_shared_agree D A tn s s
Proof
  simp[ld_shared_agree_def, word_agree_except_def] >>
  irule EVERY2_refl >>
  simp[request_agree_except_def, accounts_agree_except_def,
       transient_agree_except_def, storage_agree_except_def, word_agree_except_def]
QED

Theorem ld_shared_agree_merge:
  ld_shared_agree D A tn callee callee' ==>
  ld_shared_agree D A tn (merge_callee_state caller callee)
    (merge_callee_state caller' callee')
Proof
  simp[ld_shared_agree_def, merge_callee_state_def]
QED

Theorem ld_shared_agree_bind_outputs:
  ld_shared_agree D A tn s t /\ bind_outputs outs vals s = SOME s1 /\
  bind_outputs outs vals' t = SOME t1 ==> ld_shared_agree D A tn s1 t1
Proof
  strip_tac >>
  `ld_shared_agree D A tn s1 t = ld_shared_agree D A tn s t` by
    (qspec_then `\u. ld_shared_agree D A tn u t` mp_tac bind_outputs_preserves >>
     (impl_tac >- simp[ld_shared_agree_def, update_var_def]) >>
     disch_then rev_drule >> simp[]) >>
  `ld_shared_agree D A tn s1 t1 = ld_shared_agree D A tn s1 t` by
    (qspec_then `\u. ld_shared_agree D A tn s1 u` mp_tac bind_outputs_preserves >>
     (impl_tac >- simp[ld_shared_agree_def, update_var_def]) >>
     disch_then drule >> simp[]) >>
  simp[]
QED

Theorem ld_shared_accounts_fields:
  ld_shared_agree D A tn s t ==>
  !a. (s.vs_accounts a with storage := (t.vs_accounts a).storage) = t.vs_accounts a
Proof
  simp[ld_shared_agree_def]
QED

Theorem ld_shared_storage_word:
  ld_shared_agree D A tn s t ==>
  word_agree_except {j | a = A /\ (key,j) IN tn.t_stor}
    ((s.vs_accounts a).storage key) ((t.vs_accounts a).storage key)
Proof
  simp[ld_shared_agree_def]
QED

Theorem ld_shared_transient_word:
  ld_shared_agree D A tn s t ==>
  word_agree_except {j | a = A /\ (key,j) IN tn.t_trans}
    (s.vs_transient a key) (t.vs_transient a key)
Proof
  simp[ld_shared_agree_def]
QED

Theorem ld_shared_immutables_domain:
  ld_shared_agree D A tn s t ==> FDOM s.vs_immutables = FDOM t.vs_immutables
Proof
  simp[ld_shared_agree_def]
QED

Theorem ld_shared_immutable_word:
  ld_shared_agree D A tn s t /\ key IN FDOM s.vs_immutables ==>
  word_agree_except {j | (key,j) IN tn.t_imm}
    (s.vs_immutables ' key) (t.vs_immutables ' key)
Proof
  simp[ld_shared_agree_def]
QED

Theorem ld_shared_requests:
  ld_shared_agree D A tn s t ==>
  LIST_REL (request_agree_except D) s.vs_requests t.vs_requests
Proof
  simp[ld_shared_agree_def]
QED
