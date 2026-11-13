Theory concretizePtrTaintContent
Ancestors concretizePtrOpaqueRetpc concretizePtrSharedFields ptrDiscipline venomState finite_map
  combin pred_set words

(* Parallel local-content candidate; existing paired samples are unchanged. *)
Definition ptr_taint_control_def:
  ptr_taint_control s t <=>
    ptr_core_shared
      (s with <| vs_accounts := t.vs_accounts;
                 vs_transient := t.vs_transient;
                 vs_immutables := t.vs_immutables |>) t
End

Definition ptr_taint_content_def:
  ptr_taint_content tn s t <=>
    ptr_taint_control s t /\
    (!a. (s.vs_accounts a with storage := (t.vs_accounts a).storage) =
         t.vs_accounts a) /\
    (!a. a <> s.vs_call_ctx.cc_address ==>
         (s.vs_accounts a).storage = (t.vs_accounts a).storage /\
         s.vs_transient a = t.vs_transient a) /\
    storage_agree_except tn.t_stor (contract_storage s) (contract_storage t) /\
    storage_agree_except tn.t_trans (contract_transient s) (contract_transient t) /\
    FDOM s.vs_immutables = FDOM t.vs_immutables /\
    (!k u v. FLOOKUP s.vs_immutables k = SOME u /\
             FLOOKUP t.vs_immutables k = SOME v ==>
       word_agree_except {b | (k,b) IN tn.t_imm} u v)
End

Theorem ptr_taint_content_refl[simp]:
  ptr_taint_content tn s s
Proof
  simp[ptr_taint_content_def, ptr_taint_control_def,
       ptr_core_shared_def, ptr_shared_fields_def,
       storage_agree_except_def, word_agree_except_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem ptr_storage_masked_read:
  storage_agree_except X st su ==>
  word_agree_except (key_taint X k) (st k) (su k)
Proof simp[storage_agree_except_def]
QED

Theorem ptr_storage_masked_update:
  storage_agree_except X st su /\ word_agree_except m u v ==>
  storage_agree_except (key_update X k m) ((k =+ u) st) ((k =+ v) su)
Proof
  simp[storage_agree_except_def] >> strip_tac >> qx_gen_tac `j` >>
  Cases_on `j = k` >>
  gvs[combinTheory.APPLY_UPDATE_THM, word_agree_except_def,
      key_taint_def, key_update_def] >> metis_tac[]
QED

Theorem ptr_taint_content_control:
  ptr_taint_content tn s t ==> ptr_taint_control s t
Proof simp[ptr_taint_content_def]
QED

Theorem ptr_taint_control_call_ctx:
  ptr_taint_control s t ==> s.vs_call_ctx = t.vs_call_ctx
Proof simp[ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def]
QED

Theorem ptr_taint_content_account:
  ptr_taint_content tn s t ==>
  (s.vs_accounts a with storage := (t.vs_accounts a).storage) = t.vs_accounts a
Proof simp[ptr_taint_content_def]
QED

Theorem ptr_taint_content_update_var[simp]:
  ptr_taint_content tn (update_var x u s) (update_var y v t) <=>
  ptr_taint_content tn s t
Proof
  simp[ptr_taint_content_def, ptr_taint_control_def, ptr_core_shared_def,
       ptr_shared_fields_def, update_var_def, contract_storage_def,
       contract_transient_def]
QED

Theorem ptr_taint_content_sstore:
  ptr_taint_content tn s t /\ word_agree_except m u v ==>
  ptr_taint_content (tn with t_stor := key_update tn.t_stor k m)
    (sstore k u s) (sstore k v t)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    metis_tac[ptr_taint_content_control, ptr_taint_control_call_ctx] >>
  gvs[ptr_taint_content_def, ptr_taint_control_def, ptr_core_shared_def,
      ptr_shared_fields_def, sstore_def, contract_storage_def,
      contract_transient_def, vfmStateTheory.lookup_account_def,
      vfmStateTheory.update_storage_def, combinTheory.APPLY_UPDATE_THM] >>
  reverse conj_tac >- (irule ptr_storage_masked_update >> simp[]) >>
  gen_tac >> Cases_on `t.vs_call_ctx.cc_address = a` >> simp[] >>
  qpat_x_assum `!a. _ with storage := _ = _`
    (qspec_then `a` (SUBST1_TAC o SYM)) >> simp[]
QED
Theorem ptr_taint_content_tstore:
  ptr_taint_content tn s t /\ word_agree_except m u v ==>
  ptr_taint_content (tn with t_trans := key_update tn.t_trans k m)
    (tstore k u s) (tstore k v t)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    metis_tac[ptr_taint_content_control, ptr_taint_control_call_ctx] >>
  gvs[ptr_taint_content_def, ptr_taint_control_def, ptr_core_shared_def,
      ptr_shared_fields_def, tstore_def, contract_storage_def,
      contract_transient_def, vfmStateTheory.lookup_account_def,
      vfmStateTheory.update_storage_def, combinTheory.APPLY_UPDATE_THM] >>
  irule ptr_storage_masked_update >> simp[]
QED

Theorem ptr_taint_content_sload:
  ptr_taint_content tn s t ==>
  word_agree_except (key_taint tn.t_stor k) (sload k s) (sload k t)
Proof
  simp[ptr_taint_content_def, sload_def, vfmStateTheory.lookup_storage_def] >>
  metis_tac[ptr_storage_masked_read]
QED

Theorem ptr_taint_content_tload:
  ptr_taint_content tn s t ==>
  word_agree_except (key_taint tn.t_trans k) (tload k s) (tload k t)
Proof
  simp[ptr_taint_content_def, tload_def, vfmStateTheory.lookup_storage_def] >>
  metis_tac[ptr_storage_masked_read]
QED
