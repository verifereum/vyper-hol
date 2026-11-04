(* Keyed storage observations and ordinary read effects. *)
Theory lowerDloadSafetyStorageReadEffects
Ancestors
  lowerDloadSafetyKernel lowerDloadSafetyReadSteps lowerDloadSafetyUpdates
  lowerDloadSafetyValues ptrDiscipline venomState venomExecSemantics
  vfmState finite_map list pred_set

Theorem ld_nonghost_sload:
  ld_nonghost tn s t ==>
  word_agree_except (key_taint tn.t_stor k) (sload k s) (sload k t)
Proof
  simp[ld_nonghost_def] >> strip_tac >>
  qpat_x_assum `!a. (_ with storage := _) = _ /\ _`
    (qspec_then `s.vs_call_ctx.cc_address` mp_tac) >>
  simp[storage_agree_except_def, sload_def, contract_storage_def,
       lookup_account_def, lookup_storage_def]
QED

Theorem ld_nonghost_tload:
  ld_nonghost tn s t ==>
  word_agree_except (key_taint tn.t_trans k) (tload k s) (tload k t)
Proof
  simp[ld_nonghost_def] >> strip_tac >>
  qpat_x_assum `!a. storage_agree_except _ _ _`
    (qspec_then `s.vs_call_ctx.cc_address` mp_tac) >>
  simp[storage_agree_except_def, tload_def, contract_transient_def,
       lookup_storage_def]
QED
