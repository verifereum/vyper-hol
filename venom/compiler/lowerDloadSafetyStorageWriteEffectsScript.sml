(* Masked keyed storage updates. *)
Theory lowerDloadSafetyStorageWriteEffects
Ancestors
  lowerDloadSafetyKernel ptrDiscipline venomState vfmState
  finite_map pred_set combin

Theorem ld_storage_agree_update:
  storage_agree_except X st st' /\ word_agree_except M x y ==>
  storage_agree_except (key_update X key M)
    (update_storage key x st) (update_storage key y st')
Proof
  simp[storage_agree_except_def, word_agree_except_def,
       key_taint_def, key_update_def, update_storage_def] >>
  rpt strip_tac >> Cases_on `k = key` >> gvs[APPLY_UPDATE_THM]
QED

Theorem ld_nonghost_sstore:
  ld_nonghost tn s t /\ word_agree_except M x y ==>
  ld_nonghost (tn with t_stor := key_update tn.t_stor key M)
    (sstore key x s) (sstore key y t)
Proof
  simp[ld_nonghost_def, sstore_def, lookup_account_def] >>
  strip_tac >>
  qpat_assum `!a. (_ with storage := _) = _ /\ _`
    (qspec_then `t.vs_call_ctx.cc_address` strip_assume_tac) >>
  gvs[account_state_component_equality] >> rpt conj_tac >> rpt gen_tac >>
  Cases_on `a = t.vs_call_ctx.cc_address` >>
  gvs[combinTheory.APPLY_UPDATE_THM] >>
  metis_tac[ld_storage_agree_update]
QED

Theorem ld_nonghost_tstore:
  ld_nonghost tn s t /\ word_agree_except M x y ==>
  ld_nonghost (tn with t_trans := key_update tn.t_trans key M)
    (tstore key x s) (tstore key y t)
Proof
  simp[ld_nonghost_def, tstore_def] >>
  strip_tac >> rpt conj_tac >> rpt gen_tac >>
  Cases_on `a = t.vs_call_ctx.cc_address` >>
  gvs[combinTheory.APPLY_UPDATE_THM] >>
  metis_tac[ld_storage_agree_update]
QED
