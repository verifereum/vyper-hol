Theory concretizeLayoutStateTransport
Ancestors concretizeLayoutSupplement maskedStateAlgebra venomState
  ptrDiscipline vfmState combin finite_map pred_set

Theorem concretize_supplement_sload:
  concretize_supplement D tn s t /\
  s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address ==>
  word_agree_except (key_taint tn.t_stor k) (sload k s) (sload k t)
Proof
  simp[concretize_supplement_def, accounts_agree_except_def,
       sload_def, contract_storage_def, lookup_account_def,
       lookup_storage_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `s.vs_call_ctx.cc_address` mp_tac) >>
  simp[] >> metis_tac[storage_agree_except_read]
QED

Theorem concretize_supplement_tload:
  concretize_supplement D tn s t /\
  s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address ==>
  word_agree_except (key_taint tn.t_trans k) (tload k s) (tload k t)
Proof
  simp[concretize_supplement_def, transient_agree_except_def,
       tload_def, contract_transient_def, lookup_storage_def] >>
  rpt strip_tac >> metis_tac[storage_agree_except_read]
QED

Theorem concretize_supplement_tstore:
  concretize_supplement D tn s t /\
  s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address /\
  word_agree_except m x y ==>
  concretize_supplement D (tn with t_trans := key_update tn.t_trans k m)
    (tstore k x s) (tstore k y t)
Proof
  simp[concretize_supplement_def, tstore_def, transient_agree_except_def,
       update_storage_def] >>
  rpt strip_tac >> Cases_on `a = s.vs_call_ctx.cc_address` >>
  gvs[APPLY_UPDATE_THM] >> metis_tac[storage_agree_except_update]
QED

Theorem concretize_supplement_sstore:
  concretize_supplement D tn s t /\
  s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address /\
  word_agree_except m x y ==>
  concretize_supplement D (tn with t_stor := key_update tn.t_stor k m)
    (sstore k x s) (sstore k y t)
Proof
  simp[concretize_supplement_def, sstore_def, accounts_agree_except_def,
       lookup_account_def, update_storage_def] >>
  rpt strip_tac >> Cases_on `a = s.vs_call_ctx.cc_address` >>
  gvs[APPLY_UPDATE_THM, account_state_component_equality] >>
  metis_tac[storage_agree_except_update]
QED

Theorem concretize_supplement_immutables:
  concretize_supplement D tn s t /\ word_agree_except m x y ==>
  concretize_supplement D (tn with t_imm := key_update tn.t_imm k m)
    (s with vs_immutables := s.vs_immutables |+ (k,x))
    (t with vs_immutables := t.vs_immutables |+ (k,y))
Proof
  simp[concretize_supplement_def] >>
  metis_tac[imms_agree_except_update]
QED

Theorem concretize_local_obs_tstore:
  concretize_local_obs s t /\
  s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address ==>
  concretize_local_obs (tstore k x s) (tstore k y t)
Proof
  simp[concretize_local_obs_def, dead_result_rel_def, tstore_def,
       transient_agree_except_def, storage_agree_except_def,
       key_taint_def, word_agree_except_def]
QED

Theorem concretize_local_obs_sstore:
  concretize_local_obs s t /\
  s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address ==>
  concretize_local_obs (sstore k x s) (sstore k y t)
Proof
  simp[concretize_local_obs_def, dead_result_rel_def, sstore_def,
       lookup_account_def, accounts_agree_except_def,
       storage_agree_except_def, key_taint_def, word_agree_except_def,
       account_state_component_equality] >>
  rpt strip_tac >> Cases_on `a = s.vs_call_ctx.cc_address` >>
  gvs[APPLY_UPDATE_THM] >> metis_tac[]
QED

Theorem concretize_local_obs_immutables:
  concretize_local_obs s t ==>
  concretize_local_obs
    (s with vs_immutables := s.vs_immutables |+ (k,x))
    (t with vs_immutables := t.vs_immutables |+ (k,y))
Proof
  simp[concretize_local_obs_def, dead_result_rel_def,
       imms_agree_except_def, word_agree_except_def]
QED
