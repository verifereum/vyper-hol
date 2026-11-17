(* Neutral account, storage and environment effects for ordinary opcodes. *)
Theory stackBoundEffectState
Ancestors
  stackBoundEffectCore vfmExecution vfmState vfmContext list pair

Theorem sb_eff_get_current_context_neutral[simp]:
  sb_eff_neutral get_current_context
Proof
  rw[sb_eff_neutral_def, get_current_context_def, return_def] >>
  gvs[sb_eff_frame_refl]
QED

Theorem sb_eff_get_accounts_neutral[simp]:
  sb_eff_neutral get_accounts
Proof
  simp[sb_eff_neutral_def, get_accounts_def, return_def, sb_eff_frame_refl]
QED

Theorem sb_eff_get_tStorage_neutral[simp]:
  sb_eff_neutral get_tStorage
Proof
  simp[sb_eff_neutral_def, get_tStorage_def, return_def, sb_eff_frame_refl]
QED

Theorem sb_eff_get_original_neutral[simp]:
  sb_eff_neutral get_original
Proof
  rw[sb_eff_neutral_def, get_original_def, return_def] >>
  gvs[sb_eff_frame_refl]
QED

Theorem sb_eff_get_tx_params_neutral[simp]:
  sb_eff_neutral get_tx_params
Proof
  simp[sb_eff_neutral_def, get_tx_params_def, return_def, sb_eff_frame_refl]
QED

Theorem sb_eff_get_callee_neutral[simp]:
  sb_eff_neutral get_callee
Proof
  simp[get_callee_def, sb_eff_neutral_bind]
QED

Theorem sb_eff_get_gas_left_neutral[simp]:
  sb_eff_neutral get_gas_left
Proof
  simp[get_gas_left_def, sb_eff_neutral_bind]
QED

Theorem sb_eff_get_static_neutral[simp]:
  sb_eff_neutral get_static
Proof
  simp[get_static_def, sb_eff_neutral_bind]
QED

Theorem sb_eff_get_current_code_neutral[simp]:
  sb_eff_neutral get_current_code
Proof
  simp[get_current_code_def, sb_eff_neutral_bind]
QED

Theorem sb_eff_get_code_neutral[simp]:
  sb_eff_neutral (get_code address)
Proof
  simp[get_code_def, sb_eff_neutral_bind]
QED

Theorem sb_eff_get_call_data_neutral[simp]:
  sb_eff_neutral get_call_data
Proof
  simp[get_call_data_def, sb_eff_neutral_bind]
QED

Theorem sb_eff_get_return_data_neutral[simp]:
  sb_eff_neutral get_return_data
Proof
  simp[get_return_data_def, sb_eff_neutral_bind]
QED

Theorem sb_eff_get_return_data_check_neutral[simp]:
  sb_eff_neutral (get_return_data_check offset sz)
Proof
  simp[get_return_data_check_def, sb_eff_neutral_bind,
       sb_eff_neutral_ignore_bind]
QED

Theorem sb_eff_assert_not_static_neutral[simp]:
  sb_eff_neutral assert_not_static
Proof
  simp[assert_not_static_def, sb_eff_neutral_bind]
QED

Theorem sb_eff_update_accounts_neutral[simp]:
  sb_eff_neutral (update_accounts f)
Proof
  simp[sb_eff_neutral_def, update_accounts_def, return_def, sb_eff_frame_def]
QED

Theorem sb_eff_set_tStorage_neutral[simp]:
  sb_eff_neutral (set_tStorage ts)
Proof
  simp[sb_eff_neutral_def, set_tStorage_def, return_def, sb_eff_frame_def]
QED

Theorem sb_eff_set_domain_neutral[simp]:
  sb_eff_neutral (set_domain d)
Proof
  simp[sb_eff_neutral_def, set_domain_def, return_def, sb_eff_frame_def]
QED

Theorem sb_eff_domain_check_neutral:
  sb_eff_neutral cont ==>
  sb_eff_neutral (domain_check err check addfn cont)
Proof
  strip_tac >> simp[sb_eff_neutral_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `s.msdomain`
  >- (gvs[domain_check_def, AllCaseEqs(), fail_def] >>
      metis_tac[sb_eff_neutral_def, sb_eff_frame_refl]) >>
  `sb_eff_neutral (ignore_bind (set_domain (Collect (addfn d))) cont)` by
    simp[sb_eff_neutral_ignore_bind] >>
  gvs[domain_check_def] >> metis_tac[sb_eff_neutral_def]
QED

Theorem sb_eff_access_address_neutral[simp]:
  sb_eff_neutral (access_address address)
Proof
  rewrite_tac[access_address_def] >> irule sb_eff_domain_check_neutral >>
  simp[sb_eff_neutral_def, return_def, sb_eff_frame_def]
QED

Theorem sb_eff_access_slot_neutral[simp]:
  sb_eff_neutral (access_slot slot)
Proof
  rewrite_tac[access_slot_def] >> irule sb_eff_domain_check_neutral >>
  simp[sb_eff_neutral_def, return_def, sb_eff_frame_def]
QED

Theorem sb_eff_write_storage_neutral[simp]:
  sb_eff_neutral (write_storage address key value)
Proof
  simp[write_storage_def]
QED

Theorem sb_eff_write_transient_storage_neutral[simp]:
  sb_eff_neutral (write_transient_storage address key value)
Proof
  simp[write_transient_storage_def, sb_eff_neutral_bind]
QED

Theorem sb_eff_push_logs_neutral[simp]:
  sb_eff_neutral (push_logs logs)
Proof
  rw[sb_eff_neutral_def, push_logs_def, bind_def,
     get_current_context_def, set_current_context_def, return_def] >>
  gvs[AllCaseEqs(), sb_eff_frame_def] >>
  Cases_on `s.contexts` >> gvs[]
QED

Theorem sb_eff_update_gas_refund_neutral[simp]:
  sb_eff_neutral (update_gas_refund deltas)
Proof
  PairCases_on `deltas` >>
  rw[sb_eff_neutral_def, update_gas_refund_def, bind_def,
     get_current_context_def, set_current_context_def, return_def] >>
  gvs[AllCaseEqs(), sb_eff_frame_def] >>
  Cases_on `s.contexts` >> gvs[]
QED

Theorem sb_eff_sstore_gas_neutral[simp]:
  sb_eff_neutral (step_sstore_gas_consumption address key value)
Proof
  rewrite_tac[step_sstore_gas_consumption_def] >>
  irule sb_eff_neutral_bind >> simp[] >> gen_tac >>
  irule sb_eff_neutral_ignore_bind >> simp[] >>
  irule sb_eff_neutral_bind >> simp[] >> gen_tac >>
  irule sb_eff_neutral_bind >> simp[] >> gen_tac >>
  irule sb_eff_neutral_bind >> simp[] >> gen_tac >>
  simp[sb_eff_neutral_ignore_bind]
QED
