(* Call and deployment corollaries for the source recipient-overflow error. *)
Theory totalBalanceOverflowCore
Ancestors
  totalBalanceCallTrace vyperBalanceOverflow e2eDefs e2eDeployDefs
  vfmTotalBalance

Theorem call_state_rel_no_recipient_overflow_core:
  call_state_rel tops runtime_bc am tx es /\
  call_external_trace (SOME (MAP SND (call_trace es))) gobs am tx =
    (res,am',rqs,obs) ==>
  total_balance am'.accounts <= 2 ** 256 - 1 /\ source_result_ok res
Proof
  strip_tac >>
  `value_transfer_ok tx am.accounts` by
    fs[call_state_rel_def, world_rel_def] >>
  `total_balance es.rollback.accounts <= 2 ** 256 - 1` by
    (irule balance_bounded_rollback >>
     fs[call_state_rel_def, evm_state_ok_def]) >>
  `total_balance (accounts_after_transfer tx am.accounts) =
     total_balance am.accounts` by
    (Cases_on `tx.value = 0`
     >- simp[accounts_after_transfer_def]
     >- (Cases_on `tx.sender = tx.target`
         >- simp[accounts_after_transfer_def]
         >- (rw[value_transfer_ok_def, accounts_after_transfer_def] >>
             `update_account tx.sender
                 (lookup_account tx.sender am.accounts with balance updated_by
                    flip $- tx.value)
                 (update_account tx.target
                   (lookup_account tx.target am.accounts with balance updated_by
                     $+ tx.value) am.accounts) =
                vfmExecution$transfer_value tx.sender tx.target tx.value am.accounts` by
               simp[vfmExecutionTheory.transfer_value_def,
                    vfmStateTheory.lookup_account_def,
                    vfmStateTheory.update_account_def,
                    combinTheory.APPLY_UPDATE_THM,
                    combinTheory.UPDATE_COMMUTES] >>
             qpat_assum `_ = vfmExecution$transfer_value _ _ _ _`
               (fn h => rw[h]) >>
             irule vfmTotalBalanceTheory.total_balance_transfer_value >>
             fs[value_transfer_ok_def]))) >>
  `total_balance am.accounts <= 2 ** 256 - 1` by
    gvs[call_state_rel_def, world_rel_def] >>
  `EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1)
      (MAP SND (call_trace es))` by
    (irule call_trace_outcomes_total_balance_bounded >>
     fs[call_state_rel_def, evm_state_ok_def]) >>
  irule source_call_external_no_recipient_overflow >>
  qexistsl [`am`, `gobs`, `obs`, `MAP SND (call_trace es)`, `rqs`, `tx`] >>
  simp[]
QED

Theorem deploy_state_rel_no_recipient_overflow_core:
  deploy_state_rel tops deploy_bc am tx es /\
  load_contract_trace (SOME (MAP SND (call_trace es))) gobs am tx
    [(NONE,tops)] [] = (res,obs) ==>
  total_balance am.accounts <= 2 ** 256 - 1 /\ source_result_ok res
Proof
  strip_tac >>
  `value_transfer_ok tx am.accounts` by
    fs[deploy_state_rel_def] >>
  `total_balance es.rollback.accounts <= 2 ** 256 - 1` by
    (irule balance_bounded_rollback >>
     fs[deploy_state_rel_def]) >>
  `total_balance (accounts_after_transfer tx am.accounts) =
     total_balance am.accounts` by
    (Cases_on `tx.value = 0`
     >- simp[accounts_after_transfer_def]
     >- (Cases_on `tx.sender = tx.target`
         >- simp[accounts_after_transfer_def]
         >- (rw[value_transfer_ok_def, accounts_after_transfer_def] >>
             `update_account tx.sender
                 (lookup_account tx.sender am.accounts with balance updated_by
                    flip $- tx.value)
                 (update_account tx.target
                   (lookup_account tx.target am.accounts with balance updated_by
                     $+ tx.value) am.accounts) =
                vfmExecution$transfer_value tx.sender tx.target tx.value am.accounts` by
               simp[vfmExecutionTheory.transfer_value_def,
                    vfmStateTheory.lookup_account_def,
                    vfmStateTheory.update_account_def,
                    combinTheory.APPLY_UPDATE_THM,
                    combinTheory.UPDATE_COMMUTES] >>
             qpat_assum `_ = vfmExecution$transfer_value _ _ _ _`
               (fn h => rw[h]) >>
             irule vfmTotalBalanceTheory.total_balance_transfer_value >>
             fs[value_transfer_ok_def]))) >>
  `total_balance am.accounts <= 2 ** 256 - 1` by
    gvs[deploy_state_rel_def] >>
  `EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1)
      (MAP SND (call_trace es))` by
    (irule call_trace_outcomes_total_balance_bounded >>
     fs[deploy_state_rel_def, evm_state_ok_def]) >>
  `source_result_ok res /\
     (!am' rqs. res = INL (am',rqs) ==>
       total_balance am'.accounts <= 2 ** 256 - 1)` by
    (irule source_load_contract_no_recipient_overflow >>
     qexistsl [`am`, `[]`, `gobs`, `[(NONE,tops)]`, `obs`,
               `MAP SND (call_trace es)`, `tx`] >>
     simp[]) >>
  gvs[]
QED
