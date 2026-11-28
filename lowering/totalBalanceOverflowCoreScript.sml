(* Call and deployment corollaries for the source recipient-overflow error. *)
Theory totalBalanceOverflowCore
Ancestors
  totalBalanceCallTrace vyperBalanceOverflow e2eDefs e2eDeployDefs
  vfmTotalBalance

Theorem total_balance_accounts_after_transfer:
  value_transfer_ok tx accounts ==>
  total_balance (accounts_after_transfer tx accounts) = total_balance accounts
Proof
  Cases_on `tx.value = 0` >- simp[accounts_after_transfer_def] >>
  Cases_on `tx.sender = tx.target` >- simp[accounts_after_transfer_def] >>
  rw[value_transfer_ok_def, accounts_after_transfer_def] >>
  `update_account tx.sender
      (lookup_account tx.sender accounts with balance updated_by flip $- tx.value)
      (update_account tx.target
        (lookup_account tx.target accounts with balance updated_by $+ tx.value)
        accounts) =
     vfmExecution$transfer_value tx.sender tx.target tx.value accounts` by
    simp[vfmExecutionTheory.transfer_value_def,
         vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
         combinTheory.APPLY_UPDATE_THM,
         combinTheory.UPDATE_COMMUTES] >>
  rw[] >>
  `total_balance (vfmExecution$transfer_value tx.sender tx.target tx.value accounts) =
     total_balance accounts` by
    (irule vfmTotalBalanceTheory.total_balance_transfer_value >>
     first_assum ACCEPT_TAC) >>
  rw[]
QED

Theorem call_state_rel_total_balance_bounded:
  call_state_rel tops runtime_bc am tx es ==>
  total_balance am.accounts <= 2 ** 256 - 1
Proof
  strip_tac >>
  `total_balance es.rollback.accounts <= 2 ** 256 - 1` by
    (irule balance_bounded_rollback >>
     fs[call_state_rel_def, evm_state_ok_def]) >>
  `total_balance (accounts_after_transfer tx am.accounts) =
     total_balance am.accounts` by
    (irule total_balance_accounts_after_transfer >>
     fs[call_state_rel_def, world_rel_def]) >>
  gvs[call_state_rel_def, world_rel_def]
QED

Theorem call_state_rel_no_recipient_overflow_core:
  call_state_rel tops runtime_bc am tx es /\
  call_external_trace (SOME (MAP SND (call_trace es))) gobs am tx =
    (res,am',rqs,obs) ==>
  total_balance am'.accounts <= 2 ** 256 - 1 /\ source_result_ok res
Proof
  strip_tac >>
  `total_balance am.accounts <= 2 ** 256 - 1` by
    metis_tac[call_state_rel_total_balance_bounded] >>
  `EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1)
      (MAP SND (call_trace es))` by
    (irule call_trace_outcomes_total_balance_bounded >>
     fs[call_state_rel_def, evm_state_ok_def]) >>
  irule source_call_external_no_recipient_overflow >>
  qexistsl [`am`, `gobs`, `obs`, `MAP SND (call_trace es)`, `rqs`, `tx`] >>
  simp[]
QED

Theorem deploy_state_rel_total_balance_bounded:
  deploy_state_rel tops deploy_bc am tx es ==>
  total_balance am.accounts <= 2 ** 256 - 1
Proof
  strip_tac >>
  `total_balance es.rollback.accounts <= 2 ** 256 - 1` by
    (irule balance_bounded_rollback >>
     fs[deploy_state_rel_def]) >>
  `total_balance (accounts_after_transfer tx am.accounts) =
     total_balance am.accounts` by
    (irule total_balance_accounts_after_transfer >>
     fs[deploy_state_rel_def]) >>
  gvs[deploy_state_rel_def]
QED

Theorem deploy_state_rel_no_recipient_overflow_core:
  deploy_state_rel tops deploy_bc am tx es /\
  load_contract_trace (SOME (MAP SND (call_trace es))) gobs am tx
    [(NONE,tops)] [] = (res,obs) ==>
  total_balance am.accounts <= 2 ** 256 - 1 /\ source_result_ok res
Proof
  strip_tac >>
  `total_balance am.accounts <= 2 ** 256 - 1` by
    metis_tac[deploy_state_rel_total_balance_bounded] >>
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

Theorem call_state_rel_no_recipient_overflow_public:
  call_state_rel tops runtime_bc am tx es /\
  call_external (SOME (MAP SND (call_trace es))) gobs am tx =
    (res,am',rqs) ==>
  source_result_ok res
Proof
  strip_tac >>
  `total_balance am.accounts <= 2 ** 256 - 1` by
    metis_tac[call_state_rel_total_balance_bounded] >>
  `EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1)
      (MAP SND (call_trace es))` by
    (irule call_trace_outcomes_total_balance_bounded >>
     fs[call_state_rel_def, evm_state_ok_def]) >>
  `total_balance am'.accounts <= 2 ** 256 - 1 /\ source_result_ok res` by
    (irule source_call_external_no_recipient_overflow_public >>
     qexistsl [`am`, `gobs`, `MAP SND (call_trace es)`, `rqs`, `tx`] >>
     metis_tac[]) >>
  gvs[]
QED
