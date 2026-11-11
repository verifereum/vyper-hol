(* selfdestruct's balance moves keep the source and Venom accounts in
   agreement: the transfer to the beneficiary, then EIP-6780's zeroing of
   an account created in the transaction. *)
Theory selfdestructHalt
Ancestors
  loweringStateRelDefs accountsRelProps vyperInterpreter vyperState
  vfmExecution vfmState combin

Theorem accounts_agree_target_balance:
  !cx a1 a2.
    accounts_agree cx a1 a2 ==>
    (a1 cx.txn.target).balance = (a2 cx.txn.target).balance
Proof
  rw[accounts_agree_def] >>
  qpat_x_assum `_ with storage := _ = _` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem accounts_agree_lookup_balance:
  !cx a1 a2 addr.
    accounts_agree cx a1 a2 ==>
    (lookup_account addr a1).balance = (lookup_account addr a2).balance
Proof
  rw[lookup_account_def] >> Cases_on `addr = cx.txn.target`
  >- metis_tac[accounts_agree_target_balance] >>
  gvs[accounts_agree_def]
QED

(* Changing the balance of any account keeps the agreement when both
   sides change it alike. *)
Theorem accounts_agree_balance_update:
  !cx a1 a2 addr f.
    accounts_agree cx a1 a2 ==>
    accounts_agree cx
      (update_account addr (lookup_account addr a1 with balance updated_by f) a1)
      (update_account addr (lookup_account addr a2 with balance updated_by f) a2)
Proof
  rw[accounts_agree_def, update_account_def, lookup_account_def,
     APPLY_UPDATE_THM] >>
  rw[] >> gvs[] >>
  qpat_x_assum `_ with storage := _ = _` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem accounts_agree_transfer_value:
  !cx a1 a2 fr to v.
    accounts_agree cx a1 a2 ==>
    accounts_agree cx (vfmExecution$transfer_value fr to v a1)
                      (vfmExecution$transfer_value fr to v a2)
Proof
  rw[vfmExecutionTheory.transfer_value_def] >> fs[] >>
  `!a. lookup_account to a =
       lookup_account to
         (update_account fr
            (lookup_account fr a with balance updated_by flip $- v) a)` by
    simp[lookup_account_def, update_account_def, APPLY_UPDATE_THM] >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  rpt (irule accounts_agree_balance_update) >> simp[]
QED

(* EIP-6780's zeroing of the running account. *)
Theorem accounts_agree_zero_balance:
  !cx a1 a2 addr.
    accounts_agree cx a1 a2 ==>
    accounts_agree cx
      (update_account addr (lookup_account addr a1 with balance := 0) a1)
      (update_account addr (lookup_account addr a2 with balance := 0) a2)
Proof
  rpt strip_tac >>
  drule accounts_agree_balance_update >>
  disch_then (qspecl_then [`addr`, `K 0`] mp_tac) >> simp[]
QED
