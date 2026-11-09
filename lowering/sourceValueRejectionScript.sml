(* Source value rejection after excluding balance/overflow failures. *)
Theory sourceValueRejection
Ancestors e2eDefs vyperInterpreter vyperState

Theorem send_call_value_reject_iff:
  value_transfer_ok cx.txn s.accounts ==>
  ((?e s'. send_call_value mut cx s = (INR e,s')) <=>
   cx.txn.value <> 0 /\ mut <> Payable)
Proof
  Cases_on `cx.txn.value = 0` >>
  Cases_on `mut = Payable` >>
  Cases_on `cx.txn.sender = cx.txn.target` >>
  simp[value_transfer_ok_def, send_call_value_def, transfer_value_def,
       return_def, bind_def, ignore_bind_def, check_def, assert_def,
       get_accounts_def, update_accounts_def]
QED

Theorem send_call_value_reject_condition:
  value_transfer_ok cx.txn s.accounts /\
  send_call_value mut cx s = (INR e,s') ==>
  cx.txn.value <> 0 /\ mut <> Payable
Proof
  metis_tac[send_call_value_reject_iff]
QED
