(* Concrete NONE-mode pair projection for legacy lowering/e2e clients.
   This is not an oracle-mode semantic bridge. TASK056 owns legacy removal. *)
Theory vyperEntryCompat
Ancestors vyperInterpreter

Definition call_external_simple_def:
  call_external_simple am tx =
    (FST (call_external NONE am tx), FST (SND (call_external NONE am tx)))
End

Theorem call_external_simple_projection:
  call_external NONE am tx = (res,am',rqs) ==>
  call_external_simple am tx = (res,am')
Proof
  simp[call_external_simple_def]
QED

Theorem call_external_simple_cases:
  call_external_simple am tx = (res,am') <=>
  ?rqs. call_external NONE am tx = (res,am',rqs)
Proof
  Cases_on `call_external NONE am tx` >>
  rename1 `call_external NONE am tx = (result, machine_requests)` >>
  Cases_on `machine_requests` >> simp[call_external_simple_def]
QED
