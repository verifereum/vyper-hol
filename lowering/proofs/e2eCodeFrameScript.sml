(*
 * The installed code of a contract survives a transaction's EVM run: only a
 * creation frame's return deposits code, at an address with no code yet.
 *)
Theory e2eCodeFrame
Ancestors
  vfmState vfmContext vfmExecution vfmExecutionProp vfmRunCall vfmAccountFrame

(* Intuition: code is written only by the deposit at the end of a frame whose
   outputTo is Code b, and CREATE/CREATE2 push such a frame only when b is not
   account_already_created, which nonempty code rules out. SELFDESTRUCT only
   moves balance and queues a deletion (processed after run_call). Reverts
   restore saved rollbacks taken during the run, which hold the same code.
   At depth 1 a failure is reraised without restoring a rollback, which
   touches no code either. *)
Theorem run_call_preserves_installed_code:
  wf_state es /\ LENGTH es.contexts = 1 /\
  (lookup_account a es.rollback.accounts).code <> [] /\
  (FST (HD es.contexts)).msgParams.outputTo <> Code a /\
  run_call es = SOME (r, es') ==>
  (lookup_account a es'.rollback.accounts).code =
  (lookup_account a es.rollback.accounts).code
Proof
  cheat
QED
