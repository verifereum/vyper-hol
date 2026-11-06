(* Creation cannot retarget an existing executing account. A zero original
   account remains zero in originalAccounts even when creation targets it. *)
Theory frameCreationGuard
Ancestors
  vfmExecution vfmExecutionProp vfmAccountFrame vfmRunCall vfmRunWithinFrame
  vfmState vfmContext vfmTypes list evmCreationGuard

Theorem run_call_creation_guard:
  wf_state es /\ es.contexts <> [] /\
  (created = account_empty (lookup_account self es.originalAccounts)) /\
  (created \/ account_already_created (lookup_account self es.rollback.accounts)) /\
  (2 <= LENGTH es.contexts ==>
    created \/ account_already_created
      (lookup_account self (SND (HD es.contexts)).accounts)) /\
  ((FST (HD es.contexts)).msgParams.outputTo = Code self ==> created) /\
  run_call es = SOME (r, post) ==>
  (created = account_empty (lookup_account self post.originalAccounts)) /\
  (created \/ account_already_created (lookup_account self post.rollback.accounts))
Proof
  cheat
QED
