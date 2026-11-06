(* Creation cannot retarget an existing executing account. A zero original
   account remains zero in originalAccounts even when creation targets it. *)
Theory frameCreationGuard
Ancestors
  vfmExecution vfmExecutionProp vfmAccountFrame vfmRunCall vfmRunWithinFrame
  vfmState vfmContext vfmTypes list arithmetic evmCreationGuard

Definition creation_guard_inv_def:
  creation_guard_inv d self created (q:unit + exception) s <=>
    wf_state s /\
    (created = account_empty (lookup_account self s.originalAccounts)) /\
    (created \/ account_already_created (lookup_account self s.rollback.accounts)) /\
    (ISL q /\ d <= LENGTH s.contexts ==>
      EVERY (\rb. created \/ account_already_created
        (lookup_account self rb.accounts)) (active_rollbacks d s) /\
      EVERY (\p. (FST p).msgParams.outputTo = Code self ==> created)
        (TAKE (LENGTH s.contexts - d + 1) s.contexts))
End

Theorem creation_guard_inv_post:
  creation_guard_inv d self created q s ==>
  (created = account_empty (lookup_account self s.originalAccounts)) /\
  (created \/ account_already_created (lookup_account self s.rollback.accounts))
Proof
  simp[creation_guard_inv_def]
QED

Theorem creation_guard_inv_initial:
  wf_state es /\ es.contexts <> [] /\
  (created = account_empty (lookup_account self es.originalAccounts)) /\
  (created \/ account_already_created (lookup_account self es.rollback.accounts)) /\
  (2 <= LENGTH es.contexts ==>
    created \/ account_already_created
      (lookup_account self (SND (HD es.contexts)).accounts)) /\
  ((FST (HD es.contexts)).msgParams.outputTo = Code self ==> created) ==>
  creation_guard_inv (LENGTH es.contexts) self created (INL ()) es
Proof
  Cases_on `es.contexts` >> simp[] >>
  rename1 `es.contexts = h::tail` >>
  Cases_on `tail` >>
  simp[creation_guard_inv_def, active_rollbacks_def, MAX_DEF] >>
  strip_tac >> gvs[] >> rw[] >> simp[ADD1] >>
  `LENGTH t = 0` by decide_tac >> simp[]
QED

Theorem creation_guard_inv_pre:
  creation_guard_inv d self created q s /\ ISL q /\
  d <= LENGTH s.contexts /\ 0 < d /\ s.contexts <> [] ==>
  (created \/ account_already_created (lookup_account self s.rollback.accounts)) /\
  (2 <= LENGTH s.contexts ==>
    created \/ account_already_created
      (lookup_account self (SND (HD s.contexts)).accounts)) /\
  ((FST (HD s.contexts)).msgParams.outputTo = Code self ==> created)
Proof
  Cases_on `s.contexts` >> simp[] >>
  simp[creation_guard_inv_def, active_rollbacks_def] >>
  rpt strip_tac >> gvs[] >>
  `0 < SUC (SUC (LENGTH t)) - MAX 2 d`
    by (rw[MAX_DEF] >> decide_tac) >>
  qpat_x_assum `EVERY _ (MAP SND _)` mp_tac >>
  Cases_on `SUC (SUC (LENGTH t)) - MAX 2 d` >> gvs[]
QED

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
