(* Creation cannot retarget an existing executing account. A zero original
   account remains zero in originalAccounts even when creation targets it. *)
Theory frameCreationGuard
Ancestors
  vfmExecution vfmExecutionProp vfmAccountFrame vfmRunCall vfmRunWithinFrame
  vfmState vfmContext vfmTypes list arithmetic pair While evmCreationGuard

Definition creation_guard_inv_def:
  creation_guard_inv d self created (q:unit + exception option) s <=>
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

Theorem creation_guard_inv_step:
  0 < d /\ d <= LENGTH s.contexts /\
  creation_guard_inv d self created (INL ()) s /\ step s = (r,t) ==>
  creation_guard_inv d self created r t
Proof
  strip_tac >>
  `wf_state s /\ s.contexts <> []` by gvs[creation_guard_inv_def, wf_state_def] >>
  `wf_state t` by metis_tac[step_preserves_wf_state, SND] >>
  Cases_on `created`
  >- (gvs[creation_guard_inv_def] >>
      metis_tac[step_creation_original_empty]) >>
  drule creation_guard_inv_pre >> simp[] >> strip_tac >>
  `account_empty (lookup_account self t.originalAccounts) =
   account_empty (lookup_account self s.originalAccounts)`
    by (irule step_creation_original_empty >>
        gvs[creation_guard_inv_def] >> metis_tac[]) >>
  gvs[] >>
  `account_already_created (lookup_account self t.rollback.accounts)`
    by (irule step_creation_live_guard >> metis_tac[]) >>
  gvs[creation_guard_inv_def] >> strip_tac >>
  conj_tac
  >- (irule step_creation_active_rollbacks >> metis_tac[]) >>
  Cases_on `r` >> gvs[] >>
  drule step_creation_code_prefix >> simp[] >>
  disch_then (qspecl_then [`t`, `s`, `self`] mp_tac) >> fs[]
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
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `creation_guard_inv (LENGTH es.contexts) self created (INL ()) es`
    by (irule creation_guard_inv_initial >> metis_tac[]) >>
  `creation_guard_inv (LENGTH es.contexts) self created r post`
    suffices_by metis_tac[creation_guard_inv_post] >>
  qpat_x_assum `run_call es = _` mp_tac >>
  rewrite_tac[run_call_def] >> disch_tac >>
  `(\p. creation_guard_inv (LENGTH es.contexts) self created (FST p) (SND p))
    (r,post)` suffices_by simp[] >>
  irule (MP_CANON WhileTheory.OWHILE_INV_IND) >>
  goal_assum (first_assum o mp_then Any mp_tac) >> simp[] >>
  conj_tac >- gvs[] >>
  qx_gen_tac `p` >> PairCases_on `p` >> simp[] >> strip_tac >>
  Cases_on `p0` >> gvs[] >>
  Cases_on `step p1` >> simp[] >>
  `0 < LENGTH es.contexts` by (Cases_on `es.contexts` >> gvs[]) >>
  irule creation_guard_inv_step >> metis_tac[GREATER_EQ]
QED

(* A parent frame's guards survive entry into and execution of one child. *)
Theorem step_run_call_creation_guard:
  wf_state s /\
  (created = account_empty (lookup_account self s.originalAccounts)) /\
  (created \/ account_already_created (lookup_account self s.rollback.accounts)) /\
  step s = (INL (), v) /\
  LENGTH v.contexts = SUC (LENGTH s.contexts) /\
  run_call v = SOME (r, t) ==>
  (created = account_empty (lookup_account self t.originalAccounts)) /\
  (created \/ account_already_created (lookup_account self t.rollback.accounts))
Proof
  cheat
QED
