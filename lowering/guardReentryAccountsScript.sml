Theory guardReentryAccounts
Ancestors
  evmCreationGuard vfmAccountFrame vfmRunCall vfmExecution vfmExecutionProp vfmState
  list arithmetic

val guard_protected_rollbacks = ``\(base:execution_state) s.
  EVERY (\rb. !addr.
    account_already_created (lookup_account addr base.rollback.accounts) ==>
    account_already_created (lookup_account addr rb.accounts))
    (s.rollback :: MAP SND
      (TAKE (LENGTH s.contexts - LENGTH base.contexts) s.contexts))``;

val guard_protected_outputs = ``\(base:execution_state) s.
  EVERY (\mp. !addr. mp.outputTo = Code addr ==>
    ~account_already_created (lookup_account addr base.rollback.accounts))
    (MAP (\p. (FST p).msgParams)
      (TAKE (LENGTH s.contexts - LENGTH base.contexts) s.contexts))``;

Theorem guard_reaches_created_original_nonempty:
  wf_state es /\
  account_already_created (lookup_account a es.rollback.accounts) /\
  ~account_empty (lookup_account a es.originalAccounts) /\
  run_call_reaches es s /\ LENGTH es.contexts <= LENGTH s.contexts ==>
  account_already_created (lookup_account a s.rollback.accounts) /\
  ~account_empty (lookup_account a s.originalAccounts)
Proof
  strip_tac >>
  `0 < LENGTH es.contexts` by
    (Cases_on `es.contexts` >> gvs[wf_state_def]) >>
  `wf_state s /\
   (LENGTH es.contexts <= LENGTH s.contexts ==>
    ^guard_protected_rollbacks es s /\ ^guard_protected_outputs es s /\
    ~account_empty (lookup_account a s.originalAccounts))`
    suffices_by (simp[] >> metis_tac[]) >>
  BETA_TAC >>
  irule (BETA_RULE (Q.INST
    [`Q` |-> `\st. wf_state st /\
      (LENGTH es.contexts <= LENGTH st.contexts ==>
       ^guard_protected_rollbacks es st /\ ^guard_protected_outputs es st /\
       ~account_empty (lookup_account a st.originalAccounts))`,
     `es` |-> `es`, `s` |-> `s`] run_call_reaches_inv)) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `step current_st = (INL u, next_st)` >>
  `wf_state next_st` by
    (drule_all step_preserves_wf_state >> simp[]) >>
  simp[] >> strip_tac >> fs[] >>
  `^guard_protected_rollbacks es next_st` by
    (BETA_TAC >>
     mp_tac (Q.INST [`d` |-> `LENGTH es.contexts`, `B` |-> `es.rollback`,
       `s` |-> `current_st`, `t` |-> `next_st`, `x` |-> `u`]
       step_continuing_collision_protection) >> simp[]) >>
  `^guard_protected_outputs es next_st` by
    (BETA_TAC >>
     mp_tac (Q.INST [`d` |-> `LENGTH es.contexts`, `B` |-> `es.rollback`,
       `s` |-> `current_st`, `t` |-> `next_st`, `x` |-> `u`]
       step_continuing_protected_frames) >> simp[]) >>
  `account_already_created (lookup_account a current_st.rollback.accounts)` by
    (qpat_assum `!addr. account_already_created _ ==> account_already_created _`
       (qspec_then `a` mp_tac) >> simp[]) >>
  `~account_empty (lookup_account a next_st.originalAccounts)` by
    (mp_tac (Q.INST [`s` |-> `current_st`, `t` |-> `next_st`,
       `r` |-> `INL u`, `a` |-> `a`] step_creation_original_empty) >> simp[]) >>
  fs[]
QED
