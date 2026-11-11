(* Fixed-address creation-status boundaries for EVM execution. *)
Theory evmCreationGuard
Ancestors
  vfmAccountDeletion vfmExecution vfmExecutionProp vfmState vfmContext
  vfmTypes vfmPreserves vfmRunCall vfmRunWithinFrame vfmAccountFrame
  vfmStepLength vfmSameFrame vfmStoragePredicates list combin finite_map pair arithmetic

Theorem step_inst_creation_original_empty:
  s.contexts <> [] /\
  (account_empty (lookup_account a s.originalAccounts) \/
   account_already_created (lookup_account a s.rollback.accounts)) /\
  step_inst op s = (r,t) ==>
  (account_empty (lookup_account a t.originalAccounts) =
   account_empty (lookup_account a s.originalAccounts))
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  Cases_on `op = Create \/ op = Create2`
  >- (gvs[step_inst_def] >>
      drule_all step_create_deletion_projections >> strip_tac >> gvs[] >>
      Cases_on `a = b` >>
      gvs[lookup_account_def, update_account_def, combinTheory.APPLY_UPDATE_THM,
          account_empty_def, account_already_created_def, empty_account_state_def]) >>
  Cases_on `op = Call \/ op = CallCode \/ op = DelegateCall \/ op = StaticCall`
  >- (gvs[step_inst_def] >>
      drule_all (SRULE [preserves_when_def] step_call_deletion_call) >>
      simp[]) >>
  Cases_on `op = SelfDestruct`
  >- (gvs[step_inst_def] >>
      drule_all step_self_destruct_deletion_provenance >> simp[]) >>
  gvs[] >>
  mp_tac step_inst_deletion_exact >>
  simp[preserves_when_def] >>
  disch_then (qspecl_then [`s`, `r`, `t`] mp_tac) >> simp[]
QED

Theorem step_creation_original_empty:
  wf_state s /\
  (account_empty (lookup_account a s.originalAccounts) \/
   account_already_created (lookup_account a s.rollback.accounts)) /\
  step s = (r,t) ==>
  (account_empty (lookup_account a t.originalAccounts) =
   account_empty (lookup_account a s.originalAccounts))
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  `s.contexts <> []` by gvs[wf_state_def] >>
  qhdtm_x_assum `step` mp_tac >>
  simp[step_def, handle_def, bind_def, get_current_context_def,
       return_def, fail_def, COND_RATOR, COND_RAND] >>
  Cases_on `FLOOKUP (FST (HD s.contexts)).msgParams.parsed
    (FST (HD s.contexts)).pc` >> simp[]
  >- (Cases_on `LENGTH (FST (HD s.contexts)).msgParams.code <=
         (FST (HD s.contexts)).pc` >> simp[] >>
      simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
      metis_tac[step_inst_creation_original_empty,
        step_inst_preserves_nonempty_contexts, SND,
        handle_step_deletion_projections]) >>
  simp[ignore_bind_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  `!op. (SND (step_inst op s)).contexts <> []`
    by simp[step_inst_preserves_nonempty_contexts] >>
  `!op u v. step_inst op s = (v,u) ==>
    (account_empty (lookup_account a u.originalAccounts) =
     account_empty (lookup_account a s.originalAccounts))`
    by metis_tac[step_inst_creation_original_empty] >>
  mp_tac (Q.INST [`op` |-> `x`]
    (SRULE [preserves_when_def] inc_pc_or_jump_deletion_exact)) >>
  metis_tac[SND, handle_step_deletion_projections]
QED

Theorem step_continuing_creation_guard:
  wf_state s /\
  created = account_empty (lookup_account self s.originalAccounts) /\
  (~created ==> account_already_created (lookup_account self s.rollback.accounts)) /\
  step s = (INL (),t) /\ LENGTH s.contexts <= LENGTH t.contexts ==>
  created = account_empty (lookup_account self t.originalAccounts) /\
  (~created ==> account_already_created (lookup_account self t.rollback.accounts))
Proof
  strip_tac >>
  `0 < LENGTH s.contexts` by (Cases_on `s.contexts` >> gvs[wf_state_def]) >>
  `account_empty (lookup_account self t.originalAccounts) =
    account_empty (lookup_account self s.originalAccounts)` by
    (irule step_creation_original_empty >> metis_tac[]) >>
  `!addr. account_already_created (lookup_account addr s.rollback.accounts) ==>
    account_already_created (lookup_account addr t.rollback.accounts)` by
    (mp_tac (Q.INST [`d` |-> `LENGTH s.contexts`, `B` |-> `s.rollback`,
                    `s` |-> `s`, `t` |-> `t`, `x` |-> `()`]
      step_continuing_collision_current) >> simp[]) >>
  metis_tac[]
QED

val creation_step_inner = ``do
  context <- get_current_context;
  case FLOOKUP context.msgParams.parsed context.pc of
  | SOME op => ignore_bind (step_inst op) (inc_pc_or_jump op)
  | NONE => if LENGTH context.msgParams.code <= context.pc
            then step_inst Stop else step_inst Invalid
  od``;

Theorem step_creation_live_guard:
  wf_state s /\
  account_already_created (lookup_account a s.rollback.accounts) /\
  (2 <= LENGTH s.contexts ==>
    account_already_created (lookup_account a (SND (HD s.contexts)).accounts)) /\
  (FST (HD s.contexts)).msgParams.outputTo <> Code a /\
  step s = (r,t) ==>
  account_already_created (lookup_account a t.rollback.accounts)
Proof
  strip_tac >>
  `s.contexts <> []` by gvs[wf_state_def] >>
  qhdtm_x_assum `step` mp_tac >> simp[step_def, handle_def] >>
  Cases_on `^creation_step_inner s` >>
  rename1 `^creation_step_inner s = (q,u)` >>
  `(lookup_account a s.rollback.accounts).nonce <=
     (lookup_account a u.rollback.accounts).nonce /\
   (lookup_account a u.rollback.accounts).code =
     (lookup_account a s.rollback.accounts).code`
    by (irule (SRULE [] step_inner_nonce_code) >> metis_tac[]) >>
  `same_frame_or_grow ^creation_step_inner` by simp[] >>
  `LENGTH s.contexts <= LENGTH u.contexts`
    by (drule_all same_frame_or_grow_length >> simp[]) >>
  `u.contexts <> []` by (strip_tac >> gvs[]) >>
  `account_already_created (lookup_account a u.rollback.accounts)`
    by (gvs[account_already_created_def] >> decide_tac) >>
  Cases_on `q` >> simp[] >> strip_tac
  >- gvs[] >>
  Cases_on `LENGTH u.contexts = LENGTH s.contexts`
  >- (`same_frame_rel s u`
        by (drule_all same_frame_or_grow_eq_length >> simp[]) >>
      `(lookup_account a t.rollback.accounts).nonce <> 0 \/
        ~NULL (lookup_account a t.rollback.accounts).code`
        suffices_by simp[account_already_created_def] >>
      irule handle_step_protected_account >>
      qexistsl_tac [`y`, `r`, `u`] >>
      gvs[same_frame_rel_def, account_already_created_def]) >>
  `LENGTH s.contexts < LENGTH u.contexts` by decide_tac >>
  `((lookup_account a s.rollback.accounts).nonce <> 0 \/
    ~NULL (lookup_account a s.rollback.accounts).code)`
    by gvs[account_already_created_def] >>
  drule_at (Pat `bind _ _ _ = _`) step_inner_inr_grow_protected_head >>
  disch_then (qspec_then `a` mp_tac) >> simp[] >> strip_tac >>
  `(lookup_account a t.rollback.accounts).nonce <> 0 \/
    ~NULL (lookup_account a t.rollback.accounts).code`
    suffices_by simp[account_already_created_def] >>
  irule handle_step_protected_account >>
  qexistsl_tac [`y`, `r`, `u`] >>
  gvs[account_already_created_def]
QED

Theorem step_creation_active_rollbacks:
  0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
  step s = (r,t) /\
  account_already_created (lookup_account a s.rollback.accounts) /\
  account_already_created (lookup_account a t.rollback.accounts) /\
  EVERY (\rb. account_already_created (lookup_account a rb.accounts))
    (active_rollbacks d s) ==>
  EVERY (\rb. account_already_created (lookup_account a rb.accounts))
    (active_rollbacks d t)
Proof
  strip_tac >>
  `s.contexts <> [] /\ outputTo_consistent_stack s /\
   EVERY (wf_context o FST) s.contexts` by gvs[wf_state_def] >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (irule active_rollbacks_same_frame_transport >> simp[] >>
      qexists_tac `s` >> simp[] >> irule step_same_frame >>
      metis_tac[outputTo_consistent_stack_imp_consistent]) >>
  Cases_on `LENGTH t.contexts < LENGTH s.contexts`
  >- (drule_all step_pop_structure >> strip_tac >>
      irule active_rollbacks_pop_transport >>
      simp[] >> metis_tac[]) >>
  `LENGTH s.contexts < LENGTH t.contexts` by decide_tac >>
  `LENGTH t.contexts > LENGTH s.contexts` by simp[] >>
  drule_all step_push_structure >> strip_tac >>
  irule active_rollbacks_push_transport >>
  simp[] >>
  qexistsl_tac [
    `\rb. account_already_created (lookup_account a rb.accounts)`,
    `\x y. account_already_created (lookup_account a x.accounts) ==>
            account_already_created (lookup_account a y.accounts)`, `s`] >>
  simp[ADD1] >> qx_gen_tac `i` >> strip_tac >>
  Cases_on `i`
  >- (simp[] >>
      drule_all step_growth_saved_head_nonce_code >>
      disch_then (qspec_then `a` mp_tac) >>
      gvs[account_already_created_def] >> decide_tac) >>
  simp[] >> strip_tac >>
  `lookup_account a (SND (EL (SUC n) t.contexts)).accounts =
   lookup_account a (SND (EL n s.contexts)).accounts`
    by (irule step_growth_old_snapshot_lookup >>
        gvs[account_already_created_def]) >> simp[]
QED

Theorem step_creation_code_prefix:
  0 < d /\ d <= LENGTH s.contexts /\ wf_state s /\
  step s = (INL x,t) /\ d <= LENGTH t.contexts /\
  account_already_created (lookup_account a s.rollback.accounts) /\
  EVERY (\p. (FST p).msgParams.outputTo <> Code a)
    (TAKE (LENGTH s.contexts-d+1) s.contexts) ==>
  EVERY (\p. (FST p).msgParams.outputTo <> Code a)
    (TAKE (LENGTH t.contexts-d+1) t.contexts)
Proof
  strip_tac >>
  `s.contexts <> [] /\ outputTo_consistent_stack s /\
   EVERY (wf_context o FST) s.contexts` by gvs[wf_state_def] >>
  `LENGTH s.contexts-d+1 = LENGTH s.contexts-(d-1) /\
   LENGTH t.contexts-d+1 = LENGTH t.contexts-(d-1)` by decide_tac >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (`same_frame_rel s t` by (irule step_same_frame >>
        metis_tac[outputTo_consistent_stack_imp_consistent]) >>
      drule (Q.INST [`d` |-> `d-1`,
        `P` |-> `\mp. mp.outputTo <> Code a`]
        protected_frames_same_frame_transport) >>
      simp[EVERY_MAP] >>
      disch_then (qspecl_then [`d`, `a`] mp_tac) >> fs[]) >>
  Cases_on `LENGTH t.contexts < LENGTH s.contexts`
  >- (drule_all step_pop_structure >> strip_tac >>
      mp_tac (Q.INST [`d` |-> `d-1`, `child` |-> `HD s.contexts`,
        `P` |-> `\mp. mp.outputTo <> Code a`]
        protected_frames_pop_transport) >>
      simp[EVERY_MAP] >> disch_then irule >> gvs[] >> metis_tac[]) >>
  `LENGTH s.contexts < LENGTH t.contexts` by decide_tac >>
  `LENGTH t.contexts > LENGTH s.contexts` by simp[] >>
  ` (FST (HD t.contexts)).msgParams.outputTo <> Code a` by
    (mp_tac (Q.INST [`B` |-> `s.rollback`, `r` |-> `INL x`]
       step_growth_code_provenance) >>
     simp[] >> metis_tac[]) >>
  drule_all step_push_structure >> strip_tac >>
  Cases_on `d = 1`
  >- (gvs[] >> Cases_on `s.contexts` >> gvs[] >>
      Cases_on `t.contexts` >> gvs[] >>
      rename1 `t.contexts = child::cs` >>
      Cases_on `cs` >> gvs[] >>
      `LENGTH t'' = LENGTH t'` by decide_tac >>
      `MAP (\c:context. c.msgParams.outputTo) (MAP FST t'') =
       MAP (\c:context. c.msgParams.outputTo) (MAP FST t')` by simp[] >>
      `EVERY (\out. out <> Code a)
        (MAP (\c:context. c.msgParams.outputTo) (MAP FST t''))`
        by (pure_asm_rewrite_tac[] >> simp[EVERY_MAP]) >>
      qpat_x_assum `LENGTH t'' = LENGTH t'`
        (fn th => rewrite_tac[GSYM th]) >> fs[EVERY_MAP]) >>
  mp_tac (Q.INST [`d` |-> `d-1`,
    `P` |-> `\mp. mp.outputTo <> Code a`]
    protected_frames_push_transport) >>
  simp[EVERY_MAP, ADD1] >> disch_then irule >> fs[]
QED
