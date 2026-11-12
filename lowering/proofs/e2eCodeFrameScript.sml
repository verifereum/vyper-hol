(*
 * The installed code of a contract survives a transaction's EVM run: only a
 * creation frame's return deposits code, at an address with no code yet.
 *)
Theory e2eCodeFrame
Ancestors
  vfmState vfmContext vfmExecution vfmExecutionProp vfmRunCall vfmAccountFrame
  vfmHandleStep vfmStepLength vfmSameFrame vfmRunWithinFrame
  list pair arithmetic

Theorem handle_step_code_sources[local]:
  s.contexts <> [] /\ handle_step e s = (r,t) /\
  (FST (HD s.contexts)).msgParams.outputTo <> Code a ==>
  (lookup_account a t.rollback.accounts).code =
    (lookup_account a s.rollback.accounts).code \/
  (2 <= LENGTH s.contexts /\
   (lookup_account a t.rollback.accounts).code =
     (lookup_account a (SND (HD s.contexts)).accounts).code)
Proof
  strip_tac >>
  qhdtm_x_assum `handle_step` mp_tac >>
  simp[handle_step_def] >> IF_CASES_TAC
  >- (simp[reraise_def] >> strip_tac >> gvs[]) >>
  simp[handle_def] >>
  strip_assume_tac (INST_TYPE [alpha |-> ``:unit``] handle_create_INR) >>
  simp[] >> strip_tac >>
  drule_all handle_create_preserves_tl_and_snd_hd >> strip_tac >>
  drule_all handle_create_preserves_length >> strip_tac >>
  drule_all handle_create_code_other >> strip_tac >>
  drule_all handle_exception_rollback_sources >> strip_tac >> gvs[]
QED

val code_step_inner = ``do
  context <- get_current_context;
  case FLOOKUP context.msgParams.parsed context.pc of
  | SOME op => ignore_bind (step_inst op) (inc_pc_or_jump op)
  | NONE => if LENGTH context.msgParams.code <= context.pc
            then step_inst Stop else step_inst Invalid
  od``;

Theorem step_inner_inr_grow_saved_accounts[local]:
  wf_state s /\ ^code_step_inner s = (INR e,u) /\
  LENGTH s.contexts < LENGTH u.contexts ==>
  (SND (HD u.contexts)).accounts = s.rollback.accounts
Proof
  strip_tac >>
  `s.contexts <> []` by gvs[wf_state_def] >>
  gvs[bind_def, get_current_context_def, return_def, fail_def,
      COND_RATOR, vfmTypesTheory.option_CASE_rator, AllCaseEqs(),
      ignore_bind_def]
  >~ [`step_inst Stop`]
  >- (`preserves_same_frame (step_inst Stop)` by simp[] >>
      imp_res_tac psf_imp_length_contexts_preserved >> gvs[])
  >~ [`step_inst Invalid`]
  >- (`preserves_same_frame (step_inst Invalid)` by simp[] >>
      imp_res_tac psf_imp_length_contexts_preserved >> gvs[])
  >- (`preserves_same_frame (inc_pc_or_jump op)` by simp[] >>
      drule_then drule psf_imp_length_contexts_preserved >>
      (impl_tac >-
        (strip_tac >>
         gvs[inc_pc_or_jump_def, COND_RATOR, AllCaseEqs(), return_def] >>
         gvs[bind_def, AllCaseEqs(), get_current_context_def, fail_def])) >>
      strip_tac >> drule step_inst_inl_grew_is_call >> gvs[] >>
      strip_tac >> gvs[inc_pc_or_jump_def, return_def]) >>
  rename1 `step_inst op s = (INR e,u)` >>
  drule step_inst_inr_grew_is_call_family >>
  (impl_tac >- gvs[]) >>
  reverse (Cases_on `step_inst op s = step_call op s`)
  >- (strip_tac >> gvs[step_inst_def]) >>
  gvs[] >> strip_tac >>
  irule step_call_grow_saved_accounts >> metis_tac[]
QED

Theorem step_installed_code_current[local]:
  wf_state s /\ c <> [] /\
  (lookup_account a s.rollback.accounts).code = c /\
  (2 <= LENGTH s.contexts ==>
    (lookup_account a (SND (HD s.contexts)).accounts).code = c) /\
  (FST (HD s.contexts)).msgParams.outputTo <> Code a /\
  step s = (r,t) ==>
  (lookup_account a t.rollback.accounts).code = c
Proof
  strip_tac >>
  `s.contexts <> []` by gvs[wf_state_def] >>
  qhdtm_x_assum `step` mp_tac >> simp[step_def, handle_def] >>
  Cases_on `^code_step_inner s` >>
  rename1 `^code_step_inner s = (q,u)` >>
  `(lookup_account a u.rollback.accounts).code = c` by
    (drule_all step_inner_nonce_code >> simp[]) >>
  `same_frame_or_grow ^code_step_inner` by simp[] >>
  `LENGTH s.contexts <= LENGTH u.contexts` by
    (drule_all same_frame_or_grow_length >> simp[]) >>
  `u.contexts <> []` by (strip_tac >> gvs[]) >>
  Cases_on `q` >> simp[] >> strip_tac
  >- gvs[] >>
  rename1 `handle_step e u = (r,t)` >>
  Cases_on `LENGTH u.contexts = LENGTH s.contexts`
  >- (`same_frame_rel s u` by
        (drule_all same_frame_or_grow_eq_length >> simp[]) >>
      `(FST (HD u.contexts)).msgParams.outputTo <> Code a /\
       (2 <= LENGTH u.contexts ==>
        (lookup_account a (SND (HD u.contexts)).accounts).code = c)` by
        gvs[same_frame_rel_def] >>
      drule_all handle_step_code_sources >> strip_tac >> gvs[]) >>
  `LENGTH s.contexts < LENGTH u.contexts` by decide_tac >>
  drule_at (Pat `bind _ _ _ = _`) step_inner_inr_grow_protected_head >>
  disch_then (qspec_then `a` mp_tac) >> simp[NULL_EQ] >> strip_tac >>
  drule_all step_inner_inr_grow_saved_accounts >> strip_tac >>
  `(FST (HD u.contexts)).msgParams.outputTo <> Code a` by simp[] >>
  drule_all handle_step_code_sources >> strip_tac >> gvs[]
QED

Theorem step_installed_code_rollbacks[local]:
  wf_state s /\ c <> [] /\
  EVERY (\rb. (lookup_account a rb.accounts).code = c)
    (active_rollbacks 1 s) /\
  EVERY (\cr. (FST cr).msgParams.outputTo <> Code a) s.contexts /\
  step s = (r,t) ==>
  EVERY (\rb. (lookup_account a rb.accounts).code = c)
    (active_rollbacks 1 t)
Proof
  strip_tac >>
  `s.contexts <> [] /\ outputTo_consistent_stack s /\
   EVERY (wf_context o FST) s.contexts` by gvs[wf_state_def] >>
  `(lookup_account a s.rollback.accounts).code = c` by
    gvs[active_rollbacks_def] >>
  `(2 <= LENGTH s.contexts ==>
     (lookup_account a (SND (HD s.contexts)).accounts).code = c)` by
    (strip_tac >>
     `MEM (SND (HD s.contexts)) (active_rollbacks 1 s)` by
       (irule (cj 2 active_rollbacks_pop_sources) >> simp[]) >>
     gvs[EVERY_MEM]) >>
  `(FST (HD s.contexts)).msgParams.outputTo <> Code a` by
    (Cases_on `s.contexts` >> gvs[]) >>
  `(lookup_account a t.rollback.accounts).code = c` by
    (drule_all step_installed_code_current >> simp[]) >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (irule active_rollbacks_same_frame_transport >> simp[] >>
      qexists_tac `s` >> simp[] >> irule step_same_frame >>
      metis_tac[outputTo_consistent_stack_imp_consistent]) >>
  Cases_on `LENGTH t.contexts < LENGTH s.contexts`
  >- (drule_all step_pop_structure >> strip_tac >>
      irule active_rollbacks_pop_transport >> simp[] >> metis_tac[]) >>
  `LENGTH s.contexts < LENGTH t.contexts` by decide_tac >>
  `LENGTH t.contexts > LENGTH s.contexts` by simp[] >>
  drule_all step_push_structure >> strip_tac >>
  irule active_rollbacks_push_transport >> simp[] >>
  qexistsl_tac [
    `\rb. (lookup_account a rb.accounts).code = c`,
    `\x y. (lookup_account a y.accounts).code =
            (lookup_account a x.accounts).code`, `s`] >>
  simp[ADD1] >>
  (reverse conj_tac >- (Cases_on `s.contexts` >> gvs[])) >>
  qx_gen_tac `i` >> strip_tac >>
  Cases_on `i`
  >- (simp[] >> drule_all step_growth_saved_head_nonce_code >>
      disch_then (qspec_then `a` mp_tac) >> simp[]) >>
  rename1 `SUC n < LENGTH s.contexts` >> simp[] >>
  `lookup_account a (SND (EL (SUC n) t.contexts)).accounts =
   lookup_account a (SND (EL n s.contexts)).accounts` by
    (irule step_growth_old_snapshot_lookup >> simp[NULL_EQ] >>
     metis_tac[]) >> simp[]
QED

(* A step can push Code a only after the collision check has established
   that a has no installed code. Existing frames retain their output target. *)
Theorem step_excludes_installed_code_frame[local]:
  wf_state s /\
  (lookup_account a s.rollback.accounts).code <> [] /\
  EVERY (\cr. (FST cr).msgParams.outputTo <> Code a) s.contexts /\
  step s = (r,t) ==>
  EVERY (\cr. (FST cr).msgParams.outputTo <> Code a) t.contexts
Proof
  strip_tac >>
  `s.contexts <> [] /\ outputTo_consistent_stack s /\
   EVERY (wf_context o FST) s.contexts` by gvs[wf_state_def] >>
  Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (suspend "growth") >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (drule_all step_same_frame_foreign >> strip_tac >>
      Cases_on `s.contexts` >> gvs[] >>
      Cases_on `t.contexts` >> gvs[]) >>
  `LENGTH t.contexts < LENGTH s.contexts` by decide_tac >>
  drule_all step_pop_structure >> strip_tac >>
  qpat_x_assum `EVERY (\cr. _ <> Code a) s.contexts` mp_tac >>
  qpat_assum `s.contexts = _::_::_`
    (fn th => pure_once_rewrite_tac[th]) >>
  simp[] >> gvs[]
QED

Resume step_excludes_installed_code_frame[growth]:
  `(FST (HD t.contexts)).msgParams.outputTo <> Code a` by
    (strip_tac >>
     `~account_already_created (lookup_account a s.rollback.accounts)` by
       (irule (SRULE [] step_growth_code_provenance) >>
        qexistsl_tac [`r`, `s`, `t`] >> simp[]) >>
     gvs[account_already_created_def, listTheory.NULL_EQ]) >>
  drule step_push_structure >> (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >>
  Cases_on `t.contexts` >> gvs[] >>
  rename1 `t.contexts = child::tail` >>
  Cases_on `tail` >> gvs[] >>
  rename1 `MAP FST new_tail = MAP FST old_tail` >>
  `EVERY (\ctx. ctx.msgParams.outputTo <> Code a) (MAP FST new_tail)`
    suffices_by simp[listTheory.EVERY_MAP, combinTheory.o_DEF] >>
  qpat_assum `MAP FST new_tail = _` (fn th => rewrite_tac[th]) >>
  simp[listTheory.EVERY_MAP, combinTheory.o_DEF]
QED

Finalise step_excludes_installed_code_frame

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
  strip_tac >> gvs[run_call_def] >>
  `(\p. wf_state (SND p) /\
     EVERY (\rb. (lookup_account a rb.accounts).code =
                    (lookup_account a es.rollback.accounts).code)
       (active_rollbacks 1 (SND p)) /\
     EVERY (\cr. (FST cr).msgParams.outputTo <> Code a)
       (SND p).contexts) (r,es')` suffices_by
    simp[active_rollbacks_def] >>
  irule (MP_CANON WhileTheory.OWHILE_INV_IND) >>
  goal_assum $ drule_at Any >>
  simp[] >> conj_tac
  >- (Cases_on `es.contexts` >> gvs[active_rollbacks_def]) >>
  qx_gen_tac `p` >> PairCases_on `p` >> simp[] >> strip_tac >>
  rename1 `LENGTH state.contexts >= 1` >>
  Cases_on `step state` >> simp[] >>
  conj_tac
  >- (drule step_preserves_wf_state >> simp[]) >>
  conj_tac
  >- (irule step_installed_code_rollbacks >> metis_tac[]) >>
  irule step_excludes_installed_code_frame >>
  goal_assum $ drule_at Any >> simp[] >>
  gvs[active_rollbacks_def]
QED
