(* Code of an existing account survives every prefix above the entry frame. *)
Theory guardReentryCode
Ancestors
  evmCreationGuard vfmRunCall vfmAccountFrame vfmExecution vfmExecutionProp
  vfmState vfmContext vfmTypes vfmSameFrame vfmStoragePredicates
  vfmPreserves vfmStepLength vfmWfState vfmRunWithinFrame vfmStaticCalls vfmHandleStep
  list rich_list pair arithmetic combin

val guard_code_inner = ``do
  context <- get_current_context;
  case FLOOKUP context.msgParams.parsed context.pc of
  | SOME op => ignore_bind (step_inst op) (inc_pc_or_jump op)
  | NONE => if LENGTH context.msgParams.code <= context.pc
            then step_inst Stop else step_inst Invalid
  od``;

val guard_code_prefix = ``\d a (s:execution_state).
  EVERY (\rb. ~NULL (lookup_account a rb.accounts).code)
    (s.rollback :: MAP SND (TAKE (LENGTH s.contexts-d) s.contexts)) /\
  EVERY (\mp. mp.outputTo <> Code a)
    (MAP (\p. (FST p).msgParams)
      (TAKE (LENGTH s.contexts-d) s.contexts))``;

Theorem guard_reaches_code_nonempty:
  wf_state es /\ ~NULL (lookup_account a es.rollback.accounts).code /\
  run_call_reaches es s /\ LENGTH es.contexts <= LENGTH s.contexts ==>
  ~NULL (lookup_account a s.rollback.accounts).code
Proof
  strip_tac >>
  `0 < LENGTH es.contexts` by
    (Cases_on `es.contexts` >> gvs[wf_state_def]) >>
  `wf_state s /\
   (LENGTH es.contexts <= LENGTH s.contexts ==>
    ^guard_code_prefix (LENGTH es.contexts) a s)`
    suffices_by fs[] >>
  BETA_TAC >>
  irule (BETA_RULE (Q.INST
    [`Q` |-> `\st. wf_state st /\
      (LENGTH es.contexts <= LENGTH st.contexts ==>
       ^guard_code_prefix (LENGTH es.contexts) a st)`,
     `es` |-> `es`, `s` |-> `s`] run_call_reaches_inv)) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `step current_st = (INL u,next_st)` >>
  `wf_state next_st` by
    (drule_all step_preserves_wf_state >> simp[]) >>
  simp[] >> strip_tac >> fs[] >>
  qabbrev_tac `d = LENGTH es.contexts` >>
  `current_st.contexts <> [] /\ outputTo_consistent_stack current_st /\
   outputTo_consistent current_st /\
   EVERY (wf_context o FST) current_st.contexts` by
    metis_tac[wf_state_def, outputTo_consistent_stack_imp_consistent] >>
  `~NULL (lookup_account a current_st.rollback.accounts).code` by fs[] >>
  `account_already_created (lookup_account a current_st.rollback.accounts)` by
    fs[account_already_created_def] >>
  `~NULL (lookup_account a next_st.rollback.accounts).code` by
    (qpat_x_assum `step current_st = _` mp_tac >>
     simp[step_def, handle_def] >>
     Cases_on `^guard_code_inner current_st` >>
     rename1 `^guard_code_inner current_st = (q,mid)` >>
     `(lookup_account a mid.rollback.accounts).code =
       (lookup_account a current_st.rollback.accounts).code` by
       (drule_all step_inner_nonce_code >> simp[]) >>
     `same_frame_or_grow ^guard_code_inner` by simp[] >>
     `LENGTH current_st.contexts <= LENGTH mid.contexts` by
       (drule_all same_frame_or_grow_length >> simp[]) >>
     `mid.contexts <> []` by (strip_tac >> gvs[]) >>
     Cases_on `q` >> simp[] >> strip_tac
     >- gvs[] >>
     rename1 `handle_step ex mid = (INL (),next_st)` >>
     `~NULL (lookup_account a (SND (HD mid.contexts)).accounts).code /\
      (FST (HD mid.contexts)).msgParams.outputTo <> Code a` by
       (Cases_on `LENGTH mid.contexts = LENGTH current_st.contexts`
        >- (drule_all handle_step_inl_pops >> strip_tac >>
            `d < LENGTH current_st.contexts` by (fs[Abbr `d`] >> decide_tac) >>
            `same_frame_rel current_st mid` by
              (drule_all same_frame_or_grow_eq_length >> simp[]) >>
            `0 < LENGTH current_st.contexts-d` by decide_tac >>
            `~NULL (lookup_account a (SND (HD current_st.contexts)).accounts).code /\
             (FST (HD current_st.contexts)).msgParams.outputTo <> Code a` by
              (Cases_on `LENGTH current_st.contexts-d` >- fs[] >>
               Cases_on `current_st.contexts` >- fs[] >>
               fs[TAKE_def]) >>
            gvs[same_frame_rel_def]) >>
        `LENGTH current_st.contexts < LENGTH mid.contexts` by decide_tac >>
        `?mr. (FST (HD mid.contexts)).msgParams.outputTo = Memory mr` by
          (drule_at (Pat `bind _ _ _ = _`) step_inner_inr_grow_protected_head >>
           disch_then (qspec_then `a` mp_tac) >>
           simp[account_already_created_def]) >>
        simp[] >>
        `(SND (HD mid.contexts)).accounts = current_st.rollback.accounts`
          suffices_by simp[] >>
        qpat_x_assum `^guard_code_inner current_st = (INR ex,mid)` mp_tac >>
        simp[bind_def, get_current_context_def, return_def, fail_def,
             COND_RATOR, vfmTypesTheory.option_CASE_rator, AllCaseEqs(),
             ignore_bind_def] >> rpt strip_tac >> gvs[]
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
        rename1 `step_inst op current_st = (INR ex,mid)` >>
        drule step_inst_inr_grew_is_call_family >>
        (impl_tac >- gvs[]) >>
        reverse (Cases_on `step_inst op current_st = step_call op current_st`)
        >- (strip_tac >> gvs[step_inst_def]) >>
        gvs[] >> metis_tac[step_call_grow_saved_accounts]) >>
     qpat_x_assum `handle_step ex mid = _` mp_tac >>
     simp[handle_step_def] >> IF_CASES_TAC
     >- (simp[reraise_def] >> strip_tac >> gvs[]) >>
     simp[handle_def] >>
     strip_assume_tac (INST_TYPE [alpha |-> ``:unit``] handle_create_INR |>
       Q.INST [`e` |-> `ex`, `s` |-> `mid`]) >>
     simp[] >> strip_tac >>
     drule_all handle_create_preserves_tl_and_snd_hd >> strip_tac >>
     drule_all handle_create_preserves_length >> strip_tac >>
     drule_all handle_create_code_other >> strip_tac >>
     drule_all handle_exception_rollback_sources >> strip_tac >> gvs[]) >>
  `EVERY (\rb. ~NULL (lookup_account a rb.accounts).code)
    (next_st.rollback :: MAP SND
      (TAKE (LENGTH next_st.contexts-d) next_st.contexts))` by
    (Cases_on `LENGTH next_st.contexts = LENGTH current_st.contexts`
      >- (irule protected_rollbacks_same_frame_transport >>
          simp[] >> qexists_tac `current_st` >> simp[] >>
          irule step_same_frame >> metis_tac[]) >>
      Cases_on `LENGTH next_st.contexts < LENGTH current_st.contexts`
      >- (drule_all step_pop_structure >> strip_tac >>
          mp_tac (protected_rollbacks_pop_transport |> Q.INST
            [`s` |-> `current_st`, `t` |-> `next_st`,
             `d` |-> `d`,
             `P` |-> `\rb. ~NULL (lookup_account a rb.accounts).code`,
             `child` |-> `HD current_st.contexts`, `parent` |-> `parent`,
             `rest` |-> `rest`, `new_head` |-> `new_head`]) >>
          simp[] >> fs[Abbr `d`]) >>
      `LENGTH current_st.contexts < LENGTH next_st.contexts` by decide_tac >>
      `LENGTH next_st.contexts > LENGTH current_st.contexts` by simp[] >>
      drule_all step_push_structure >> strip_tac >>
      irule protected_rollbacks_push_transport >> simp[] >>
      qexistsl_tac
        [`\rb. ~NULL (lookup_account a rb.accounts).code`,
         `\x y. (lookup_account a y.accounts).code =
                  (lookup_account a x.accounts).code`, `current_st`] >>
      simp[ADD1] >> qx_gen_tac `i` >> strip_tac >>
      Cases_on `i`
      >- (simp[] >> drule_all step_growth_saved_head_nonce_code >>
          disch_then (qspec_then `a` mp_tac) >> simp[]) >>
      simp[] >>
      `lookup_account a (SND (EL (SUC n) next_st.contexts)).accounts =
       lookup_account a (SND (EL n current_st.contexts)).accounts` by
        (irule step_growth_old_snapshot_lookup >>
         simp[] >> fs[account_already_created_def]) >> simp[]) >>
  `EVERY (\mp. mp.outputTo <> Code a)
    (MAP (\p. (FST p).msgParams)
      (TAKE (LENGTH next_st.contexts-d) next_st.contexts))` by
    (Cases_on `LENGTH next_st.contexts = LENGTH current_st.contexts`
  >- (irule protected_frames_same_frame_transport >>
      qexists_tac `current_st` >> simp[] >>
      irule step_same_frame >> metis_tac[]) >>
  Cases_on `LENGTH next_st.contexts < LENGTH current_st.contexts`
  >- (drule_all step_pop_structure >> strip_tac >>
      mp_tac (protected_frames_pop_transport |> Q.INST
        [`s` |-> `current_st`, `t` |-> `next_st`,
         `d` |-> `d`, `P` |-> `\mp. mp.outputTo <> Code a`,
         `child` |-> `HD current_st.contexts`, `parent` |-> `parent`,
         `rest` |-> `rest`, `new_head` |-> `new_head`]) >>
      simp[] >> fs[Abbr `d`]) >>
  `LENGTH current_st.contexts < LENGTH next_st.contexts` by decide_tac >>
  `(FST (HD next_st.contexts)).msgParams.outputTo <> Code a` by
    (mp_tac (Q.INST [`B` |-> `current_st.rollback`, `s` |-> `current_st`,
      `t` |-> `next_st`, `r` |-> `INL u`] step_growth_code_provenance) >>
     simp[] >> metis_tac[]) >>
  `LENGTH next_st.contexts > LENGTH current_st.contexts` by simp[] >>
  `1 <= LENGTH current_st.contexts` by decide_tac >>
  drule_all step_push_structure >> strip_tac >>
  irule protected_frames_push_transport >>
  simp[] >> qexists_tac `current_st` >> simp[ADD1] >> fs[Abbr `d`]) >>
  fs[]
QED
