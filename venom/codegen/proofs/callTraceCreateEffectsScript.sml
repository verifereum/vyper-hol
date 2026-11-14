Theory callTraceCreateEffects
Ancestors
  vfmExecution vfmExecutionProp vfmRunCall vfmStoragePredicates
  vfmPreserves vfmStepLength

Theorem transient_of_rollback[local]:
  preserves_rollback m ==>
  preserves (\s t. t.rollback.tStorage = s.rollback.tStorage) m
Proof
  rw[preserves_rollback_def, preserves_def] >> first_x_assum drule >> simp[]
QED

Theorem transient_bind[local]:
  preserves (\s t. t.rollback.tStorage = s.rollback.tStorage) g /\
  (!x. preserves (\s t. t.rollback.tStorage = s.rollback.tStorage) (f x)) ==>
  preserves (\s t. t.rollback.tStorage = s.rollback.tStorage) (bind g f)
Proof
  strip_tac >> irule preserves_bind >> simp[] >> metis_tac[]
QED

Theorem transient_create_leaves[local]:
  preserves (\s t. t.rollback.tStorage = s.rollback.tStorage) (access_address address) /\
  preserves (\s t. t.rollback.tStorage = s.rollback.tStorage) (abort_create_exists sender) /\
  preserves (\s t. t.rollback.tStorage = s.rollback.tStorage)
    (proceed_create sender address value code gas)
Proof
  rw[preserves_def, access_address_def, domain_check_def, set_domain_def,
     abort_create_exists_def, proceed_create_def, update_accounts_def,
     get_rollback_def, get_original_def, set_original_def, push_context_def,
     bind_def, ignore_bind_def, return_def, fail_def,
     push_stack_def, inc_pc_def, get_current_context_def,
     set_current_context_def, assert_def, AllCaseEqs()] >> gvs[COND_RAND]
QED

Theorem transient_step_create[local]:
  preserves (\s t. t.rollback.tStorage = s.rollback.tStorage) (step_create two)
Proof
  simp[step_create_def, ignore_bind_def] >>
  rpt (ho_match_mp_tac transient_bind >>
       (conj_tac >- (irule transient_of_rollback >> simp[])) >>
       simp[] >> rpt gen_tac) >>
  IF_CASES_TAC
  >- (irule transient_of_rollback >> simp[]) >>
  ho_match_mp_tac transient_bind >>
  (conj_tac >- simp[transient_create_leaves]) >> simp[] >>
  ho_match_mp_tac transient_bind >>
  (conj_tac >- (irule transient_of_rollback >> simp[])) >>
  simp[] >> IF_CASES_TAC >> simp[transient_create_leaves]
QED

Theorem handled_create_same_depth_fields:
  wf_state s /\
  handle (step_create two) handle_step s = (INL u,t) /\
  LENGTH t.contexts = LENGTH s.contexts ==>
  !a. (lookup_account a t.rollback.accounts).code =
        (lookup_account a s.rollback.accounts).code /\
      (lookup_account a t.rollback.accounts).storage =
        (lookup_account a s.rollback.accounts).storage /\
      t.rollback.tStorage a = s.rollback.tStorage a
Proof
  strip_tac >> `s.contexts <> []` by gvs[wf_state_def] >>
  Cases_on `step_create two s` >> Cases_on `q`
  >- (gvs[handle_def] >> gen_tac >>
      mp_tac preserves_nonce_code_step_create >>
      simp[preserves_def] >> disch_then drule >> strip_tac >>
      mp_tac transient_step_create >> simp[preserves_def] >>
      disch_then drule >> strip_tac >> simp[] >>
      drule step_create_storage_object >>
      disch_then (qspec_then `a` mp_tac) >> simp[]) >>
  gvs[handle_def] >>
  drule_all step_create_inr_no_grow >> strip_tac >>
  `r.contexts <> []` by
    metis_tac[step_create_preserves_nonempty_contexts, pairTheory.SND] >>
  drule_all handle_step_inl_pops >> simp[]
QED
