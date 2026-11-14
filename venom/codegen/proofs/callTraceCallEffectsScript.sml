Theory callTraceCallEffects
Ancestors
  vfmExecution vfmExecutionProp vfmAccountFrame vfmStaticCalls
  vfmPreserves vfmRunCall vfmStepLength vfmSameFrame
  asmFrameCallStep vfmHandleStep

Theorem proceed_call_fields[local]:
  s.contexts <> [] /\
  proceed_call op sender address value ao az code gas output s = (r,t) ==>
  !a. (lookup_account a t.rollback.accounts).code =
        (lookup_account a s.rollback.accounts).code /\
      (lookup_account a t.rollback.accounts).storage =
        (lookup_account a s.rollback.accounts).storage /\
      t.rollback.tStorage a = s.rollback.tStorage a
Proof
  strip_tac >> Cases_on `op <> CallCode /\ 0 < value` >>
  gvs[proceed_call_def, bind_def, ignore_bind_def,
      get_rollback_def, read_memory_def, get_current_context_def,
      get_caller_def, get_value_def, get_static_def,
      push_context_def, update_accounts_def, return_def, fail_def,
      AllCaseEqs()] >>
  qmatch_asmsub_abbrev_tac `(if _ then _ else _) ss = _` >>
  (Cases_on `fIN address precompile_addresses`
  >- (gvs[] >>
      qmatch_asmsub_abbrev_tac `dpa ss = _` >>
      `cp dpa` by simp[Abbr `dpa`] >>
      `ss.contexts <> []` by simp[Abbr `ss`] >>
      qpat_x_assum `cp dpa` mp_tac >> rewrite_tac[cp_def] >>
      disch_then drule_all >> strip_tac >>
      gvs[cp_rel_def, Abbr `ss`, transfer_value_preserves_code,
          transfer_value_preserves_storage]) >>
  gvs[return_def, Abbr `ss`, transfer_value_preserves_code,
      transfer_value_preserves_storage])
QED

Theorem call_fields_cp_bind[local]:
  cp g /\
  (!x s r t. s.contexts <> [] /\ f x s = (r,t) ==>
    !a. (lookup_account a t.rollback.accounts).code =
          (lookup_account a s.rollback.accounts).code /\
        (lookup_account a t.rollback.accounts).storage =
          (lookup_account a s.rollback.accounts).storage /\
        t.rollback.tStorage a = s.rollback.tStorage a) ==>
  !s r t. s.contexts <> [] /\ bind g f s = (r,t) ==>
    !a. (lookup_account a t.rollback.accounts).code =
          (lookup_account a s.rollback.accounts).code /\
        (lookup_account a t.rollback.accounts).storage =
          (lookup_account a s.rollback.accounts).storage /\
        t.rollback.tStorage a = s.rollback.tStorage a
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[bind_def, AllCaseEqs()] >>
  qpat_x_assum `cp g` mp_tac >> rewrite_tac[cp_def] >>
  disch_then drule_all >> strip_tac >> gvs[] >>
  qpat_x_assum `!x s r t. _` (qspecl_then [`x`, `s''`, `r`, `t`] mp_tac) >>
  simp[]
QED

Theorem step_call_fields[local]:
  !s r t. s.contexts <> [] /\ step_call op s = (r,t) ==>
    !a. (lookup_account a t.rollback.accounts).code =
          (lookup_account a s.rollback.accounts).code /\
        (lookup_account a t.rollback.accounts).storage =
          (lookup_account a s.rollback.accounts).storage /\
        t.rollback.tStorage a = s.rollback.tStorage a
Proof
  simp[step_call_def, ignore_bind_def] >>
  ho_match_mp_tac call_fields_cp_bind >> simp[] >> gen_tac >>
  pairarg_tac >> simp[] >>
  ho_match_mp_tac call_fields_cp_bind >> simp[] >> gen_tac >>
  ho_match_mp_tac call_fields_cp_bind >> simp[] >> gen_tac >>
  ho_match_mp_tac call_fields_cp_bind >> simp[] >> gen_tac >>
  ho_match_mp_tac call_fields_cp_bind >> simp[] >>
  Cases >> simp[] >>
  ho_match_mp_tac call_fields_cp_bind >> simp[] >> gen_tac >>
  pairarg_tac >> simp[] >>
  ho_match_mp_tac call_fields_cp_bind >> simp[] >>
  ho_match_mp_tac call_fields_cp_bind >> simp[] >>
  ho_match_mp_tac call_fields_cp_bind >> simp[] >>
  ho_match_mp_tac call_fields_cp_bind >> simp[] >> gen_tac >>
  IF_CASES_TAC
  >- (rpt strip_tac >>
      `cp (abort_call_value stipend)` by simp[] >>
      qpat_x_assum `cp _` mp_tac >> rewrite_tac[cp_def] >>
      disch_then drule_all >> simp[cp_rel_def]) >>
  ho_match_mp_tac call_fields_cp_bind >> simp[] >>
  ho_match_mp_tac call_fields_cp_bind >> simp[] >> gen_tac >>
  IF_CASES_TAC
  >- (rpt strip_tac >>
      `cp (abort_unuse stipend)` by simp[] >>
      qpat_x_assum `cp _` mp_tac >> rewrite_tac[cp_def] >>
      disch_then drule_all >> simp[cp_rel_def]) >>
  rpt gen_tac >> strip_tac >> drule_all proceed_call_fields >> simp[]
QED

Theorem handled_call_same_depth_fields:
  wf_state s /\
  handle (step_call op) handle_step s = (INL u,t) /\
  LENGTH t.contexts = LENGTH s.contexts ==>
  !a. (lookup_account a t.rollback.accounts).code =
        (lookup_account a s.rollback.accounts).code /\
      (lookup_account a t.rollback.accounts).storage =
        (lookup_account a s.rollback.accounts).storage /\
      t.rollback.tStorage a = s.rollback.tStorage a
Proof
  strip_tac >> `s.contexts <> []` by gvs[wf_state_def] >>
  gvs[handle_def, AllCaseEqs()]
  >- (drule_all step_call_fields >> simp[]) >>
  rename1 `step_call op s = (INR ex,mid)` >>
  `mid.contexts <> []` by
    (metis_tac[vfmExecutionPropTheory.step_call_preserves_nonempty_contexts, pairTheory.SND]) >>
  drule_all handle_step_inl_pops >> strip_tac >>
  `LENGTH s.contexts < LENGTH mid.contexts` by decide_tac >>
  drule_all step_call_reaches_proceed_call >> strip_tac >>
  `u.contexts <> []` by gvs[cp_rel_def] >>
  drule_all asm_proceed_call_saved_checkpoint >> strip_tac >>
  drule_all proceed_call_memory_output >> strip_tac >>
  drule_all asm_proceed_call_terminal_kind >> strip_tac >>
  drule_all asm_call_memory_handle_step >> strip_tac >>
  gvs[] >>
  drule_all handle_exception_rollback_sources >> strip_tac >>
  drule_all step_call_fields >> strip_tac >>
  gvs[cp_rel_def]
QED
