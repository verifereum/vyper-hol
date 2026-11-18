(* Concrete overflow inversion for the full execution step. *)
Theory stackBoundOverflow
Ancestors
  vfmContextLength vfmRunCall vfmDecreasesGas vfmStoragePredicates
  vfmWfState vfmHandleStep vfmStepLength vfmSameFrame
  vfmExecution vfmExecutionProp vfmContext vfmState vfmTypes
  finite_map list pair

Theorem sb_single_exception_overflow[local]:
  !s e. LENGTH s.contexts = 1 /\
    FST (handle_exception e s) = INR (SOME StackOverflow) ==>
    e = SOME StackOverflow
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  Cases_on `e = NONE` >> Cases_on `e = SOME Reverted` >>
  gvs[handle_exception_def, get_gas_left_def, consume_gas_def,
      get_current_context_def, set_current_context_def,
      get_num_contexts_def, set_return_data_def,
      bind_def, ignore_bind_def, return_def, reraise_def,
      assert_def, fail_def, AllCaseEqs()] >>
  Cases_on `h0.msgParams.gasLimit - h0.gasUsed + h0.gasUsed <=
            h0.msgParams.gasLimit` >> gvs[]
QED

Theorem sb_create_overflow[local]:
  !s e. s.contexts <> [] /\
    FST (handle_create e s : unit execution_result) = INR (SOME StackOverflow) ==>
    e = SOME StackOverflow
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  Cases_on `e` >> Cases_on `h0.msgParams.outputTo` >>
  gvs[handle_create_def, get_return_data_def, get_output_to_def,
      get_current_context_def, set_current_context_def,
      consume_gas_def, update_accounts_def, bind_def, ignore_bind_def,
      return_def, reraise_def, assert_def, fail_def, AllCaseEqs()] >>
  gvs[COND_RATOR, COND_RAND, AllCaseEqs()]
QED

Theorem sb_single_handler_overflow[local]:
  !s e. LENGTH s.contexts = 1 /\
    FST (handle_step e s) = INR (SOME StackOverflow) ==>
    e = SOME StackOverflow
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `vfm_abort e` >- gvs[handle_step_def, reraise_def] >>
  qpat_x_assum `FST _ = _` mp_tac >>
  simp[handle_step_def, handle_def] >>
  Cases_on `handle_create e s : unit execution_result` >>
  Cases_on `q` >> gvs[] >> strip_tac >>
  rename1 `handle_create e s = (INR err,mid)` >>
  `LENGTH mid.contexts = 1` by metis_tac[handle_create_preserves_length] >>
  `err = SOME StackOverflow` by metis_tac[sb_single_exception_overflow] >>
  irule sb_create_overflow >> qexists_tac `s` >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem sb_inner_overflow_inst[local]:
  !s op t. s.contexts <> [] /\
    (case FLOOKUP (FST (HD s.contexts)).msgParams.parsed
                 (FST (HD s.contexts)).pc of
       SOME op' => op = op'
     | NONE => op = if LENGTH (FST (HD s.contexts)).msgParams.code <=
                           (FST (HD s.contexts)).pc
                      then Stop else Invalid) /\
    step_inner s = (INR (SOME StackOverflow),t) ==>
    step_inst op s = (INR (SOME StackOverflow),t)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  qpat_x_assum `step_inner _ = _` mp_tac >>
  simp[step_inner_def, get_current_context_def, bind_def, return_def] >>
  Cases_on `FLOOKUP h0.msgParams.parsed h0.pc` >> gvs[]
  >- (Cases_on `LENGTH h0.msgParams.code <= h0.pc` >> gvs[]) >>
  simp[ignore_bind_def, bind_def] >>
  Cases_on `step_inst op s` >> Cases_on `q` >> gvs[] >>
  strip_tac >> drule inc_pc_or_jump_inr_eq >> simp[]
QED

Theorem sb_step_overflow_inner[local]:
  !s t e. wf_state s /\
    FST (step s) = INR (SOME StackOverflow) /\
    step_inner s = (INR e,t) ==>
    e = SOME StackOverflow /\ LENGTH t.contexts = LENGTH s.contexts
Proof
  rpt gen_tac >> strip_tac >>
  `s.contexts <> []` by gvs[wf_state_def] >>
  `FST (handle_step e t) = INR (SOME StackOverflow)` by
    gvs[step_eq_handle_step_inner, handle_def] >>
  `~vfm_abort e` by
    (strip_tac >> gvs[handle_step_def, reraise_def]) >>
  `EVERY (wf_context o FST) t.contexts /\ t.contexts <> []` by
    (mp_tac decreases_gas_cred_step_inner >>
     simp[decreases_gas_cred_def] >>
     disch_then (qspec_then `s` mp_tac) >> gvs[wf_state_def]) >>
  `stack_room_ok t /\ gas_stack_ok t` by
    metis_tac[step_inner_preserves_stack_room_gas_ok] >>
  `~(LENGTH t.contexts >= 2)` by
    (strip_tac >> Cases_on `handle_step e t` >>
     drule_all handle_step_not_abort_returns_inl >> gvs[]) >>
  `LENGTH t.contexts = 1` by
    (Cases_on `t.contexts` >> gvs[] >>
     rename1 `t.contexts = h::cs` >> Cases_on `cs` >> gvs[]) >>
  `LENGTH s.contexts <= LENGTH t.contexts` by
    (`same_frame_or_grow step_inner` by simp[] >>
     drule_all same_frame_or_grow_length >> simp[]) >>
  conj_tac >- metis_tac[sb_single_handler_overflow] >>
  Cases_on `s.contexts` >> gvs[] >>
  rename1 `s.contexts = h::cs` >> Cases_on `cs` >> gvs[]
QED

Theorem sb_step_no_overflow_from_raw:
  !s op.
    wf_state s /\ s.contexts <> [] /\
    (case FLOOKUP (FST (HD s.contexts)).msgParams.parsed
                 (FST (HD s.contexts)).pc of
       SOME op' => op = op'
     | NONE => op = if LENGTH (FST (HD s.contexts)).msgParams.code <=
                           (FST (HD s.contexts)).pc
                      then Stop else Invalid) /\
    (!t. ~(step_inst op s = (INR (SOME StackOverflow),t) /\
            LENGTH t.contexts = LENGTH s.contexts)) ==>
    FST (step s) <> INR (SOME StackOverflow)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `step_inner s` >> Cases_on `q`
  >- gvs[step_eq_handle_step_inner, handle_def] >>
  drule_all sb_step_overflow_inner >> strip_tac >> gvs[] >>
  drule_all sb_inner_overflow_inst >> strip_tac >>
  metis_tac[]
QED
