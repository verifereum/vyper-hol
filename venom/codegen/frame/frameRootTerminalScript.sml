(* One-step inversion at a non-creation root. *)
Theory frameRootTerminal
Ancestors
  frameGas vfmContextLength vfmRunCall vfmDecreasesGas vfmStoragePredicates
  vfmExecution vfmExecutionProp vfmContext vfmState vfmTypes vfmHandleStep
  vfmStepLength vfmSameFrame vfmRunWithinFrame vfmStaticCalls

Theorem root_handle_exception[local]:
  s.contexts = [(c,rb)] /\ wf_context c /\
  handle_exception e s = (INR e',t) ==>
  e' = e /\ (e = NONE ==> t = s)
Proof
  strip_tac >>
  qpat_x_assum `handle_exception e s = _` mp_tac >>
  simp[handle_exception_def, get_gas_left_def, consume_gas_def,
       get_current_context_def, set_current_context_def,
       get_num_contexts_def, set_return_data_def,
       bind_def, ignore_bind_def, return_def, reraise_def,
       assert_def, fail_def, wf_context_def] >>
  Cases_on `e = NONE` >>
  gvs[get_current_context_def, set_current_context_def, bind_def,
      ignore_bind_def, return_def, reraise_def, assert_def, fail_def,
      wf_context_def] >>
  Cases_on `e = SOME Reverted` >>
  gvs[get_current_context_def, set_current_context_def, bind_def,
      ignore_bind_def, return_def, reraise_def, assert_def, fail_def]
QED

Theorem root_handle_step[local]:
  s.contexts = [(c,rb)] /\ wf_context c /\
  (!a. c.msgParams.outputTo <> Code a) /\
  handle_step e s = (INR e',t) ==>
  e' = e /\ (e = NONE ==> t = s)
Proof
  strip_tac >>
  qpat_x_assum `handle_step e s = _` mp_tac >>
  Cases_on `vfm_abort e`
  >- simp[handle_step_def, reraise_def] >>
  `handle_create e s = ((INR e : unit + exception option),s)` by
    (irule (handle_create_reraises |> REWRITE_RULE [reraise_def]) >> gvs[]) >>
  gvs[handle_step_def, handle_def] >> strip_tac >>
  drule_all root_handle_exception >> simp[]
QED

Theorem root_inner_terminal[local]:
  wf_state s /\ s.contexts = [(c,rb)] /\
  (!a. c.msgParams.outputTo <> Code a) /\
  step s = (INR e',t) ==>
  ?e u c1 rb1. step_inner s = (INR e,u) /\
    u.contexts = [(c1,rb1)] /\ e' = e /\
    (e = NONE ==> t = u)
Proof
  strip_tac >>
  qpat_x_assum `step s = _` mp_tac >>
  simp[step_eq_handle_step_inner, handle_def] >>
  Cases_on `step_inner s` >> Cases_on `FST (step_inner s)` >> gvs[] >>
  rename1 `step_inner s = (INR e,u)` >> strip_tac >>
  `s.contexts <> []` by simp[] >>
  `EVERY (wf_context o FST) u.contexts /\ u.contexts <> []`
    by (mp_tac decreases_gas_cred_step_inner >>
        simp[decreases_gas_cred_def] >>
        disch_then (qspec_then `s` mp_tac) >>
        gvs[wf_state_def]) >>
  `stack_room_ok u /\ gas_stack_ok u`
    by metis_tac[step_inner_preserves_stack_room_gas_ok] >>
  `~(LENGTH u.contexts >= 2)` by
    (strip_tac >>
     `outputTo_consistent s` by
       metis_tac[outputTo_consistent_stack_imp_consistent, wf_state_def] >>
     `~vfm_abort e` by
       (mp_tac (Q.INST [`s'` |-> `u`] step_inner_inr_grow_not_abort) >>
        gvs[step_inner_def]) >>
     drule_all handle_step_not_abort_returns_inl >> simp[]) >>
  `?c1 rb1. u.contexts = [(c1,rb1)]` by
    (Cases_on `u.contexts` >> gvs[] >>
     rename1 `u.contexts = h::cs` >> Cases_on `cs` >> gvs[] >>
     Cases_on `h` >> simp[]) >>
  `same_frame_rel s u` by
    (irule (INST_TYPE [alpha |-> ``:unit``] same_frame_or_grow_eq_length) >>
     gvs[] >> qexistsl_tac [`step_inner`,`INR e`] >> simp[]) >>
  `!a. c1.msgParams.outputTo <> Code a` by
    gvs[same_frame_rel_def] >>
  `wf_context c1` by gvs[] >>
  drule_all root_handle_step >> strip_tac >>
  qexistsl_tac [`c1`,`rb1`] >> gvs[]
QED

Theorem root_inner_inst[local]:
  s.contexts = [(c,rb)] /\ step_inner s = (INR e,u) /\
  e <> SOME InvalidJumpDest /\ e <> SOME Impossible ==>
  ?op. frame_inst_at s s op /\ step_inst op s = (INR e,u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `step_inner s = _` mp_tac >>
  simp[step_inner_def, get_current_context_def, bind_def, return_def] >>
  Cases_on `FLOOKUP c.msgParams.parsed c.pc`
  >- (Cases_on `LENGTH c.msgParams.code <= c.pc` >>
      gvs[frame_inst_at_def] >> strip_tac >>
      goal_assum $ drule_at Any >> simp[]) >>
  rename1 `FLOOKUP c.msgParams.parsed c.pc = SOME op` >>
  gvs[ignore_bind_def] >>
  Cases_on `step_inst op s` >> Cases_on `FST (step_inst op s)` >> gvs[bind_def]
  >- (strip_tac >>
      drule inc_pc_or_jump_inr_eq >> gvs[]) >>
  strip_tac >> qexists_tac `op` >>
  gvs[frame_inst_at_def]
QED

Theorem root_step_ends_at_inst:
  wf_state s /\ s.contexts = [(c,rb)] /\
  (!a. c.msgParams.outputTo <> Code a) /\ step s = (r,t) ==>
  (r = INR (SOME OutOfGas) ==>
   ?op u. frame_inst_at s s op /\
          step_inst op s = (INR (SOME OutOfGas),u) /\ LENGTH u.contexts = 1) /\
  (r = INR NONE ==>
   ?op. frame_inst_at s s op /\ step_inst op s = (INR NONE,t) /\
        LENGTH t.contexts = 1)
Proof
  strip_tac >> conj_tac >> strip_tac >> gvs[] >>
  drule_all root_inner_terminal >> strip_tac >> gvs[] >>
  drule_at (Pat `step_inner _ = _`) root_inner_inst >> simp[] >>
  strip_tac >>
  goal_assum $ drule_at Any >> gvs[]
QED
