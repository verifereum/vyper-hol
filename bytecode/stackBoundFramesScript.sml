(* Transfer of a suspended checker continuation through frame handlers. *)
Theory stackBoundFrames
Ancestors
  stackBoundInterface stackBoundDefs vfmRunCall vfmWfState vfmHandleStep vfmRunWithinFrame
  vfmSameFrame vfmStepLength vfmExecution vfmExecutionProp vfmContext
  vfmState list rich_list pair finite_map

Theorem sb_handle_no_same_depth_success:
  s.contexts <> [] /\ handle_step e s = (INL (),t) ==>
  LENGTH t.contexts < LENGTH s.contexts
Proof
  strip_tac >> drule_all handle_step_inl_pops >> simp[]
QED

Theorem sb_step_decode:
  s.contexts <> [] /\ sb_decoded (FST (HD s.contexts)) op ==>
  step s = handle (sb_inner op) handle_step s
Proof
  simp[sb_decoded_def] >> strip_tac >>
  Cases_on `FLOOKUP (FST (HD s.contexts)).msgParams.parsed
    (FST (HD s.contexts)).pc` >>
  gvs[step_def, sb_inner_def, bind_def, ignore_bind_def,
      get_current_context_def, return_def, fail_def] >>
  Cases_on `LENGTH (FST (HD s.contexts)).msgParams.code <=
    (FST (HD s.contexts)).pc` >>
  gvs[step_inst_def, bind_def, fail_def, finish_def, handle_def,
      get_current_context_def, return_def, ignore_bind_def,
      set_return_data_def, set_current_context_def]
QED

Theorem sb_exception_resume_shape[local]:
  s.contexts = (c,rb)::(p,prb)::rest /\
  handle_exception e s = (INL (),t) ==>
  ?p' w. t.contexts = (p',prb)::rest /\
    p'.msgParams = p.msgParams /\ p'.jumpDest = p.jumpDest /\
    p'.pc = p.pc + 1 /\ p'.stack = w::p.stack
Proof
  strip_tac >>
  Cases_on `c.msgParams.outputTo` >>
  Cases_on `e = NONE` >> Cases_on `e = SOME Reverted` >>
  gvs[handle_exception_def, bind_def, ignore_bind_def,
      get_gas_left_def, get_current_context_def, return_def,
      consume_gas_def, set_return_data_def, set_current_context_def,
      get_num_contexts_def, get_return_data_def, get_output_to_def,
      reraise_def, assert_def, fail_def, inc_pc_def, push_stack_def,
      write_memory_def, pop_and_incorporate_context_def, pop_context_def,
      set_rollback_def, unuse_gas_def, update_gas_refund_def,
      push_logs_def, AllCaseEqs()]
QED

Theorem sb_suspended_tail[local]:
  sb_at code q d s /\ d < LENGTH s.contexts /\
  LENGTH t.contexts = LENGTH s.contexts /\
  MAP FST (TL t.contexts) = MAP FST (TL s.contexts) ==>
  sb_at code q d t
Proof
  Cases_on `q` >> simp[sb_at_def] >> strip_tac >>
  `0 < LENGTH s.contexts - d` by decide_tac >>
  Cases_on `LENGTH s.contexts - d` >> gvs[] >>
  Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[] >>
  `n < LENGTH t' /\ n < LENGTH t''` by gvs[] >>
  `FST (EL n t') = FST (EL n t'')` by
    metis_tac[EL_MAP] >>
  gvs[]
QED

Theorem sb_exception_resume[local]:
  sb_at code q d s /\ d < LENGTH s.contexts /\
  handle_exception e s = (INL (),t) /\ d <= LENGTH t.contexts ==>
  sb_at code q d t
Proof
  strip_tac >> `0 < d` by (Cases_on `q` >> gvs[sb_at_def]) >>
  Cases_on `s.contexts` >- gvs[] >>
  Cases_on `t'` >- gvs[] >>
  PairCases_on `h` >> PairCases_on `h'` >>
  drule_all sb_exception_resume_shape >> strip_tac >>
  Cases_on `q` >>
  Cases_on `d = SUC (LENGTH t'')`
  >- gvs[sb_at_def, bytecode_stack_describes_def] >>
  `d < SUC (LENGTH t'')` by gvs[] >>
  `SUC (SUC (LENGTH t'')) - d = SUC (SUC (LENGTH t'') - d)` by
    decide_tac >>
  `0 < SUC (LENGTH t'') - d` by decide_tac >>
  Cases_on `SUC (LENGTH t'') - d` >> gvs[sb_at_def]
QED

Theorem sb_handle_resume:
  sb_at code q d s /\ d < LENGTH s.contexts /\
  handle_step e s = (INL (),t) /\ d <= LENGTH t.contexts ==>
  sb_at code q d t
Proof
  strip_tac >>
  `s.contexts <> []` by (Cases_on `s.contexts` >> gvs[]) >>
  qpat_x_assum `handle_step e s = _` mp_tac >>
  simp[handle_step_def] >> IF_CASES_TAC >- simp[reraise_def] >>
  simp[handle_def] >>
  strip_assume_tac (INST_TYPE [alpha |-> ``:unit``] handle_create_INR) >>
  simp[] >> strip_tac >>
  drule_all handle_create_preserves_tl_and_snd_hd >> strip_tac >>
  drule_all handle_create_preserves_length >> strip_tac >>
  `sb_at code q d s'` by
    (irule sb_suspended_tail >> qexists_tac `s` >> simp[]) >>
  irule sb_exception_resume >> metis_tac[]
QED

Theorem sb_suspended_grow[local]:
  sb_at code q d s /\ d < LENGTH s.contexts /\
  LENGTH t.contexts = LENGTH s.contexts + 1 /\
  MAP FST (TL (TL t.contexts)) = MAP FST (TL s.contexts) ==>
  sb_at code q d t
Proof
  Cases_on `q` >> simp[sb_at_def] >> strip_tac >>
  `0 < LENGTH s.contexts - d` by decide_tac >>
  `LENGTH t.contexts - d = SUC (LENGTH s.contexts - d)` by decide_tac >>
  Cases_on `LENGTH s.contexts - d` >> gvs[] >>
  namedCases_on `s.contexts` ["", "hs xs"] >> gvs[] >>
  namedCases_on `t.contexts` ["", "ht ys"] >> gvs[] >>
  namedCases_on `ys` ["", "hp zs"] >> gvs[] >>
  `n < LENGTH xs /\ n < LENGTH zs` by gvs[] >>
  `FST (EL n xs) = FST (EL n zs)` by metis_tac[EL_MAP] >>
  `SUC (LENGTH xs) + 1 - d = SUC (SUC n)` by decide_tac >>
  gvs[]
QED

Theorem sb_inner_deeper[local]:
  wf_state s /\ sb_at code q d s /\ d < LENGTH s.contexts /\
  step_inner s = (r,t) ==> sb_at code q d t /\ d < LENGTH t.contexts
Proof
  strip_tac >> `s.contexts <> []` by (Cases_on `s.contexts` >> gvs[]) >>
  `LENGTH s.contexts <= LENGTH t.contexts` by
    metis_tac[same_frame_or_grow_length, same_frame_or_grow_step_inner_named,
              arithmeticTheory.GREATER_EQ] >>
  reverse conj_tac >- decide_tac >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (`same_frame_rel s t` by
        (irule (INST_TYPE [alpha |-> ``:unit``] same_frame_or_grow_eq_length) >>
         simp[] >>
         qexistsl_tac [`step_inner`, `r`] >> simp[]) >>
      irule sb_suspended_tail >> qexists_tac `s` >>
      gvs[same_frame_rel_def]) >>
  `LENGTH t.contexts > LENGTH s.contexts` by decide_tac >>
  drule_all step_inner_push_structure >> strip_tac >>
  irule sb_suspended_grow >> qexists_tac `s` >> simp[]
QED

Theorem sb_deeper_preserved_thm:
  sb_deeper_preserved
Proof
  rw[sb_deeper_preserved_def] >>
  Cases_on `step_inner s` >> rename1 `step_inner s = (result,mid)` >>
  drule_all sb_inner_deeper >> strip_tac >>
  qpat_x_assum `step s = _` mp_tac >>
  simp[step_eq_handle_step_inner, handle_def] >>
  Cases_on `result` >> simp[] >> strip_tac >- gvs[] >>
  irule sb_handle_resume >> metis_tac[]
QED
