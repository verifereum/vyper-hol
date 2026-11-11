Theory frameHistoryCfg
Ancestors
  frameExecutionHistory frameCfgBoundary ptrDiscipline contextCodegenRel
  venomInstProps venomWf venomExecSemantics venomState venomInst list rich_list

Definition history_visits_def:
  history_visits [] = [] /\
  history_visits [(i,s)] = [s.vs_current_bb] /\
  history_visits ((i,s)::(j,t)::rest) =
    if is_terminator i.inst_opcode then
      s.vs_current_bb :: history_visits ((j,t)::rest)
    else history_visits ((j,t)::rest)
End

Definition frame_history_cfg_def:
  frame_history_cfg fn h <=>
    h <> [] /\ history_visits h <> [] /\
    is_fn_path fn (history_visits h) /\
    (?entry. fn_entry_label fn = SOME entry /\ HD (history_visits h) = entry) /\
    LAST (history_visits h) = (SND (LAST h)).vs_current_bb
End

Theorem history_visits_self_loop:
  is_terminator i.inst_opcode /\ s.vs_current_bb = t.vs_current_bb ==>
    history_visits [(i,s);(j,t)] = [s.vs_current_bb;s.vs_current_bb]
Proof
  simp[history_visits_def]
QED

Theorem history_visits_same_block:
  ~is_terminator i.inst_opcode /\ s.vs_current_bb = t.vs_current_bb ==>
    history_visits [(i,s);(j,t)] = [s.vs_current_bb]
Proof
  simp[history_visits_def]
QED

Theorem history_visits_snoc:
  !h j t. h <> [] /\
    (is_terminator (FST (LAST h)).inst_opcode \/
     t.vs_current_bb = (SND (LAST h)).vs_current_bb) ==>
    history_visits (h ++ [(j,t)]) =
      if is_terminator (FST (LAST h)).inst_opcode then
        history_visits h ++ [t.vs_current_bb]
      else history_visits h
Proof
  Induct >> simp[] >> qx_gen_tac `obs` >> PairCases_on `obs` >>
  namedCases_on `h` ["", "obs2 rest"]
  >- (simp[history_visits_def] >>
      Cases_on `is_terminator obs0.inst_opcode` >> simp[])
  >> PairCases_on `obs2` >>
  rpt strip_tac >> gvs[history_visits_def] >>
  Cases_on `is_terminator obs0.inst_opcode` >> gvs[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem frame_history_cfg_singleton:
  fn_entry_label fn = SOME s.vs_current_bb ==>
  frame_history_cfg fn [(i,s)]
Proof
  simp[frame_history_cfg_def, history_visits_def, is_fn_path_def]
QED

Theorem frame_history_cfg_snoc:
  frame_history_cfg fn h /\ LAST h = (i,s) /\
  (if is_terminator i.inst_opcode then
     fn_cfg_edge fn s.vs_current_bb t.vs_current_bb
   else t.vs_current_bb = s.vs_current_bb) ==>
  frame_history_cfg fn (h ++ [(j,t)])
Proof
  rpt strip_tac >>
  `h <> []` by gvs[frame_history_cfg_def] >>
  Cases_on `is_terminator i.inst_opcode`
  >- (drule history_visits_snoc >> simp[] >> strip_tac >>
      gvs[frame_history_cfg_def] >>
      simp[LAST_APPEND] >> conj_tac
      >- (irule venomExecProofsTheory.is_fn_path_snoc >> simp[]) >>
      Cases_on `history_visits h` >> gvs[]) >>
  drule history_visits_snoc >> simp[] >> strip_tac >>
  gvs[frame_history_cfg_def, LAST_APPEND]
QED

Theorem bind_outputs_current_bb[local]:
  bind_outputs outs vals s = SOME s' ==> s'.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >> irule venomInstProofs1Theory.bind_outputs_preserves >>
  simp[update_var_def] >> metis_tac[]
QED

Theorem return_binding_current_bb:
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller callee)) = SOME s' ==>
  s'.vs_current_bb = caller.vs_current_bb
Proof
  strip_tac >> drule bind_outputs_current_bb >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem setup_enters_block_entry:
  setup_callee fn args s = SOME cs /\ enters_block fn cs s1 ==>
    fn_entry_label fn = SOME s1.vs_current_bb
Proof
  rpt strip_tac >> drule enters_block_control_labels >>
  gvs[setup_callee_def, fn_entry_label_def, entry_block_def, AllCaseEqs()]
QED

Theorem frame_history_cfg_invariant:
  !vs0 ctx stk PG G tn fn inst s hs h.
    frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
    EVERY wf_function ctx.ctx_functions ==>
    MEM fn ctx.ctx_functions /\ frame_history_cfg fn h /\
    h <> [] /\ LAST h = (inst,s) /\
    LIST_REL (\f h0. MEM f.cf_fn ctx.ctx_functions /\
      f.cf_inst.inst_opcode = INVOKE /\ frame_history_cfg f.cf_fn h0 /\
      h0 <> [] /\ LAST h0 = (f.cf_inst,f.cf_state)) stk hs
Proof
  ho_match_mp_tac frame_history_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  disch_tac
  >- (drule lookup_function_MEM >> strip_tac >>
      drule enters_block_control_labels >> simp[] >> strip_tac >>
      simp[] >> irule frame_history_cfg_singleton >> gvs[])
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume frame_history_cfg_invariant[next]:
  gvs[LAST_APPEND] >>
  drule_all step_preserves_control_flow >> strip_tac >>
  irule frame_history_cfg_snoc >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume frame_history_cfg_invariant[block]:
  gvs[LAST_APPEND] >>
  `wf_function fn` by metis_tac[EVERY_MEM] >>
  drule_all active_terminator_cfg_transition >> strip_tac >>
  irule frame_history_cfg_snoc >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume frame_history_cfg_invariant[call]:
  gvs[] >> drule lookup_function_MEM >> strip_tac >>
  drule_all setup_enters_block_entry >> strip_tac >>
  simp[] >> irule frame_history_cfg_singleton >> simp[]
QED

Resume frame_history_cfg_invariant[ret]:
  gvs[LAST_APPEND] >>
  drule return_binding_current_bb >> strip_tac >>
  irule frame_history_cfg_snoc >>
  goal_assum (drule_at Any) >> simp[is_terminator_def]
QED

Finalise frame_history_cfg_invariant

Theorem frame_history_current_cfg:
  EVERY wf_function ctx.ctx_functions /\
  frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
    frame_history_cfg fn h
Proof
  metis_tac[frame_history_cfg_invariant]
QED

Theorem frame_history_saved_cfg:
  EVERY wf_function ctx.ctx_functions /\
  frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
    LIST_REL (\f h0. frame_history_cfg f.cf_fn h0) stk hs
Proof
  rpt strip_tac >> drule frame_history_cfg_invariant >> simp[] >>
  strip_tac >> irule LIST_REL_mono >> goal_assum (drule_at Any) >> simp[]
QED

Theorem frame_history_saved_cfg_at:
  EVERY wf_function ctx.ctx_functions /\
  frame_history vs0 ctx stk PG G tn fn inst s hs h /\ n < LENGTH stk ==>
    frame_history_cfg (EL n stk).cf_fn (EL n hs)
Proof
  rpt strip_tac >> drule_all frame_history_saved_cfg >>
  simp[LIST_REL_EL_EQN]
QED

Theorem frame_reachable_cfg_histories:
  EVERY wf_function ctx.ctx_functions /\
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  ?hs h. frame_history vs0 ctx stk PG G tn fn inst s hs h /\
    frame_history_cfg fn h /\
    LIST_REL (\f h0. frame_history_cfg f.cf_fn h0) stk hs
Proof
  rpt strip_tac >> drule frame_reachable_has_history >> strip_tac >>
  goal_assum (drule_at Any) >>
  metis_tac[frame_history_current_cfg, frame_history_saved_cfg]
QED
