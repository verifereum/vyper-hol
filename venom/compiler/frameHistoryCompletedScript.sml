Theory frameHistoryCompleted
Ancestors
  frameHistoryInstructions frameHistoryCfg frameExecutionHistory
  frameCfgBoundary contextCodegenRel venomInstProps venomExecProofs
  venomWf venomExecSemantics venomState venomInst list rich_list

Definition history_completed_blocks_def:
  history_completed_blocks fn h <=>
    !bb j. MEM bb fn.fn_blocks /\
      MEM bb.bb_label (FRONT (history_visits h)) /\
      phi_prefix_length bb.bb_instructions <= j /\
      j < LENGTH bb.bb_instructions ==>
      ?old_inst old_s. MEM (old_inst,old_s) (FRONT h) /\
        old_s.vs_current_bb = bb.bb_label /\ old_s.vs_inst_idx = j /\
        active_inst fn old_inst old_s /\
        old_inst = EL j bb.bb_instructions
End

Theorem history_completed_blocks_singleton:
  history_completed_blocks fn [(i,s)]
Proof
  simp[history_completed_blocks_def, history_visits_def]
QED

Theorem history_completed_blocks_same_visits:
  history_completed_blocks fn h /\ h <> [] /\
  history_visits (h ++ [(i,t)]) = history_visits h ==>
    history_completed_blocks fn (h ++ [(i,t)])
Proof
  simp[history_completed_blocks_def, FRONT_APPEND] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[APPEND_FRONT_LAST, MEM_APPEND]
QED

Theorem history_completed_blocks_terminator:
  wf_function fn /\ history_completed_blocks fn h /\
  history_instruction_prefix fn h /\ frame_history_cfg fn h /\
  h <> [] /\ LAST h = (i,s) /\
  active_inst fn i s /\ is_terminator i.inst_opcode ==>
    history_completed_blocks fn (h ++ [(i',t)])
Proof
  rpt strip_tac >> drule history_visits_snoc >> simp[] >> strip_tac >>
  simp[history_completed_blocks_def, FRONT_APPEND] >>
  rpt strip_tac >>
  Cases_on `MEM bb.bb_label (FRONT (history_visits h))`
  >- (gvs[history_completed_blocks_def] >> first_x_assum drule_all >>
      strip_tac >> qexists_tac `old_s` >> simp[] >>
      metis_tac[APPEND_FRONT_LAST, MEM_APPEND]) >>
  `bb.bb_label = s.vs_current_bb` by
    (gvs[frame_history_cfg_def] >> metis_tac[APPEND_FRONT_LAST, MEM_APPEND, MEM]) >>
  `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions) /\
   i = EL s.vs_inst_idx bb.bb_instructions` by
    (gvs[active_inst_def] >>
     `bb = bb'` by metis_tac[same_label_same_block] >> gvs[] >>
     metis_tac[wf_function_bb_well_formed, bb_well_formed_def]) >>
  Cases_on `j = s.vs_inst_idx`
  >- (qexists_tac `s` >> gvs[] >> metis_tac[MEM_LAST_NOT_NIL]) >>
  `j < s.vs_inst_idx` by decide_tac >>
  gvs[history_instruction_prefix_def] >> first_x_assum drule_all >>
  strip_tac >> qexists_tac `old_s` >> simp[] >>
  metis_tac[APPEND_FRONT_LAST, MEM_APPEND]
QED

Theorem frame_history_completed_invariant:
  !vs0 ctx stk PG G tn fn inst s hs h.
    frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
    EVERY wf_function ctx.ctx_functions ==>
    history_completed_blocks fn h /\
    LIST_REL (\f h0. history_completed_blocks f.cf_fn h0) stk hs
Proof
  ho_match_mp_tac frame_history_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> disch_tac
  >- simp[history_completed_blocks_singleton]
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume frame_history_completed_invariant[next]:
  gvs[] >> irule history_completed_blocks_same_visits >>
  goal_assum (drule_at Any) >>
  drule frame_history_current_endpoint >> strip_tac >>
  drule_all step_preserves_control_flow >> strip_tac >>
  drule history_visits_snoc >> simp[]
QED

Resume frame_history_completed_invariant[block]:
  gvs[] >>
  drule frame_history_cfg_invariant >> simp[] >> strip_tac >>
  drule_all frame_history_current_instruction_prefix >> strip_tac >>
  irule history_completed_blocks_terminator >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[EVERY_MEM]
QED

Resume frame_history_completed_invariant[call]:
  gvs[history_completed_blocks_singleton]
QED

Resume frame_history_completed_invariant[ret]:
  gvs[] >>
  drule frame_history_cfg_invariant >> simp[] >> strip_tac >> gvs[] >>
  irule history_completed_blocks_same_visits >>
  goal_assum (drule_at Any) >>
  drule return_binding_current_bb >> strip_tac >>
  drule history_visits_snoc >> simp[is_terminator_def]
QED

Finalise frame_history_completed_invariant

Theorem frame_history_current_completed:
  EVERY wf_function ctx.ctx_functions /\
  frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
    history_completed_blocks fn h
Proof
  metis_tac[frame_history_completed_invariant]
QED

Theorem frame_history_saved_completed:
  EVERY wf_function ctx.ctx_functions /\
  frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
    LIST_REL (\f h0. history_completed_blocks f.cf_fn h0) stk hs
Proof
  metis_tac[frame_history_completed_invariant]
QED

Theorem frame_history_saved_completed_at:
  EVERY wf_function ctx.ctx_functions /\
  frame_history vs0 ctx stk PG G tn fn inst s hs h /\ n < LENGTH stk ==>
    history_completed_blocks (EL n stk).cf_fn (EL n hs)
Proof
  rpt strip_tac >> drule_all frame_history_saved_completed >>
  simp[LIST_REL_EL_EQN]
QED

Theorem frame_reachable_observation_histories:
  EVERY wf_function ctx.ctx_functions /\
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  ?hs h. frame_history vs0 ctx stk PG G tn fn inst s hs h /\
    frame_history_cfg fn h /\ history_instruction_prefix fn h /\
    history_completed_blocks fn h /\
    LIST_REL (\f h0. frame_history_cfg f.cf_fn h0 /\
      history_instruction_prefix f.cf_fn h0 /\
      history_completed_blocks f.cf_fn h0) stk hs
Proof
  rpt strip_tac >> drule frame_reachable_has_history >> strip_tac >>
  drule_all frame_history_current_cfg >> strip_tac >>
  drule_all frame_history_current_instruction_prefix >> strip_tac >>
  drule_all frame_history_current_completed >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  drule_all frame_history_saved_cfg >> strip_tac >>
  drule_all frame_history_saved_instruction_prefix >> strip_tac >>
  drule_all frame_history_saved_completed >> strip_tac >>
  gvs[LIST_REL_EL_EQN] >> qexists_tac `hs` >> simp[]
QED
