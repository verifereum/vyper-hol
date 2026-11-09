Theory frameHistoryInstructions
Ancestors
  frameHistoryCfg frameExecutionHistory frameCfgBoundary contextCodegenRel
  venomInstProps venomExecProofs venomWf venomExecSemantics venomState venomInst list rich_list

Definition history_instruction_prefix_def:
  history_instruction_prefix fn h <=>
    !inst s bb j. h <> [] /\ LAST h = (inst,s) /\
      MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
      phi_prefix_length bb.bb_instructions <= j /\ j < s.vs_inst_idx ==>
      ?old_inst old_s. MEM (old_inst,old_s) (FRONT h) /\
        old_s.vs_current_bb = bb.bb_label /\ old_s.vs_inst_idx = j /\
        active_inst fn old_inst old_s /\
        old_inst = EL j bb.bb_instructions
End

Theorem enters_block_entry_index:
  enters_block fn s s1 ==>
    ?bb. MEM bb fn.fn_blocks /\ bb.bb_label = s1.vs_current_bb /\
      s1.vs_inst_idx = phi_prefix_length bb.bb_instructions
Proof
  strip_tac >> drule enters_block_control_labels >> strip_tac >>
  gvs[enters_block_def] >>
  drule lookup_block_MEM >> drule lookup_block_label >>
  rpt strip_tac >> goal_assum (drule_at Any) >> simp[]
QED

Theorem history_instruction_prefix_entry:
  wf_function fn /\ enters_block fn s t /\ h <> [] /\ LAST h = (i,t) ==>
    history_instruction_prefix fn h
Proof
  rpt strip_tac >> drule enters_block_entry_index >> strip_tac >>
  simp[history_instruction_prefix_def, LAST_APPEND] >> rpt strip_tac >>
  `bb = bb'` by metis_tac[same_label_same_block] >> gvs[]
QED

Theorem history_instruction_prefix_snoc:
  wf_function fn /\ history_instruction_prefix fn h /\ h <> [] /\
  LAST h = (i,s) /\ active_inst fn i s /\
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = SUC s.vs_inst_idx ==>
    history_instruction_prefix fn (h ++ [(i',t)])
Proof
  rpt strip_tac >>
  simp[history_instruction_prefix_def, LAST_APPEND, FRONT_APPEND] >>
  rpt strip_tac >> Cases_on `j = s.vs_inst_idx`
  >- (qexists_tac `s` >> gvs[active_inst_def] >>
      `bb = bb'` by metis_tac[same_label_same_block] >>
      gvs[] >> metis_tac[MEM_LAST_NOT_NIL]) >>
  `j < s.vs_inst_idx` by decide_tac >>
  gvs[history_instruction_prefix_def] >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `old_s` >> simp[] >>
  metis_tac[APPEND_FRONT_LAST, MEM_APPEND]
QED

Theorem frame_history_instruction_prefix_invariant:
  !vs0 ctx stk PG G tn fn inst s hs h.
    frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
    EVERY wf_function ctx.ctx_functions ==>
    MEM fn ctx.ctx_functions /\ history_instruction_prefix fn h /\
    h <> [] /\ LAST h = (inst,s) /\
    LIST_REL (\f h0. MEM f.cf_fn ctx.ctx_functions /\
      active_inst f.cf_fn f.cf_inst f.cf_state /\
      history_instruction_prefix f.cf_fn h0 /\
      h0 <> [] /\ LAST h0 = (f.cf_inst,f.cf_state)) stk hs
Proof
  ho_match_mp_tac frame_history_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> disch_tac
  >- (drule lookup_function_MEM >> strip_tac >> simp[] >>
      irule history_instruction_prefix_entry >>
      simp[] >> metis_tac[EVERY_MEM])
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume frame_history_instruction_prefix_invariant[next]:
  gvs[LAST_APPEND] >>
  drule_all step_preserves_control_flow >> strip_tac >>
  irule history_instruction_prefix_snoc >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[EVERY_MEM]
QED

Resume frame_history_instruction_prefix_invariant[block]:
  gvs[LAST_APPEND] >> irule history_instruction_prefix_entry >>
  simp[LAST_APPEND] >> metis_tac[EVERY_MEM]
QED

Resume frame_history_instruction_prefix_invariant[call]:
  gvs[] >> drule lookup_function_MEM >> strip_tac >> simp[] >>
  irule history_instruction_prefix_entry >>
  simp[] >> metis_tac[EVERY_MEM]
QED

Resume frame_history_instruction_prefix_invariant[ret]:
  gvs[LAST_APPEND] >>
  drule return_binding_current_bb >> strip_tac >>
  irule history_instruction_prefix_snoc >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[EVERY_MEM]
QED

Finalise frame_history_instruction_prefix_invariant

Theorem frame_history_current_instruction_prefix:
  EVERY wf_function ctx.ctx_functions /\
  frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
    history_instruction_prefix fn h
Proof
  metis_tac[frame_history_instruction_prefix_invariant]
QED

Theorem frame_history_saved_instruction_prefix:
  EVERY wf_function ctx.ctx_functions /\
  frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
    LIST_REL (\f h0. history_instruction_prefix f.cf_fn h0) stk hs
Proof
  rpt strip_tac >> drule frame_history_instruction_prefix_invariant >> simp[] >>
  strip_tac >> irule LIST_REL_mono >> goal_assum (drule_at Any) >> simp[]
QED

Theorem frame_history_saved_instruction_prefix_at:
  EVERY wf_function ctx.ctx_functions /\
  frame_history vs0 ctx stk PG G tn fn inst s hs h /\ n < LENGTH stk ==>
    history_instruction_prefix (EL n stk).cf_fn (EL n hs)
Proof
  rpt strip_tac >> drule_all frame_history_saved_instruction_prefix >>
  simp[LIST_REL_EL_EQN]
QED

Theorem frame_reachable_instruction_histories:
  EVERY wf_function ctx.ctx_functions /\
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  ?hs h. frame_history vs0 ctx stk PG G tn fn inst s hs h /\
    history_instruction_prefix fn h /\
    LIST_REL (\f h0. history_instruction_prefix f.cf_fn h0) stk hs
Proof
  rpt strip_tac >> drule frame_reachable_has_history >> strip_tac >>
  goal_assum (drule_at Any) >>
  metis_tac[frame_history_current_instruction_prefix,
            frame_history_saved_instruction_prefix]
QED
