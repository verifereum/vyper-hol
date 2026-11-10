Theory concretizeLayoutRunEntry
Ancestors concretizeLayoutRunState concretizeLayoutScopedEntry
  concretizeLayoutPhaseOrigin concretizeLayoutScopedPhase
  venomExecSemantics venomState contextCodegenRel concretizeLayoutBlockEntry
  venomWf list venomInst venomExecProofs

Theorem layout_scoped_enters_entry:
  enters_block fn s p /\ enters_block fn' t p' /\ ~a.lop_pending /\
  layout_ordinary_trace vs0 C q0 es qs q a p /\
  layout_ordinary_state D lo C' q0 es qs a p p' ==>
  ?bb bb' phi phi' b.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    eval_phis s bb.bb_instructions = OK phi /\
    eval_phis t bb'.bb_instructions = OK phi' /\
    p = (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
    p' = (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) /\
    b = (a with lop_origin :=
      <|lbo_source := bb; lbo_target := bb'; lbo_entry := p|>) /\
    layout_ordinary_entry D lo vs0 C C' q0 es qs q b p p' /\
    layout_scoped_phi_link g (INL b) fn fn' s t bb bb' phi phi'
Proof
  simp[enters_block_def] >> strip_tac >>
  drule_all layout_scoped_install_origin >> strip_tac >>
  metis_tac[]
QED

Theorem layout_scoped_initial_enters_entry:
  enters_block fn s p /\ EVERY bb_well_formed fn.fn_blocks /\
  joint_trace vs0 C q0 es qs q /\
  q0 = JointConfig [] [] FEMPTY entry_taint fn inst p [] FEMPTY hs h /\
  p.vs_allocas = FEMPTY ==>
  ?bb bb' phi phi' b.
    enters_block (concretize_function_with_positions positions fn) s p /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block s.vs_current_bb
      (concretize_function_with_positions positions fn).fn_blocks = SOME bb' /\
    eval_phis s bb.bb_instructions = OK phi /\
    eval_phis s bb'.bb_instructions = OK phi' /\
    p = (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
    p = (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) /\
    b.lop_cursor = 0 /\ b.lop_bound = 0 /\ b.lop_config = q0 /\
    b.lop_ids = [0] /\ b.lop_anns = [([],FEMPTY)] /\
    b.lop_target_taint = entry_taint /\
    layout_ordinary_entry D lo vs0 C C' q0 es qs q b p p /\
    layout_scoped_phi_link g (INL b) fn
      (concretize_function_with_positions positions fn) s s bb bb' phi phi'
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    gvs[enters_block_def] >>
  `MEM bb fn.fn_blocks` by (fs[lookup_block_def] >> metis_tac[FIND_MEM]) >>
  `bb_well_formed bb` by fs[EVERY_MEM] >>
  drule_all concretize_enters_block_exact >>
  disch_then (qspec_then `positions` assume_tac) >>
  drule_all layout_run_initial_state >>
  disch_then (qspecl_then [`ARB`, `lo`, `D`, `C'`] strip_assume_tac) >>
  drule_all (Q.INST [`fn'` |-> `concretize_function_with_positions positions fn`]
    layout_scoped_enters_entry) >>
  disch_then (qspec_then `g` strip_assume_tac) >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

val _ = export_theory();
