Theory concretizeLayoutPhaseExceptional
Ancestors concretizeLayoutPhaseOrigin concretizeLayoutExceptionalCopy
  concretizeLayoutExceptionalEntry concretizeLayoutBlockPairing concretizeStepStructure
  frameJointTrace frameJointTransition
  frameOriginHistory frameOriginReachable frameResolvedTrace
  venomExecSemantics venomInst list arithmetic concretizeLayoutRankedCorridor

Theorem layout_returncopy_phase_block_abort:
  ptr_discipline lo C vs0 /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz /\
  get_instruction g.lop_origin.lbo_source s.vs_inst_idx = SOME inst /\
  layout_block_pair positions g.lop_origin.lbo_source g.lop_origin.lbo_target
    s.vs_inst_idx t.vs_inst_idx /\
  revert_forward_pair g.lop_origin.lbo_source s.vs_inst_idx j /\
  step_inst_base inst s = OK post /\
  exec_block (SUC fuel) C g.lop_origin.lbo_source s = Abort a final ==>
  ?final'. exec_block (SUC fuel) C' g.lop_origin.lbo_target t = Abort a final' /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q (INL g) (INL g)
      (Abort a final) (Abort a final')
Proof
  strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    metis_tac[layout_ordinary_ready] >>
  qpat_x_assum `layout_ordinary_trace _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_trace_def, layout_ordinary_state_def] >> rpt strip_tac >>
  `joint_config_reachable vs0 C g.lop_config` by
    (drule joint_trace_prefix_reachable >>
     pure_rewrite_tac[EVERY_EL] >>
     disch_then (qspec_then `g.lop_cursor` mp_tac) >> simp[]) >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (gvs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `get_instruction g.lop_origin.lbo_target t.vs_inst_idx = SOME inst` by
    (drule layout_block_pair_lookup >> disch_then drule >>
     simp[concretize_positions_unchanged]) >>
  `layout_block_pair positions g.lop_origin.lbo_source g.lop_origin.lbo_target
    (SUC s.vs_inst_idx) (SUC t.vs_inst_idx)` by
    (drule_all layout_block_pair_advance >>
     simp[concretize_positions_unchanged, ADD1]) >>
  `terminal_corridor g.lop_origin.lbo_source g.lop_origin.lbo_source
    (SUC s.vs_inst_idx) j` by
    (irule layout_revert_forward_corridor >> goal_assum (drule_at Any) >> simp[]) >>
  `ranked_terminal_corridor g.lop_origin.lbo_source g.lop_origin.lbo_target
    (SUC s.vs_inst_idx) (SUC t.vs_inst_idx) (j - SUC s.vs_inst_idx)` by
    (drule_all layout_terminal_corridor_ranked >> simp[]) >>
  `post.vs_inst_idx = s.vs_inst_idx` by
    (irule step_inst_base_preserves_inst_idx >> goal_assum (drule_at Any) >>
     simp[is_terminator_def]) >>
  qpat_x_assum `exec_block _ _ _ _ = Abort _ _` mp_tac >>
  simp[Once exec_block_def, step_inst_non_invoke, is_terminator_def] >> strip_tac >>
  `?tpost final'. step_inst_base inst t = OK tpost /\
    exec_block (SUC fuel) C' g.lop_origin.lbo_target
      (tpost with vs_inst_idx := SUC tpost.vs_inst_idx) = Abort a final' /\
    dead_result_rel D (Abort a final) (Abort a final')` by
    (irule concretize_returncopy_atomic_abort >> simp[] >>
     goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
     simp[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `tpost.vs_inst_idx = t.vs_inst_idx` by
    (irule step_inst_base_preserves_inst_idx >> goal_assum (drule_at Any) >>
     simp[is_terminator_def]) >>
  qexists_tac `final'` >> simp[layout_phase_ok_abort_def] >>
  simp[Once exec_block_def, step_inst_non_invoke, is_terminator_def] >>
  metis_tac[step_inst_base_preserves_inst_idx, is_terminator_def]
QED

val _ = export_theory();
