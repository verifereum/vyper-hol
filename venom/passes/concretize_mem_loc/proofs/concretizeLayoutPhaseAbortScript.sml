Theory concretizeLayoutPhaseAbort
Ancestors concretizeLayoutScopedPhase concretizeLayoutLocalTerminals
  concretizeLayoutLocalAssertions concretizeLayoutLocalSelfdestruct
  concretizeLayoutLocalReturnCopy concretizeLayoutPhaseOrigin
  frameRelocationLocal frameRelocationEnvironment list
  frameJointTrace frameJointTransition frameOriginHistory frameOriginReachable
  ptrDiscipline

Theorem layout_scoped_abort_embedding:
  dead_result_rel D (Abort a s) (Abort b t) ==>
  layout_scoped_outcome D Ret Entry g h (Abort a s) (Abort b t)
Proof
  simp[layout_scoped_outcome_def, layout_scoped_run_outcome_def]
QED

Theorem layout_simple_abort_step:
  layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  MEM inst.inst_opcode [INVALID; REVERT; SSTORE; TSTORE; LOG] /\
  step_inst_base inst s = Abort a post ==>
  ?tpost. step_inst_base inst t = Abort a tpost /\
    dead_result_rel D (Abort a post) (Abort a tpost) /\
    layout_scoped_outcome D Ret Entry (INL g) (INL g)
      (Abort a post) (Abort a tpost)
Proof
  strip_tac >>
  `variable_domains s t /\ s.vs_labels = t.vs_labels /\
   s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static` by
    (Cases_on `g.lop_config` >>
     fs[layout_ordinary_entry_def, layout_ordinary_state_def,
        relocation_env_def] >> metis_tac[local_rel_domains]) >>
  `?tpost. step_inst_base inst t = Abort a tpost /\
    dead_result_rel D (Abort a post) (Abort a tpost)` by
    (gvs[MEM] >> metis_tac[concretize_invalid_complete,
      concretize_revert_complete, concretize_static_write_abort_complete, MEM]) >>
  metis_tac[layout_scoped_abort_embedding]
QED

Theorem layout_guard_abort_step:
  ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE; SELFDESTRUCT] /\
  step_inst_base inst s = Abort a post ==>
  ?tpost. step_inst_base inst t = Abort a tpost /\
    dead_result_rel D (Abort a post) (Abort a tpost) /\
    layout_scoped_outcome D Ret Entry (INL g) (INL g)
      (Abort a post) (Abort a tpost)
Proof
  strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    fs[layout_ordinary_entry_def] >>
  `joint_config_reachable vs0 C g.lop_config` by
    (fs[layout_ordinary_trace_def] >>
     drule joint_trace_prefix_reachable >> pure_rewrite_tac[EVERY_EL] >>
     disch_then (qspec_then `g.lop_cursor` mp_tac) >> simp[]) >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (gvs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `resolved_config_ok g.lop_config g.lop_ids g.lop_anns` by
    fs[layout_ordinary_trace_def] >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_state_def] >> strip_tac >> gvs[] >> fs[ETA_AX] >>
  `?tpost. step_inst_base inst t = Abort a tpost /\
    dead_result_rel D (Abort a post) (Abort a tpost)` by
    (gvs[MEM] >> metis_tac[concretize_assert_abort_complete,
      concretize_selfdestruct_abort_complete, MEM]) >>
  metis_tac[layout_scoped_abort_embedding]
QED

Theorem layout_returncopy_abort_step:
  ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz /\ step_inst_base inst s = Abort a post ==>
  ?tpost. step_inst_base inst t = Abort a tpost /\
    dead_result_rel D (Abort a post) (Abort a tpost) /\
    layout_scoped_outcome D Ret Entry (INL g) (INL g)
      (Abort a post) (Abort a tpost)
Proof
  strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    fs[layout_ordinary_entry_def] >>
  `joint_config_reachable vs0 C g.lop_config` by
    (fs[layout_ordinary_trace_def] >>
     drule joint_trace_prefix_reachable >> pure_rewrite_tac[EVERY_EL] >>
     disch_then (qspec_then `g.lop_cursor` mp_tac) >> simp[]) >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (gvs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `resolved_config_ok g.lop_config g.lop_ids g.lop_anns` by
    fs[layout_ordinary_trace_def] >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_state_def] >> strip_tac >> gvs[] >> fs[ETA_AX] >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`)
    concretize_returncopy_bounds_abort_complete >>
  disch_then (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `resolved_config_ok _ _ _`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok _ _`)) >> simp[] >> strip_tac >>
  metis_tac[layout_scoped_abort_embedding]
QED

val _ = export_theory();
