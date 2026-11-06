Theory concretizeLayoutPhaseIstore
Ancestors concretizeLayoutPhaseStorage concretizeLayoutLocalIstore
  frameRelocationTaintOrder frameJointTrace frameOriginHistory
  frameOriginReachable o1PassContract concretizeLayoutPhaseOrigin
  concretizeLayoutPhaseSuccess frameJointTransition frameOriginUpdates
  venomExecSemantics venomState venomInst memSafeRun

Theorem layout_istore_trace_step:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  ~ctx_has_dalloca C /\ fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  ~joint_read_exempt (EL g.lop_cursor (q0::qs)) /\
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [opd;opv] /\
  inst.inst_outputs = [] /\ o1_fn_shape C fn /\ MEM inst (fn_insts fn) /\
  get_instruction g.lop_origin.lbo_source s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = OK post ==>
  ?k tpost. step_inst_base inst t = OK tpost /\ k.lop_pending /\
    k.lop_cursor = SUC g.lop_cursor /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q
      (INL g) (INL k) (OK post) (OK tpost)
Proof
  strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    fs[layout_ordinary_entry_def] >>
  `joint_trace vs0 C q0 es qs q /\
   EL g.lop_cursor (q0::qs) = g.lop_config /\
   resolved_config_ok g.lop_config g.lop_ids g.lop_anns` by
    fs[layout_ordinary_trace_def] >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_state_def] >> strip_tac >> gvs[] >> fs[ETA_AX] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (drule_all joint_trace_edge_at >> strip_tac >>
     gvs[] >> fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `op_taint g.lop_target_taint opv SUBSET {k:num | k < 32}` by
    (irule relocation_reachable_operand_taint_bounded >> metis_tac[]) >>
  `?dst value. eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value` by
    (gvs[step_inst_base_def, exec_write2_def, eval_operands_def, AllCaseEqs()]) >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`)
    (REWRITE_RULE[ETA_AX] concretize_istore_local_complete) >>
  disch_then (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `resolved_config_ok _ _ _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  disch_then (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `callee_first _ _`)) >>
  disch_then (drule_at (Pat `concretize_supplement _ _ _ _`)) >>
  simp[] >> strip_tac >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> DALLOCA /\
   ~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `post.vs_inst_idx = s.vs_inst_idx` by metis_tac[step_inst_base_preserves_inst_idx] >>
  `step_inst fuel C inst s = OK post /\ step_inst fuel C' inst t = OK tpost` by
    simp[step_inst_non_invoke] >>
  `post.vs_code = tpost.vs_code /\ post.vs_data_section = tpost.vs_data_section` by
    metis_tac[step_inst_ok_code_data] >>
  drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
    layout_ordinary_success_phase >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  simp[origin_set_def, finite_mapTheory.DRESTRICT_UNIV, ETA_AX] >>
  disch_then (qspec_then `tpost` mp_tac) >> gvs[] >>
  metis_tac[ctxLookupAgreeHelpersTheory.step_inst_base_initial_fmp]
QED
