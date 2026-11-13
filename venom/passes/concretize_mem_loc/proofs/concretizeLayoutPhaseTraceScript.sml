Theory concretizeLayoutPhaseTrace
Ancestors concretizeLayoutPhaseOrigin frameJointTrace frameResolvedTrace
  frameActivationLifetime frameJointTransition frameOriginCache frameOriginUpdates
  frameResolvedCoherent list

Theorem layout_ordinary_trace_advance:
  layout_ordinary_trace vs0 C q0 es qs q g s /\ ~g.lop_pending /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  inst.inst_opcode <> DALLOCA /\ g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) ==>
  ?k. k.lop_origin = g.lop_origin /\ k.lop_pending /\
    k.lop_cursor = SUC g.lop_cursor /\ k.lop_bound = SUC g.lop_bound /\
    k.lop_ids = g.lop_ids /\ k.lop_target_taint = g.lop_target_taint /\
    k.lop_config = EL (SUC g.lop_cursor) (q0::qs) /\
    layout_ordinary_trace vs0 C q0 es qs q k post
Proof
  strip_tac >>
  qpat_x_assum `layout_ordinary_trace _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_trace_def] >> strip_tac >>
  drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  `?anns'. resolved_config_ok (EL (SUC g.lop_cursor) (q0::qs)) g.lop_ids anns'` by
    (irule resolved_config_ordinary >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `lifetime_ok (SUC g.lop_bound) g.lop_ids (EL (SUC g.lop_cursor) (q0::qs))` by
    (drule_all lifetime_transition >> simp[lifetime_step_def]) >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_trace_def, joint_chain_length] >>
  qexists_tac `g with <| lop_pending := T; lop_cursor := SUC g.lop_cursor;
    lop_bound := SUC g.lop_bound; lop_anns := anns';
    lop_config := EL (SUC g.lop_cursor) (q0::qs) |>` >>
  gvs[layout_ordinary_trace_def]
QED

Theorem layout_no_output_resolved_ordinary:
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h)
    (SOME (OriginOrdinary fuel post)) q' /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h) ids anns /\
  inst.inst_opcode <> DALLOCA /\ inst.inst_outputs = [] ==>
  resolved_config_ok q' ids anns
Proof
  simp[joint_transition_ordinary] >> rpt strip_tac >> gvs[] >>
  gvs[resolved_config_ok_def] >>
  `resolved_frame_ok birth post.vs_allocas PG G om (FST ann) (SND ann)
    (birth::births)
    ((fn,post.vs_allocas)::MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk)` by
    (irule resolved_frame_cache_transport >> goal_assum (drule_at Any) >>
     metis_tac[step_inst_cache_preserved]) >>
  drule resolved_frame_step >> disch_then (qspec_then `inst` mp_tac) >>
  simp[origin_set_def, finite_mapTheory.DRESTRICT_UNIV]
QED

Theorem layout_no_output_trace_advance:
  layout_ordinary_trace vs0 C q0 es qs q g s /\ ~g.lop_pending /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  inst.inst_opcode <> DALLOCA /\ inst.inst_outputs = [] /\
  g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  post.vs_inst_idx = s.vs_inst_idx ==>
  ?k next hs' h'. k.lop_origin = g.lop_origin /\ k.lop_pending /\
    k.lop_cursor = SUC g.lop_cursor /\ k.lop_bound = SUC g.lop_bound /\
    k.lop_ids = g.lop_ids /\ k.lop_anns = g.lop_anns /\
    k.lop_target_taint = g.lop_target_taint /\
    k.lop_config = JointConfig stk PG G (step_taint inst s post tn) fn next
      (layout_phase_normalize T post) oms om hs' h' /\
    layout_ordinary_trace vs0 C q0 es qs q k post
Proof
  strip_tac >>
  qpat_x_assum `layout_ordinary_trace _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_trace_def] >> strip_tac >>
  drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  `resolved_config_ok (EL (SUC g.lop_cursor) (q0::qs)) g.lop_ids g.lop_anns` by
    (irule layout_no_output_resolved_ordinary >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `lifetime_ok (SUC g.lop_bound) g.lop_ids (EL (SUC g.lop_cursor) (q0::qs))` by
    (drule_all lifetime_transition >> simp[lifetime_step_def]) >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_trace_def, joint_chain_length] >>
  qexists_tac `g with <| lop_pending := T; lop_cursor := SUC g.lop_cursor;
    lop_bound := SUC g.lop_bound;
    lop_config := EL (SUC g.lop_cursor) (q0::qs) |>` >>
  gvs[layout_ordinary_trace_def] >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[joint_transition_ordinary] >> strip_tac >> gvs[] >>
  simp[ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.set_prov_def,
    origin_step_def, origin_set_def, finite_mapTheory.DRESTRICT_UNIV,
    layout_phase_normalize_def] >> metis_tac[]
QED

Theorem layout_returncopy_trace_step:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  ~ctx_has_dalloca C /\ fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  g.lop_cursor < LENGTH es /\ EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  ~joint_read_exempt (EL g.lop_cursor (q0::qs)) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz /\
  get_instruction g.lop_origin.lbo_source s.vs_inst_idx = SOME inst /\
  step_inst fuel C inst s = OK post /\ post.vs_inst_idx = s.vs_inst_idx ==>
  ?k tpost. step_inst_base inst t = OK tpost /\
    k.lop_pending /\ k.lop_cursor = SUC g.lop_cursor /\
    k.lop_origin = g.lop_origin /\ k.lop_ids = g.lop_ids /\
    k.lop_config = EL (SUC g.lop_cursor) (q0::qs) /\
    resolved_annotation_update g.lop_config (EL g.lop_cursor es)
      g.lop_ids g.lop_anns k.lop_anns /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q (INL g) (INL k)
      (OK post) (OK tpost)
Proof
  strip_tac >>
  `inst_wf inst` by
    (gvs[o1PassContractTheory.o1_fn_shape_def, venomWfTheory.fn_inst_wf_def,
      venomInstTheory.fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[]) >>
  `inst.inst_outputs = []` by gvs[venomWfTheory.inst_wf_def] >>
  `layout_ordinary_trace vs0 C q0 es qs q g s` by
    metis_tac[layout_ordinary_ready] >>
  `inst.inst_opcode <> DALLOCA` by simp[] >>
  drule_all layout_no_output_trace_advance >> strip_tac >>
  drule_all layout_returncopy_pending_adapter >> strip_tac >>
  qexistsl_tac [`k with lop_target_taint := step_taint inst t tpost g.lop_target_taint`,
    `tpost`] >> simp[] >>
  conj_tac >- gvs[layout_ordinary_trace_def] >>
  simp[Once resolved_annotation_update_cases, origin_set_def,
    finite_mapTheory.DRESTRICT_UNIV]
QED

val _ = export_theory();
