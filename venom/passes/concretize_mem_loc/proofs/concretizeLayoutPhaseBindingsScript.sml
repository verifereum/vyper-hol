Theory concretizeLayoutPhaseBindings
Ancestors concretizeLayoutPhaseTrace concretizeLayoutPhaseOrigin
  frameResolvedTrace frameJointTransition frameJointTrace frameActivationLifetime
  frameOriginCache frameOriginUpdates ptrDiscipline list

Theorem layout_bound_resolved_ordinary:
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h)
    (SOME (OriginOrdinary fuel post)) q' /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\ inst.inst_opcode <> DALLOCA ==>
  resolved_config_ok q' (birth::ids)
    ((rp, origin_set rv inst.inst_outputs
      (resolved_out birth post.vs_allocas rp (origin_out PG om inst post)))::anns)
Proof
  simp[joint_transition_ordinary] >> rpt strip_tac >> gvs[] >>
  gvs[resolved_config_ok_def] >>
  `resolved_frame_ok birth post.vs_allocas PG G om rp rv
    (birth::ids)
    ((fn,post.vs_allocas)::MAP (\f. (f.cf_fn,f.cf_state.vs_allocas)) stk)` by
    (irule resolved_frame_cache_transport >> goal_assum (drule_at Any) >>
     metis_tac[step_inst_cache_preserved]) >>
  metis_tac[resolved_frame_step]
QED

Theorem layout_ordinary_bound_trace_advance:
  layout_ordinary_trace vs0 C q0 es qs q g s /\ ~g.lop_pending /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  inst.inst_opcode <> DALLOCA /\ g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  post.vs_inst_idx = s.vs_inst_idx ==>
  ?k next hs' h'. k.lop_origin = g.lop_origin /\ k.lop_pending /\
    k.lop_cursor = SUC g.lop_cursor /\ k.lop_bound = SUC g.lop_bound /\
    k.lop_ids = g.lop_ids /\ k.lop_target_taint = g.lop_target_taint /\
    k.lop_anns = (rp, origin_set rv inst.inst_outputs
      (resolved_out birth post.vs_allocas rp (origin_out PG om inst post)))::anns /\
    k.lop_config = EL (SUC g.lop_cursor) (q0::qs) /\
    k.lop_config = JointConfig stk PG (step_prov PG G inst post)
      (step_taint inst s post tn) fn next
      (layout_phase_normalize T post) oms (origin_step PG om inst post) hs' h' /\
    layout_ordinary_trace vs0 C q0 es qs q k post
Proof
  strip_tac >>
  qpat_x_assum `layout_ordinary_trace _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_trace_def] >> strip_tac >>
  drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  `resolved_config_ok (EL (SUC g.lop_cursor) (q0::qs)) g.lop_ids
    ((rp, origin_set rv inst.inst_outputs
      (resolved_out birth post.vs_allocas rp (origin_out PG om inst post)))::anns)` by
    (simp[] >> irule layout_bound_resolved_ordinary >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `lifetime_ok (SUC g.lop_bound) g.lop_ids (EL (SUC g.lop_cursor) (q0::qs))` by
    (drule_all lifetime_transition >> simp[lifetime_step_def]) >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_trace_def, joint_chain_length] >>
  qexists_tac `g with <| lop_pending := T; lop_cursor := SUC g.lop_cursor;
    lop_bound := SUC g.lop_bound;
    lop_anns := (rp, origin_set rv inst.inst_outputs
      (resolved_out birth post.vs_allocas rp (origin_out PG om inst post)))::anns;
    lop_config := EL (SUC g.lop_cursor) (q0::qs) |>` >>
  gvs[layout_ordinary_trace_def] >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[joint_transition_ordinary, layout_phase_normalize_def] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

val _ = export_theory();
