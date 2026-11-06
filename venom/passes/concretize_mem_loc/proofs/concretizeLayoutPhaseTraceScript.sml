Theory concretizeLayoutPhaseTrace
Ancestors concretizeLayoutPhaseOrigin frameJointTrace frameResolvedTrace
  frameActivationLifetime list

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

val _ = export_theory();
