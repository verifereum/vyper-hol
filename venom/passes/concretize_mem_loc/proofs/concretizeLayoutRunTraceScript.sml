Theory concretizeLayoutRunTrace
Ancestors concretizeLayoutPhaseOrigin frameJointTrace frameResolvedTrace
  frameActivationLifetime frameJointTransition frameOriginHistory finite_map

(* Ready trace bookkeeping does not constrain p.  Ordinary state alignment
   must separately identify p with the actual sampled configuration state. *)
Theorem layout_run_initial_trace:
  joint_trace vs0 C q0 es qs q ==>
  layout_ordinary_trace vs0 C q0 es qs q
    (a with <|lop_pending := F; lop_cursor := 0; lop_bound := 0;
      lop_config := q0; lop_ids := [0]; lop_anns := [([],FEMPTY)]|>) p
Proof
  strip_tac >> simp[layout_ordinary_trace_def] >>
  metis_tac[joint_trace_def, resolved_config_initial, lifetime_initial]
QED

Theorem layout_run_block_trace:
  layout_ordinary_trace vs0 C q0 es qs q a s /\
  a.lop_cursor < LENGTH es /\
  EL a.lop_cursor es = SOME (OriginBlock fuel post) ==>
  ?b. b.lop_origin = a.lop_origin /\ ~b.lop_pending /\
    b.lop_cursor = SUC a.lop_cursor /\ b.lop_bound = SUC a.lop_bound /\
    b.lop_config = EL (SUC a.lop_cursor) (q0::qs) /\
    b.lop_ids = a.lop_ids /\ b.lop_target_taint = a.lop_target_taint /\
    layout_ordinary_trace vs0 C q0 es qs q b p
Proof
  simp[layout_ordinary_trace_def] >> strip_tac >>
  drule_all joint_trace_edge_at >> strip_tac >>
  qpat_x_assum `joint_transition C _ _ _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all resolved_config_block >> disch_then (qx_choose_then `anns` assume_tac) >>
  `lifetime_ok (SUC a.lop_bound) a.lop_ids
    (EL (SUC a.lop_cursor) (q0::qs))` by
    (drule_all lifetime_transition >> simp[lifetime_step_def]) >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_trace_def, joint_chain_length] >>
  qexists `a with <|lop_pending := F; lop_cursor := SUC a.lop_cursor;
    lop_bound := SUC a.lop_bound;
    lop_config := EL (SUC a.lop_cursor) (q0::qs); lop_anns := anns|>` >>
  gs[]
QED

val _ = export_theory();
