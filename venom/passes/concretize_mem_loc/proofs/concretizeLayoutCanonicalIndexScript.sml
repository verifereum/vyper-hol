Theory concretizeLayoutCanonicalIndex
Ancestors concretizeLayoutRunEntry concretizeLayoutPhaseTrace
  concretizeLayoutPhaseOrigin concretizeLayoutRunTrace
  concretizeLayoutSelectedPairedResume
  frameActivationLifetime frameResolvedTrace frameResolvedCoherent
  frameJointTransition list arithmetic

Definition layout_phase_canonical_def:
  layout_phase_canonical es (a:layout_ordinary_phase) <=>
    a.lop_ids = EL a.lop_cursor (lifetime_annotations 0 [0] es)
End

Theorem layout_phase_canonical_initial:
  a.lop_cursor = 0 /\ a.lop_ids = [0] ==>
  layout_phase_canonical es a
Proof
  Cases_on `es` >> simp[layout_phase_canonical_def, lifetime_annotations_def]
QED

Theorem layout_phase_canonical_same:
  layout_phase_canonical es a /\ b.lop_cursor = a.lop_cursor /\
  b.lop_ids = a.lop_ids ==> layout_phase_canonical es b
Proof
  simp[layout_phase_canonical_def]
QED

Theorem layout_phase_canonical_edge:
  layout_phase_canonical es a /\ a.lop_cursor < LENGTH es /\
  b.lop_cursor = SUC a.lop_cursor /\
  b.lop_ids = lifetime_step a.lop_cursor (EL a.lop_cursor es) a.lop_ids ==>
  layout_phase_canonical es b
Proof
  simp[layout_phase_canonical_def] >> strip_tac >>
  drule lifetime_annotations_edge >>
  disch_then (qspecl_then [`0`, `[0]`] mp_tac) >> simp[]
QED

Theorem layout_phase_canonical_ordinary:
  layout_phase_canonical es a /\ a.lop_cursor < LENGTH es /\
  EL a.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  b.lop_cursor = SUC a.lop_cursor /\ b.lop_ids = a.lop_ids ==>
  layout_phase_canonical es b
Proof
  strip_tac >> irule layout_phase_canonical_edge >>
  goal_assum (drule_at Any) >> simp[lifetime_step_def]
QED

Theorem layout_phase_canonical_block:
  layout_phase_canonical es a /\ a.lop_cursor < LENGTH es /\
  EL a.lop_cursor es = SOME (OriginBlock fuel post) /\
  b.lop_cursor = SUC a.lop_cursor /\ b.lop_ids = a.lop_ids ==>
  layout_phase_canonical es b
Proof
  strip_tac >> irule layout_phase_canonical_edge >>
  goal_assum (drule_at Any) >> simp[lifetime_step_def]
QED

Theorem layout_phase_canonical_call:
  layout_phase_canonical es a /\ a.lop_cursor < LENGTH es /\
  EL a.lop_cursor es = NONE /\ b.lop_cursor = SUC a.lop_cursor /\
  b.lop_ids = SUC a.lop_cursor::a.lop_ids ==>
  layout_phase_canonical es b
Proof
  strip_tac >> irule layout_phase_canonical_edge >>
  goal_assum (drule_at Any) >> simp[lifetime_step_def]
QED

Theorem layout_phase_canonical_resume:
  layout_phase_canonical es b /\ b.lop_cursor < LENGTH es /\
  EL b.lop_cursor es = SOME (OriginResume fuel fn inst s ret send post) /\
  c.lop_cursor = SUC b.lop_cursor /\ c.lop_ids = TL b.lop_ids ==>
  layout_phase_canonical es c
Proof
  strip_tac >> irule layout_phase_canonical_edge >>
  goal_assum (drule_at Any) >> simp[lifetime_step_def]
QED

Theorem layout_canonical_trace_advance:
  layout_phase_canonical es g /\
  layout_ordinary_trace vs0 C q0 es qs q g s /\ ~g.lop_pending /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  inst.inst_opcode <> DALLOCA /\ g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) ==>
  ?k. k.lop_origin = g.lop_origin /\ k.lop_pending /\
    k.lop_cursor = SUC g.lop_cursor /\ k.lop_bound = SUC g.lop_bound /\
    k.lop_ids = g.lop_ids /\ k.lop_target_taint = g.lop_target_taint /\
    k.lop_config = EL (SUC g.lop_cursor) (q0::qs) /\
    layout_ordinary_trace vs0 C q0 es qs q k post /\
    layout_phase_canonical es k
Proof
  strip_tac >> drule_all layout_ordinary_trace_advance >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  irule layout_phase_canonical_ordinary >> goal_assum (drule_at Any) >> simp[]
QED

Theorem layout_phase_canonical_annotation_edge:
  layout_phase_canonical es a /\ a.lop_cursor < LENGTH es /\
  resolved_annotation_edge C a.lop_cursor qa (EL a.lop_cursor es) qb
    a.lop_ids anns ids' anns' /\
  b.lop_cursor = SUC a.lop_cursor /\ b.lop_ids = ids' ==>
  layout_phase_canonical es b
Proof
  simp[resolved_annotation_edge_def] >> strip_tac >>
  irule layout_phase_canonical_edge >> goal_assum (drule_at Any) >> simp[]
QED

Theorem layout_canonical_block_trace:
  layout_phase_canonical es a /\
  layout_ordinary_trace vs0 C q0 es qs q a s /\
  a.lop_cursor < LENGTH es /\
  EL a.lop_cursor es = SOME (OriginBlock fuel post) ==>
  ?b. b.lop_origin = a.lop_origin /\ ~b.lop_pending /\
    b.lop_cursor = SUC a.lop_cursor /\ b.lop_bound = SUC a.lop_bound /\
    b.lop_config = EL (SUC a.lop_cursor) (q0::qs) /\
    b.lop_ids = a.lop_ids /\ b.lop_target_taint = a.lop_target_taint /\
    layout_ordinary_trace vs0 C q0 es qs q b p /\
    layout_phase_canonical es b
Proof
  strip_tac >> drule_all layout_run_block_trace >>
  disch_then (qspec_then `p` strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >>
  irule layout_phase_canonical_block >> goal_assum (drule_at Any) >> simp[]
QED

Theorem layout_canonical_enters_entry:
  enters_block fn s p /\ enters_block fn' t p' /\ ~a.lop_pending /\
  layout_ordinary_trace vs0 C q0 es qs q a p /\
  layout_ordinary_state D lo C' q0 es qs a p p' /\
  layout_phase_canonical es a ==>
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
    layout_scoped_phi_link g (INL b) fn fn' s t bb bb' phi phi' /\
    layout_phase_canonical es b
Proof
  strip_tac >> drule_all layout_scoped_enters_entry >>
  disch_then (qspec_then `g` strip_assume_tac) >>
  gvs[layout_phase_canonical_def]
QED

Theorem layout_canonical_initial_enters_entry:
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
      (concretize_function_with_positions positions fn) s s bb bb' phi phi' /\
    layout_phase_canonical es b
Proof
  strip_tac >> drule_all layout_scoped_initial_enters_entry >>
  disch_then (qspecl_then [`positions`, `lo`] mp_tac) >>
  disch_then (qspecl_then [`g`, `D`, `C'`] strip_assume_tac) >>
  goal_assum (drule_at Any) >> gvs[] >>
  irule layout_phase_canonical_initial >> simp[]
QED

Theorem layout_canonical_resume_paired_entry:
  layout_paired_ordinary D lo vs0 C C' q0 es qs q positions
    a.lop_config a.lop_cursor bb caller bb' caller' a /\
  a.lop_config = JointConfig stk PG G caller_tn fn call caller oms om hs h /\
  a.lop_ids = birth::ids /\ a.lop_anns = (rp,rv)::anns /\
  a.lop_ids = EL a.lop_cursor iss /\ a.lop_anns = EL a.lop_cursor ass /\
  call.inst_opcode = INVOKE /\ decode_invoke call = SOME (name,ops) /\
  lookup_function name C.ctx_functions = SOME callee /\
  eval_operands ops caller = SOME args /\ setup_callee callee args caller = SOME cs /\
  get_instruction bb caller.vs_inst_idx = SOME call /\
  joint_transition C a.lop_config NONE qc /\
  selected_segment C q0 path a.lop_cursor a.lop_config ((NONE,qc)::w) b.lop_config /\
  decorated_run C callee cs (IntRet ret sc) qc (SUC a.lop_cursor) w b.lop_config dc /\
  b.lop_cursor = SUC a.lop_cursor + LENGTH w /\
  layout_ret_endpoint D lo vs0 C C' q0 es qs q b sc tc ret ret' /\
  b.lop_config = JointConfig cstk cPG cG tn callee inst sc coms com chs ch /\
  inst.inst_opcode = RET /\
  b.lop_ids = EL b.lop_cursor iss /\ b.lop_anns = EL b.lop_cursor ass /\
  es = MAP FST path /\ qs = MAP SND path /\ vs0.vs_allocas = FEMPTY /\
  b.lop_cursor < LENGTH es /\
  EL b.lop_cursor es = SOME (OriginResume fuel callee inst sc ret sc post) /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path)) (EL k iss) (EL k ass)
      (EL (SUC k) iss) (EL (SUC k) ass)) /\
  bind_outputs call.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller sc)) = SOME post /\
  bind_outputs call.inst_outputs ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state caller' tc)) = SOME post' /\
  layout_phase_canonical es b /\
  c = (a with <| lop_pending := F; lop_cursor := SUC b.lop_cursor;
    lop_bound := SUC b.lop_bound;
    lop_config := EL (SUC b.lop_cursor) (q0::qs);
    lop_ids := EL (SUC b.lop_cursor) iss;
    lop_anns := EL (SUC b.lop_cursor) ass;
    lop_target_taint := b.lop_target_taint with
      t_var := DRESTRICT a.lop_target_taint.t_var (COMPL (set call.inst_outputs)) |>) ==>
  layout_paired_ordinary D lo vs0 C C' q0 es qs q positions
    (EL (SUC b.lop_cursor) (q0::qs)) (SUC b.lop_cursor)
    bb (post with vs_inst_idx := SUC caller.vs_inst_idx)
    bb' (post' with vs_inst_idx := SUC caller'.vs_inst_idx) c /\
  layout_phase_canonical es c
Proof
  strip_tac >> conj_tac
  >- (drule_all layout_selected_resume_paired_entry >> simp[]) >>
  `resolved_annotation_edge C b.lop_cursor (EL b.lop_cursor (q0::qs))
    (EL b.lop_cursor es) (EL (SUC b.lop_cursor) (q0::qs))
    b.lop_ids b.lop_anns (EL (SUC b.lop_cursor) iss)
    (EL (SUC b.lop_cursor) ass)` by
    (qpat_x_assum `!k. k < LENGTH path ==> _`
       (qspec_then `b.lop_cursor` mp_tac) >>
     gvs[EL_MAP]) >>
  irule layout_phase_canonical_annotation_edge >>
  goal_assum (drule_at Any) >> simp[]
QED

val _ = export_theory();
