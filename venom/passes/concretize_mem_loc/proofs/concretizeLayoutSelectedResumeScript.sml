Theory concretizeLayoutSelectedResume
Ancestors concretizeLayoutResumeNormalize frameDecoratedIdentifierSuffix
  frameDecoratedAnnotationSuffix frameResolvedReturn frameFiniteCallPrefix
  frameFiniteContext frameSelectedDecoration frameResolvedCoherent
  frameDecoratedEndpoints frameJointTransition frameFiniteJointDecoration
  concretizeLayoutCallerResume concretizeLayoutPhaseOrigin frameResolvedSegments
  frameActivationLifetime arithmetic list

(* The annotations below are the fixed ambient witnesses, not independently
   selected pointwise decorations. *)
Theorem layout_selected_resume_entry:
  layout_ordinary_entry D lo vs0 C C' q0 es qs q a caller caller' /\
  ~a.lop_pending /\
  a.lop_config = JointConfig stk PG G caller_tn fn call caller oms om hs h /\
  a.lop_ids = birth::ids /\ a.lop_anns = (rp,rv)::anns /\
  a.lop_ids = EL a.lop_cursor iss /\ a.lop_anns = EL a.lop_cursor ass /\
  call.inst_opcode = INVOKE /\ decode_invoke call = SOME (name,ops) /\
  lookup_function name C.ctx_functions = SOME callee /\
  eval_operands ops caller = SOME args /\ setup_callee callee args caller = SOME cs /\
  get_instruction a.lop_origin.lbo_source caller.vs_inst_idx = SOME call /\
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
    (adopt_return_fmp ret' (merge_callee_state caller' tc)) = SOME post' ==>
  layout_ordinary_entry D lo vs0 C C' q0 es qs q
    (a with <| lop_pending := F; lop_cursor := SUC b.lop_cursor;
      lop_bound := SUC b.lop_bound;
      lop_config := EL (SUC b.lop_cursor) (q0::qs);
      lop_ids := EL (SUC b.lop_cursor) iss;
      lop_anns := EL (SUC b.lop_cursor) ass;
      lop_target_taint := b.lop_target_taint with
        t_var := DRESTRICT a.lop_target_taint.t_var (COMPL (set call.inst_outputs)) |>)
    (post with vs_inst_idx := SUC caller.vs_inst_idx)
    (post' with vs_inst_idx := SUC caller'.vs_inst_idx)
Proof
  strip_tac >>
  `layout_saved_caller D lo C' q0 es qs a caller caller'` by
    fs[layout_saved_caller_def, layout_ordinary_entry_def] >>
  `selected_run C q0 path callee cs (IntRet ret sc) qc
     (SUC a.lop_cursor) w b.lop_config dc` by
    (qpat_x_assum `selected_segment _ _ _ _ _ _ _` mp_tac >>
     simp[selected_segment_def] >> strip_tac >>
     simp[selected_run_def, selected_segment_def] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`pre ++ [(NONE,qc)]`, `suffix`] >>
     simp[APPEND_ASSOC] >>
     metis_tac[joint_segment_append, joint_segment_def,
               cj 3 decorated_execution_segment]) >>
  `EL a.lop_cursor (MAP FST path) = NONE` by
    (qpat_x_assum `selected_segment _ _ _ _ _ _ _` mp_tac >>
     simp[selected_segment_def] >> strip_tac >>
     gvs[MAP_APPEND, EL_APPEND_EQN]) >>
  drule selected_segment_indices >> strip_tac >>
  `a.lop_cursor < LENGTH path` by fs[] >>
  `FST (EL a.lop_cursor path) = NONE` by fs[EL_MAP] >>
  `resolved_annotation_edge C a.lop_cursor a.lop_config NONE qc
     (EL a.lop_cursor iss) (EL a.lop_cursor ass)
     (EL (SUC a.lop_cursor) iss) (EL (SUC a.lop_cursor) ass)` by
    (qpat_x_assum `!k. k < LENGTH path ==> _`
       (qspec_then `a.lop_cursor` mp_tac) >>
     simp[] >>
     `EL (SUC a.lop_cursor) (q0::MAP SND path) = qc` by
       (qpat_x_assum `selected_segment _ _ _ _ _ _ _` mp_tac >>
        simp[selected_segment_def] >> strip_tac >>
        gvs[MAP_APPEND, EL_APPEND_EQN]) >> fs[]) >>
  `EL (SUC a.lop_cursor) iss = SUC a.lop_cursor::birth::ids /\
   EL (SUC a.lop_cursor) ass =
     (MAP (resolved_op rv) ops,FEMPTY)::(rp,rv)::anns` by
    (fs[resolved_annotation_edge_def, lifetime_step_def,
        Once resolved_annotation_update_cases] >> gvs[]) >>
  drule_all selected_run_IntRet_identifiers >> strip_tac >>
  drule_all selected_run_IntRet_annotation_suffix >> strip_tac >>
  `decoration_frame b.lop_config = decoration_frame qc` by
    metis_tac[cj 3 decorated_execution_frame] >>
  `cstk = <| cf_fn := fn; cf_inst := call; cf_state := caller;
       cf_params := PG; cf_prov := G; cf_tvar := caller_tn.t_var |> :: stk /\
   coms = om::oms /\ chs = h::hs` by
    (gvs[] >> fs[joint_transition_call_iff, decoration_frame_def] >>
     gvs[decoration_frame_def]) >>
  `layout_ordinary_trace vs0 C q0 es qs q b sc` by
    fs[concretizeLayoutCallResultTheory.layout_ret_endpoint_def,
       layout_ordinary_entry_def] >>
  `b.lop_cursor < LENGTH path` by gvs[] >>
  `FST (EL b.lop_cursor path) = SOME (OriginResume fuel callee inst sc ret sc post)` by
    (qpat_x_assum `EL b.lop_cursor es = _` mp_tac >> simp[EL_MAP]) >>
  `EL b.lop_cursor (q0::MAP SND path) = b.lop_config` by
    gvs[layout_ordinary_trace_def] >>
  `resolved_annotation_edge C b.lop_cursor b.lop_config
     (SOME (OriginResume fuel callee inst sc ret sc post))
     (EL (SUC b.lop_cursor) (q0::qs))
     b.lop_ids b.lop_anns (EL (SUC b.lop_cursor) iss) (EL (SUC b.lop_cursor) ass)` by
    (qpat_x_assum `!k. k < LENGTH path ==> _`
       (qspec_then `b.lop_cursor` mp_tac) >>
     metis_tac[]) >>
  `b.lop_ids = SUC a.lop_cursor::birth::ids /\
   b.lop_anns = callee'::(rp,rv)::anns` by metis_tac[] >>
  `EL (SUC b.lop_cursor) iss = birth::ids /\
   EL (SUC b.lop_cursor) ass =
     (rp,DRESTRICT rv (COMPL (set call.inst_outputs)))::anns` by
    (qpat_x_assum `resolved_annotation_edge _ _ _ (SOME _) _ _ _ _ _` mp_tac >>
     qpat_x_assum `!k. k < LENGTH path ==> _` kall_tac >>
     qpat_x_assum `b.lop_ids = EL _ _` kall_tac >>
     qpat_x_assum `b.lop_anns = EL _ _` kall_tac >>
     simp[resolved_annotation_edge_def, lifetime_step_def,
          Once resolved_annotation_update_cases]) >>
  `caller.vs_call_ctx.cc_address = sc.vs_call_ctx.cc_address` by
    (drule (cj 3 decorated_execution_erases) >> strip_tac >>
     drule_all finite_callee_IntRet_address >> simp[]) >>
  drule_all layout_saved_caller_state >> strip_tac >>
  `?PG' G' next oms' om' hs' h'.
    EL (SUC b.lop_cursor) (q0::qs) =
      JointConfig stk PG' G'
        (tn with t_var := DRESTRICT caller_tn.t_var (COMPL (set call.inst_outputs)))
        fn next (post with vs_inst_idx := SUC caller.vs_inst_idx) oms' om' hs' h'` by
    (qpat_x_assum `resolved_annotation_edge _ _ _ (SOME _) _ _ _ _ _` mp_tac >>
     simp[resolved_annotation_edge_def, joint_transition_return] >> metis_tac[]) >>
  qabbrev_tac `restored = a with <| lop_pending := F;
    lop_cursor := SUC b.lop_cursor;
    lop_config := JointConfig stk PG' G'
      (tn with t_var := DRESTRICT caller_tn.t_var (COMPL (set call.inst_outputs)))
      fn next post oms' om' hs' h';
    lop_anns := (rp,DRESTRICT rv (COMPL (set call.inst_outputs)))::anns;
    lop_target_taint := b.lop_target_taint with
      t_var := DRESTRICT a.lop_target_taint.t_var (COMPL (set call.inst_outputs)) |>` >>
  `layout_ordinary_state D lo C' q0 es qs restored post post'` by
    (simp[Abbr `restored`] >> metis_tac[]) >>
  `~restored.lop_pending /\ restored.lop_config = JointConfig stk PG' G'
      (tn with t_var := DRESTRICT caller_tn.t_var (COMPL (set call.inst_outputs)))
      fn next post oms' om' hs' h'` by simp[Abbr `restored`] >>
  drule_all layout_ordinary_state_resume_indices >>
  strip_tac >>
  simp[layout_ordinary_entry_def] >>
  conj_tac >-
    (`finite_step C call caller (OK post)` by
       (irule (cj 2 frameFiniteExecutionTheory.finite_step_rules) >> simp[] >>
        metis_tac[cj 3 decorated_execution_erases]) >>
     irule finite_invoke_terminal_call_prefix_extend >>
     gvs[layout_ordinary_entry_def, layout_phase_normalize_def] >> metis_tac[]) >>
  reverse conj_tac >-
    (qpat_x_assum `!j i bound. layout_ordinary_state _ _ _ _ _ _ _ _ _`
       (qspecl_then [`SUC caller'.vs_inst_idx`, `SUC caller.vs_inst_idx`,
                    `SUC b.lop_bound`] mp_tac) >>
     qpat_x_assum `a.lop_ids = EL _ _` kall_tac >>
     qpat_x_assum `a.lop_ids = birth::ids` (fn th =>
       simp[Abbr `restored`, GSYM th]) >>
     simp[layout_ordinary_state_def]) >>
  `joint_transition C b.lop_config
     (SOME (OriginResume fuel callee inst sc ret sc post))
     (EL (SUC b.lop_cursor) (q0::qs))` by
    (qpat_x_assum `resolved_annotation_edge _ _ _ (SOME _) _ _ _ _ _` mp_tac >>
     simp[resolved_annotation_edge_def]) >>
  `resolved_config_ok (EL (SUC b.lop_cursor) (q0::qs))
     (birth::ids) ((rp,DRESTRICT rv (COMPL (set call.inst_outputs)))::anns)` by
    (qpat_x_assum `layout_ordinary_trace _ _ _ _ _ _ b _` mp_tac >>
     simp[layout_ordinary_trace_def] >> strip_tac >>
     qpat_x_assum `!k. k < LENGTH path ==> _` kall_tac >>
     drule resolved_config_return_exact >>
     gvs[] >> disch_then irule >> simp[] >>
     qexistsl [`callee'`, `SUC a.lop_cursor`] >> metis_tac[]) >>
  `lifetime_ok (SUC b.lop_bound) (birth::ids)
     (EL (SUC b.lop_cursor) (q0::qs))` by
    (qpat_x_assum `layout_ordinary_trace _ _ _ _ _ _ b _` mp_tac >>
     simp[layout_ordinary_trace_def] >> strip_tac >>
     drule lifetime_transition >>
     disch_then (qspec_then `b.lop_bound` mp_tac) >>
     simp[lifetime_step_def] >>
     disch_then (qspec_then `SUC a.lop_cursor::birth::ids` mp_tac) >>
     simp[] >> gvs[]) >>
  gvs[layout_ordinary_trace_def]
QED

val _ = export_theory();
