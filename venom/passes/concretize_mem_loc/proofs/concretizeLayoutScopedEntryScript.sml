Theory concretizeLayoutScopedEntry
Ancestors concretizeLayoutScopedPhase concretizeLayoutPhaseOrigin
          concretizeLayoutPhaseCompose frameTerminalCallOrigins
          concretizeLayoutBlockEntry concretizeStepStructure
          concretizeLayoutSupplement frameCfgBoundary contextCodegenRel
          frameRelocationLocal frameRelocationEnvironment frameRelocationTaintOrder
          frameResolvedTrace frameRelocationGuardedValues concretizeLayoutReaderContext
          passSharedDefs passSimulationDefs passSimulationProofs ptrDiscipline
          venomExecProofs venomExecProps
          venomExecSemantics venomState

(* Origin installation does not manufacture trace alignment: it preserves the
   trace and state already supplied at the two actual normalized PHI states. *)
Theorem layout_scoped_install_origin:
  ~a.lop_pending /\ layout_ordinary_trace vs0 C q0 es qs q a p /\
  layout_ordinary_state D lo C' q0 es qs a p p' /\
  p = (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
  p' = (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) ==>
  ?b. b = (a with lop_origin :=
      <|lbo_source := bb; lbo_target := bb'; lbo_entry := p|>) /\
    layout_ordinary_entry D lo vs0 C C' q0 es qs q b p p' /\
    layout_scoped_phi_link g (INL b) fn fn' s t bb bb' phi phi'
Proof
  rpt strip_tac >> simp[layout_scoped_phi_link_def,
    layout_phase_begins_def, layout_phase_origin_def, layout_phase_pending_def,
    layout_ordinary_entry_def, layout_ordinary_trace_def] >>
  conj_tac >- simp[terminal_call_prefix_rules] >>
  Cases_on `a.lop_config` >>
  gvs[layout_ordinary_state_def, layout_ordinary_trace_def]
QED

(* Raw PHI entry exposes both independently normalized indices. *)
Theorem layout_scoped_raw_phis:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb_well_formed bb /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R concretize_local_obs s t /\
  relocation_taint_le R tn un /\ relocation_env s t /\
  relocation_reader_context s t /\ s.vs_prev_bb = t.vs_prev_bb /\
  s.vs_current_bb = t.vs_current_bb /\
  EVERY (\inst. MEM inst (fn_insts fn)) bb.bb_instructions /\
  concretize_supplement D tn s t /\ eval_phis s bb.bb_instructions = OK phi /\
  s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section ==>
  ?bb' phi' p p'.
    bb' = clear_nops_block (block_map_transform
      (concretize_inst_with_positions positions) bb) /\
    lookup_block t.vs_current_bb
      (concretize_function_with_positions positions fn).fn_blocks = SOME bb' /\
    eval_phis t bb'.bb_instructions = OK phi' /\
    p = (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
    p' = (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions) /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn) L (resolved_phis s.vs_prev_bb rv bb.bb_instructions))
      (guarded_bytes (retpc_var fn) (resolved_phis s.vs_prev_bb rv bb.bb_instructions)
        (tn with t_var := phis_taint s.vs_prev_bb tn bb.bb_instructions)) R
      concretize_local_obs p p' /\
    relocation_taint_le R
      (tn with t_var := phis_taint s.vs_prev_bb tn bb.bb_instructions)
      (un with t_var := phis_taint t.vs_prev_bb un bb.bb_instructions) /\
    relocation_env p p' /\ relocation_reader_context p p' /\
    concretize_supplement D
      (tn with t_var := phis_taint s.vs_prev_bb tn bb.bb_instructions) p p' /\
    p.vs_current_bb = p'.vs_current_bb /\ p.vs_prev_bb = p'.vs_prev_bb /\
    p.vs_code = p'.vs_code /\ p.vs_data_section = p'.vs_data_section
Proof
  strip_tac >>
  `enters_block fn s (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[enters_block_def] >> metis_tac[]) >>
  drule_all concretize_enters_block_transport >>
  disch_then (qspec_then `positions` strip_assume_tac) >>
  qpat_x_assum `enters_block _ t _` mp_tac >>
  simp[enters_block_def, concretize_positions_blocks, lookup_block_map_proof,
       concretize_positions_block_label] >>
  strip_tac >> gvs[] >>
  imp_res_tac eval_phis_only_updates_vs_vars >>
  fs[venom_state_component_equality]
QED

val _ = export_theory();
