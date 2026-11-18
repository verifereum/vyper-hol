Theory gasFocusConcretizeCutGas
Ancestors
  gasFocusConcretizeEndpointCut dftBlockSim
  concretizePtrOpaqueRetpc concretizePtrValueTransport concretizePtrOrdinaryNext
  concretizeStepStructure concretizePtrOperationalOpcodes concretizePtrPairedPrefix
  concretizePtrPairedFields concretizePtrStructuralTranscript concretizePtrSourceOwnership
  concretizePtrStructuralTrace concretizePtrChronologicalHistory concretizePtrDeletedGapHistory
  concretizePtrRequestHistory concretizePtrTaintContent concretizePtrSharedFields
  concretizePtrLedgerProbe o1PassContract o1ScheduleDecomp ptrDiscipline pointerConfinedDefs
  contextCodegenRel codegenRel frameViewFacts unitLabelMapIdentity unitShapeDefs
  venomWf venomState venomInst venomExecSemantics opcodeClass finite_map list rich_list

Theorem focus_gas_mixed_vars[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  inst.inst_opcode = GAS /\ inst.inst_outputs = [out] /\ ~retpc_var f out ==>
  ptr_mixed_vars births positions
    (step_prov PT TG inst (update_var out v (s with vs_gas_readings := readings)))
    (step_taint inst s (update_var out v (s with vs_gas_readings := readings)) tn)
    f g (update_var out v (s with vs_gas_readings := readings))
        (update_var out v (t with vs_gas_readings := readings))
Proof
  strip_tac >>
  `ptr_mixed_vars births positions TG tn f g
     (s with vs_gas_readings := readings) (t with vs_gas_readings := readings)` by
    (irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qpat_x_assum `ptr_mixed_vars _ _ _ _ _ _ s t` kall_tac >>
  drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  simp[step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, out_taint_def, set_var_taint_def, op_taint_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ptr_value_transport_refl] >>
  rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def]
QED

Theorem focus_gas_history_content[local]:
  ptr_history_content tn s t ==>
  ptr_history_content tn (s with vs_gas_readings := readings)
    (t with vs_gas_readings := readings)
Proof
  simp[ptr_history_content_def, ptr_taint_content_def,
       ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def,
       contract_storage_def, contract_transient_def] >> strip_tac >> gvs[]
QED

Theorem ptr_focus_gas_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  a.po_inst.inst_opcode = GAS /\ ptr_chrono_step C' at zt ==>
  ?z TG'.
    TG' = step_prov PT TG a.po_inst z.po_state /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws
Proof
  strip_tac >>
  drule ptr_paired_endpoint_readings >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  drule ptr_frame_context_membership >> strip_tac >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `inst_wf a.po_inst /\ ssa_form a.po_fn /\
   EVERY bb_well_formed a.po_fn.fn_blocks /\ ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, wf_function_def,
        fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  `?out. a.po_inst.inst_outputs = [out]` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute]) >>
  `~retpc_var a.po_fn out` by
    (irule noncopy_output_not_retpc >> simp[] >> qexists_tac `a.po_inst` >> simp[]) >>
  `a.po_inst.inst_opcode <> ALLOCA /\ a.po_inst.inst_opcode <> NOP /\
   a.po_inst.inst_opcode <> INVOKE /\ ~is_terminator a.po_inst.inst_opcode` by
    simp[is_terminator_def] >>
  `at.po_inst = a.po_inst` by gvs[concretize_positions_unchanged] >>
  qpat_x_assum `at.po_inst = concretize_inst_with_positions _ _` kall_tac >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[] >>
  drule_all step_inst_gas_single >> strip_tac
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
    simp[]) >>
  suspend "attach"
QED

Resume ptr_focus_gas_step[attach]:
  markerLib.RESUME_TAC >>
  qabbrev_tac `v = case a.po_state.vs_gas_readings of [] => 0w | headgas::tl => headgas` >>
  qabbrev_tac `readings = DROP 1 a.po_state.vs_gas_readings` >>
  qabbrev_tac `post = update_var out v (a.po_state with vs_gas_readings := readings)` >>
  `step_inst 0 C a.po_inst a.po_state = OK post /\
   s' = update_var out v (at.po_state with vs_gas_readings := readings)` by
    (conj_tac >- simp[Abbr `post`, Abbr `v`, Abbr `readings`] >>
     qpat_x_assum `step_inst _ C' _ _ = OK s'` mp_tac >>
     simp[Abbr `v`, Abbr `readings`]) >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (qpat_assum `active_inst a.po_fn a.po_inst a.po_state`
       (mp_then Any mp_tac ptr_ordinary_next_active) >>
     disch_then irule >> simp[Abbr `post`, update_var_def]) >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  qexists_tac `z` >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  drule ptr_paired_stage_local_allocas >>
  disch_then (qspecl_then [`o1_walk_view rpolicy 2`, `rpolicy`] mp_tac) >>
  simp[] >> strip_tac >>
  `ptr_mixed_vars births positions (step_prov PT TG a.po_inst post)
     (step_taint a.po_inst a.po_state post a.po_taint) a.po_fn at.po_fn post s'` by
    (fs[ptr_paired_sample_def] >> drule_all focus_gas_mixed_vars >>
     disch_then (qspecl_then [`v`, `readings`] mp_tac) >> simp[Abbr `post`]) >>
  `ptr_paired_sample positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
     (reverse conj_tac
      >- (fs[ptr_paired_sample_def] >> irule ptr_history_content_masks >>
          qexists_tac `a.po_taint` >>
          simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def] >>
          simp[Abbr `post`] >> irule focus_gas_history_content >> simp[])) >>
     gvs[step_prov_def, out_prov_def] >>
     irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >>
     simp[Abbr `post`, update_var_def]) >>
  `ptr_paired_params positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    fs[ptr_paired_params_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def,
       Abbr `post`, update_var_def] >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, ptr_tagged_step_def,
       step_prov_def, out_prov_def, step_writes_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, range_bytes_def] >>
  fs[Abbr `post`, update_var_def]
QED
Finalise ptr_focus_gas_step
