Theory concretizePtrMstoreProducer
Ancestors
  concretizePtrPairedPrefix concretizePtrPairedPrefixProbe concretizePtrStoreSteps
  concretizePtrPairedFields concretizePtrLedgerAlignment concretizeMemLocDefs
  concretizePtrOpaqueRetpc concretizePtrSharedFields concretizePtrAllocationSize
  unitShapeDefs passSimulationDefs venomExecProofs unitLabelMapIdentity
  concretizePtrTaggedSupport concretizePtrDeletedGapHistory concretizePtrLedgerProbe
  concretizePtrSourceOwnership concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrActivationChronology
  concretizePtrChronologicalHistory
  concretizeStepStructure concretizeStepShape concretizeStepCallChecks
  concretizeStepRetpc concretizeStageShape o1PassContract
  o1ScheduleDecomp venomWf cfgWf ptrDiscipline unitMemInv
  contextCodegenRel venomExecSemantics venomState venomInst
  finite_map list arithmetic

Theorem ptr_mstore_transcript_successor:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  a.po_inst.inst_opcode = MSTORE /\ ptr_chrono_step C' at zt ==>
  ?z. ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
      (done ++ [LENGTH h - 1]) tokens registry births PT TG saved entries
      (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) /\
    ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved /\
    z.po_state.vs_allocas = a.po_state.vs_allocas /\ z.po_stack = a.po_stack
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by
    (drule_all ptr_frame_sizes >> simp[]) >>
  `inst_wf a.po_inst` by
    (gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, wf_function_def] >>
     `MEM a.po_inst (fn_insts a.po_fn)` by
       (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
        simp[Once frame_reachable_cases] >> rpt strip_tac >>
        gvs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]) >>
     fs[fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  `a.po_inst.inst_outputs = []` by gvs[inst_wf_def] >>
  `at.po_inst = a.po_inst` by
    (qpat_x_assum `ptr_paired_cursor lp a at` mp_tac >>
     simp[ptr_paired_cursor_def] >> strip_tac >>
     `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices` by
       (spose_not_then assume_tac >>
        `a.po_state.vs_inst_idx < EL at.po_state.vs_inst_idx indices` by decide_tac >>
        qpat_x_assum `!k. _ ==> _.inst_opcode = NOP`
          (qspec_then `a.po_state.vs_inst_idx` mp_tac) >> simp[] >>
        qpat_x_assum `a.po_inst = _` (SUBST_ALL_TAC) >> gvs[]) >>
     drule ptr_ledger_alignment_cursor >> strip_tac >>
     first_x_assum (qspec_then `at.po_state.vs_inst_idx` mp_tac) >> simp[] >>
     strip_tac >> gvs[concretize_inst_with_positions_def]) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[is_terminator_def]
  >- suspend "successor"
  >> qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac
  >> simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()]
QED

Resume ptr_mstore_transcript_successor[successor]:
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def,
    AllCaseEqs()] >> strip_tac >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
     a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
    fs[ptr_paired_sample_def, ptr_core_shared_def, ptr_shared_fields_def] >>
  drule_all ptr_mixed_vars_eval_presence >>
  disch_then (fn th => map_every (mp_tac o C Q.SPEC th) [`op1`,`op2`]) >>
  simp[] >> rpt strip_tac >>
  Cases_on `eval_operand op1 a.po_state` >> gvs[] >>
  Cases_on `eval_operand op2 a.po_state` >> gvs[] >>
  `?i. active_inst a.po_fn i
    (mstore (w2n x) x' a.po_state with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    suspend "source_cursor" >>
  qmatch_asmsub_abbrev_tac `active_inst a.po_fn i (post with vs_inst_idx := _)` >>
  `step_inst 0 C a.po_inst a.po_state = OK post` by
    simp[Abbr `post`, step_inst_non_invoke, step_inst_base_def, exec_write2_def] >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  `z.po_stack = a.po_stack /\ z.po_state.vs_allocas = a.po_state.vs_allocas` by
    simp[Abbr `z`, Abbr `post`, ptr_ledger_next_def, ptr_observe_def, mstore_def] >>
  `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved` by
    suspend "tagged_step" >>
  qexists_tac `z` >> simp[] >>
  drule ptr_ownership_overlay_fixed >> strip_tac >>
  drule (cj 3 ptr_structural_transcript_rules) >>
  disch_then drule >> disch_then drule >>
  simp[ptr_activation_tokens_def, ptr_activation_registry_def]
QED

Resume ptr_mstore_transcript_successor[source_cursor]:
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  qpat_x_assum `active_inst a.po_fn a.po_inst a.po_state` mp_tac >>
  simp[active_inst_def] >> strip_tac >>
  `bb_well_formed bb` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, wf_function_def] >> metis_tac[]) >>
  `SUC a.po_state.vs_inst_idx < LENGTH bb.bb_instructions` by
    (spose_not_then assume_tac >>
     `a.po_state.vs_inst_idx = LENGTH bb.bb_instructions - 1` by decide_tac >>
     `LAST bb.bb_instructions = a.po_inst` by
       (fs[bb_well_formed_def] >> metis_tac[LAST_EL, PRE_SUB1]) >>
     gvs[bb_well_formed_def, is_terminator_def]) >>
  simp[active_inst_def, mstore_def] >> qexists_tac `bb` >> simp[]
QED

Resume ptr_mstore_transcript_successor[tagged_step]:
  `ptr_tagged_step (HD tokens) PT TG a.po_inst post = TG` by
    simp[ptr_tagged_step_def, step_prov_def, set_prov_def, DRESTRICT_UNIV] >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  drule_all (cj 1 ptr_tagged_chrono_step_rules) >> strip_tac >>
  `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state = a` by
    simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
  fs[Abbr `z`, ptr_ledger_next_def] >> metis_tac[]
QED

Finalise ptr_mstore_transcript_successor
