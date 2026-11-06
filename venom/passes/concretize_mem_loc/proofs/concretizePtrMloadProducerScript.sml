Theory concretizePtrMloadProducer
Ancestors concretizePtrMloadExecution concretizePtrMstoreProducer
  concretizePtrPairedNextAttach
  concretizePtrMloadEndpoint concretizePtrPairedPrefix concretizePtrPairedFields
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrSourceOwnership concretizePtrChronologicalHistory
  concretizePtrActivationChronology
  concretizePtrAllocationSize concretizePtrDeletedGapHistory
  concretizePtrTaggedSupport concretizePtrLedgerProbe concretizePtrLedgerAlignment
  concretizePtrPrefixLedger concretizePtrSharedFields concretizePtrEventEmbedding
  concretizePtrStagePlacements concretizePtrDeletedGaps concretizePtrExecutedCoverage
  concretizeStepStructure concretizeStepShape concretizeStepCallChecks
  concretizeStepRetpc concretizeStageShape ptrDiscipline o1PassContract
  o1ScheduleDecomp unitShapeDefs passSimulationDefs venomExecProofs
  unitLabelMapIdentity contextCodegenRel codegenRel
  venomWf cfgWf venomExecSemantics venomState venomInst
  concretizePtrValueTransport concretizePtrOpaqueRetpc
  concretizePtrComparisonTransport finite_map list arithmetic

Theorem ptr_paired_prefix_mload:
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
  max_live_eom C' = SOME eom /\
  a.po_inst.inst_opcode = MLOAD /\ ptr_chrono_step C' at zt ==>
  ?z TG'.
    TG' = step_prov PT TG a.po_inst z.po_state /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws
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
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `at.po_inst = a.po_inst` by
    (qpat_x_assum `ptr_paired_cursor lp a at` mp_tac >>
     simp[ptr_paired_cursor_def] >> strip_tac >>
     `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices` by
       (spose_not_then assume_tac >>
        `a.po_state.vs_inst_idx < EL at.po_state.vs_inst_idx indices` by decide_tac >>
        qpat_x_assum `!k. _ ==> _.inst_opcode = NOP`
          (qspec_then `a.po_state.vs_inst_idx` mp_tac) >> simp[] >>
        qpat_x_assum `a.po_inst = _` SUBST_ALL_TAC >> gvs[]) >>
     drule ptr_ledger_alignment_cursor >> strip_tac >>
     first_x_assum (qspec_then `at.po_state.vs_inst_idx` mp_tac) >> simp[] >>
     strip_tac >> gvs[concretize_positions_unchanged]) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[is_terminator_def]
  >- suspend "successor"
  >> qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac
  >> simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def, AllCaseEqs()]
QED

Resume ptr_paired_prefix_mload[successor]:
  `?post. step_inst 0 C a.po_inst a.po_state = OK post /\
     ptr_mixed_vars births positions (step_prov PT TG a.po_inst post)
       (step_taint a.po_inst a.po_state post a.po_taint)
       a.po_fn at.po_fn post s'` by
    (drule ptr_paired_mload_execution_back >> simp[] >>
     disch_then (qspecl_then [`zt`,`rpolicy`,`names`,`0`,`s'`] mp_tac) >>
     (impl_tac >-
       (qpat_x_assum `step_inst fuel C' _ _ = OK _` mp_tac >>
        simp[step_inst_non_invoke])) >> simp[]) >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    suspend "source_cursor" >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  qabbrev_tac `TG' = step_prov PT TG a.po_inst z.po_state` >>
  `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG' saved` by
    suspend "tagged" >>
  `z.po_stack = a.po_stack /\ z.po_state.vs_allocas = a.po_state.vs_allocas` by
    suspend "unchanged" >>
  `ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
     (done ++ [LENGTH h - 1]) tokens registry births PT TG' saved entries
     (H ++ [(tokens,registry,births,PT,TG',saved,entries)])` by
    (drule ptr_ownership_overlay_fixed >> strip_tac >>
     drule (cj 3 ptr_structural_transcript_rules) >>
     disch_then drule >> disch_then drule >>
     simp[ptr_activation_tokens_def, ptr_activation_registry_def]) >>
  qexists_tac `z` >> qunabbrev_tac `TG'` >>
  suspend "assembly"
QED

Resume ptr_paired_prefix_mload[source_cursor]:
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
  qpat_x_assum `step_inst _ C _ _ = OK post` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> simp[active_inst_def, update_var_def] >>
  qexists_tac `bb` >> simp[]
QED

Resume ptr_paired_prefix_mload[tagged]:
  `ptr_tagged_step (HD tokens) PT TG a.po_inst post = TG'` by
    (simp[ptr_tagged_step_def, Abbr `TG'`, Abbr `z`, ptr_ledger_next_def,
          ptr_observe_def, step_prov_def, out_prov_def]) >>
  `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  qpat_x_assum `step_inst fuel C' _ _ = OK _` kall_tac >>
  drule_all (cj 1 ptr_tagged_chrono_step_rules) >> strip_tac >>
  `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state = a` by
    simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
  fs[Abbr `z`, ptr_ledger_next_def] >> metis_tac[]
QED
Resume ptr_paired_prefix_mload[unchanged]:
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  qpat_x_assum `step_inst 0 C _ _ = OK post` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def, AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def]
QED
Resume ptr_paired_prefix_mload[assembly]:
  `ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  `!ai. MEM ai (fn_insts a.po_fn) /\ ai.inst_opcode = ALLOCA ==>
       ?p. FLOOKUP (lp a.po_fn) (Allocation ai.inst_id) = SOME p` by
    (rpt strip_tac >>
     drule_all ptr_stage_alloca_mems >> strip_tac >>
     `MEM g C'.ctx_functions` by metis_tac[lookup_function_MEM] >>
     `FLOOKUP positions (Allocation ai.inst_id) =
       SOME (p,get_alloca_size a.po_fn (Allocation ai.inst_id))` by
       (fs[ptr_paired_prefix_def, ptr_stage_placements_def] >> metis_tac[]) >>
     fs[ptr_paired_code_def, fn_insts_MEM] >>
     qpat_x_assum `!bb inst. _` (qspecl_then [`bb`,`ai`] mp_tac) >> simp[]) >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  `LAST h = a /\ LAST ht = at` by metis_tac[ptr_chrono_history_end] >>
  `z.po_fn = a.po_fn` by simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  `ptr_paired_sample positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    suspend "sample" >>
  `ptr_paired_cursor lp z zt /\ ptr_paired_params positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    suspend "alignment" >>
  drule ptr_paired_prefix_nonwrite_attach >> disch_then irule >>
  simp[step_writes_def, source_memory_write_ranges_def, fixed_source_write_range_def,
       range_bytes_def]
QED

Resume ptr_paired_prefix_mload[sample]:
  qpat_x_assum `step_inst 0 C _ _ = OK post` mp_tac >>
  qpat_x_assum `step_inst fuel C' _ _ = OK s'` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  reverse conj_tac
  >- fs[ptr_paired_sample_def, ptr_core_shared_def, ptr_shared_fields_def, update_var_def] >>
  qpat_x_assum `ptr_mixed_vars _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `_.inst_opcode = MLOAD` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> strip_tac >>
  qmatch_goalsub_abbrev_tac `step_prov PT TG _ ps` >>
  qmatch_goalsub_abbrev_tac `ptr_mixed_vars _ _ _ _ _ _ ps pt` >>
  simp[ptr_mixed_vars_def, ptr_opaque_env_def, lookup_var_def,
       step_prov_def, out_prov_def] >> metis_tac[]
QED
Resume ptr_paired_prefix_mload[alignment]:
  `z.po_fn = a.po_fn` by simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  simp[] >>
  qpat_x_assum `step_inst 0 C _ _ = OK post` mp_tac >>
  qpat_x_assum `step_inst fuel C' _ _ = OK s'` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def, AllCaseEqs()] >>
  disch_then strip_assume_tac >> disch_then strip_assume_tac >> gvs[] >>
  reverse conj_tac
  >- fs[ptr_paired_params_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def,
        update_var_def] >>
  gvs[ptr_paired_cursor_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def,
      update_var_def] >> suspend "cursor"
QED
Resume ptr_paired_prefix_mload[cursor]:
  `SUC (LAST h).po_state.vs_inst_idx < LENGTH bb.bb_instructions /\
   i = EL (SUC (LAST h).po_state.vs_inst_idx) bb.bb_instructions` by
    (qpat_assum `active_inst _ i _` mp_tac >>
     qpat_assum `lookup_block _ (LAST h).po_fn.fn_blocks = SOME bb` mp_tac >>
     qpat_assum `(LAST h).po_state.vs_current_bb = (LAST ht).po_state.vs_current_bb` mp_tac >>
     qpat_assum `ALL_DISTINCT (fn_labels (LAST h).po_fn)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[active_inst_def, fn_labels_def] >> rpt strip_tac >>
     rename1 `MEM nextbb (LAST h).po_fn.fn_blocks` >>
     `lookup_block (LAST ht).po_state.vs_current_bb (LAST h).po_fn.fn_blocks = SOME nextbb` by
       (irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  `SUC (LAST ht).po_state.vs_inst_idx < LENGTH bbt.bb_instructions /\
   zt.po_inst = EL (SUC (LAST ht).po_state.vs_inst_idx) bbt.bb_instructions` by
    (qpat_assum `active_inst _ zt.po_inst _` mp_tac >>
     qpat_assum `lookup_block _ (LAST ht).po_fn.fn_blocks = SOME bbt` mp_tac >>
     qpat_assum `ALL_DISTINCT (fn_labels (LAST ht).po_fn)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[active_inst_def, fn_labels_def] >> rpt strip_tac >>
     rename1 `MEM nextbb (LAST ht).po_fn.fn_blocks` >>
     `lookup_block (LAST ht).po_state.vs_current_bb (LAST ht).po_fn.fn_blocks = SOME nextbb` by
       (irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  suspend "cursor_order"
QED
Resume ptr_paired_prefix_mload[cursor_order]:
  ` (LAST h).po_state.vs_inst_idx = EL (LAST ht).po_state.vs_inst_idx indices` by
    (spose_not_then assume_tac >>
     ` (LAST h).po_state.vs_inst_idx < EL (LAST ht).po_state.vs_inst_idx indices` by decide_tac >>
     qpat_x_assum `!k. _ ==> _.inst_opcode = NOP`
       (qspec_then `(LAST h).po_state.vs_inst_idx` mp_tac) >> simp[]) >>
  `LENGTH bbt.bb_instructions = LENGTH indices` by
    (drule ptr_ledger_alignment_cursor >> simp[]) >>
  `SUC (LAST ht).po_state.vs_inst_idx < LENGTH indices` by decide_tac >>
  `EL (LAST ht).po_state.vs_inst_idx indices <
   EL (SUC (LAST ht).po_state.vs_inst_idx) indices` by
    (qpat_assum `ptr_ledger_block_alignment _ _ _ indices` mp_tac >>
     qpat_assum `SUC (LAST ht).po_state.vs_inst_idx < LENGTH indices` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     irule ptr_ledger_alignment_order >> simp[] >>
     qexistsl_tac [`lp (LAST h).po_fn`,`bb.bb_instructions`,`bbt.bb_instructions`] >> simp[]) >>
  qexists_tac `indices` >> simp[] >> rpt strip_tac >>
  ` (concretize_inst_with_positions (lp (LAST h).po_fn)
      (EL k bb.bb_instructions)).inst_opcode = NOP` by
    (irule ptr_ledger_alignment_gap >>
     qexistsl_tac [`indices`,`SUC (LAST ht).po_state.vs_inst_idx`,`bbt.bb_instructions`] >>
     simp[] >> decide_tac) >>
  `k < LENGTH bb.bb_instructions` by
    (drule ptr_ledger_alignment_cursor >> strip_tac >>
     `EL (SUC (LAST ht).po_state.vs_inst_idx) indices < LENGTH bb.bb_instructions` by
       (qpat_x_assum `!j. j < LENGTH bbt.bb_instructions ==> _`
          (qspec_then `SUC (LAST ht).po_state.vs_inst_idx` mp_tac) >> simp[]) >> decide_tac) >>
  drule_all ptr_positioned_block_nop_iff >> simp[]
QED
Finalise ptr_paired_prefix_mload
