Theory concretizePtrParamProducer
Ancestors concretizePtrRequestHistory concretizePtrAssignProducer concretizePtrValueSelection
  concretizePtrOrdinaryNext concretizePtrOpaqueRetpc
  concretizeStepStructure concretizeStepShape
  concretizeStepRetpc concretizeStageShape concretizePtrValueTransport
  ptrDiscipline venomExecSemantics venomState venomInst finite_map words list rich_list
  concretizePtrPairedNextAttach concretizePtrPairedPrefix concretizePtrPairedFields
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrSourceOwnership concretizePtrChronologicalHistory
  concretizePtrAllocationSize concretizePtrDeletedGapHistory concretizePtrTaggedSupport
  concretizePtrLedgerProbe concretizePtrLedgerAlignment concretizePtrPrefixLedger
  concretizePtrSharedFields concretizePtrStagePlacements concretizePtrDeletedGaps
  concretizePtrExecutedCoverage o1PassContract o1ScheduleDecomp unitShapeDefs
  venomWf cfgWf unitLabelMapIdentity contextCodegenRel codegenRel frameViewFacts arithmetic

Theorem ptr_mixed_param_execution_back[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  ((PT = [] /\ s.vs_params = t.vs_params) \/
   ptr_args_transport births positions PT
     (REPLICATE (LENGTH s.vs_params) {}) s.vs_params t.vs_params) /\
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] /\ ~retpc_var f out /\
  step_inst fuel Ct inst t = OK t' ==>
  ?s'. step_inst 0 C inst s = OK s' /\
    ptr_mixed_vars births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) f g s' t'
Proof
  strip_tac >>
  `w2n idx < LENGTH s.vs_params /\ w2n idx < LENGTH t.vs_params` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     drule_all ptr_param_step >> disch_then (fn th => rewrite_tac[th]) >>
     IF_CASES_TAC >> gvs[] >>
     drule ptr_args_transport_lengths >> simp[]) >>
  `ptr_value_transport births positions
     (if w2n idx < LENGTH PT then EL (w2n idx) PT else NONE) {}
     (EL (w2n idx) s.vs_params) (EL (w2n idx) t.vs_params)` by
    (gvs[ptr_value_transport_refl] >>
     drule ptr_args_transport_lengths >> strip_tac >> simp[] >>
     drule_all ptr_args_transport_el >> simp[EL_REPLICATE]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  drule_all ptr_param_step >> disch_then (fn th => rewrite_tac[th]) >>
  simp[] >> strip_tac >> gvs[] >>
  drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  simp[step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, out_taint_def, set_var_taint_def, op_taint_def, eval_operand_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  Cases_on `if w2n idx < LENGTH PT then EL (w2n idx) PT else NONE` >>
  gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def]
QED

Theorem ptr_paired_prefix_param:
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
  a.po_inst.inst_opcode = PARAM /\ ptr_chrono_step C' at zt ==>
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
  `MEM a.po_inst (fn_insts a.po_fn) /\ inst_wf a.po_inst` by
    suspend "shape" >>
  `?idx out. a.po_inst.inst_operands = [Lit idx] /\ a.po_inst.inst_outputs = [out]` by
    (gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute, AllCaseEqs()] >> metis_tac[]) >>
  `~retpc_var a.po_fn out` by
    (irule noncopy_output_not_retpc >>
     conj_tac >- fs[EVERY_MEM] >> qexists_tac `a.po_inst` >> simp[]) >>
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
  >> simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()]
QED
Resume ptr_paired_prefix_param[shape]:
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def,
     wf_function_def, fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >> metis_tac[]
QED
Resume ptr_paired_prefix_param[successor]:
  `?post. step_inst 0 C a.po_inst a.po_state = OK post /\
     ptr_mixed_vars births positions (step_prov PT TG a.po_inst post)
       (step_taint a.po_inst a.po_state post a.po_taint)
       a.po_fn at.po_fn post s'` by
    (fs[ptr_paired_sample_def, ptr_paired_params_def] >>
     drule ptr_mixed_param_execution_back >> disch_then irule >> simp[] >>
     qpat_x_assum `step_inst fuel C' _ _ = OK _` mp_tac >>
     simp[step_inst_non_invoke]) >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    ( `EVERY bb_well_formed a.po_fn.fn_blocks` by
        (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
      `post.vs_current_bb = a.po_state.vs_current_bb` by
        (qpat_x_assum `step_inst 0 C _ _ = OK post` mp_tac >>
         drule_all ptr_param_step >> disch_then (fn th => rewrite_tac[th]) >>
         IF_CASES_TAC >> simp[update_var_def] >> strip_tac >> gvs[]) >>
      qpat_assum `active_inst a.po_fn a.po_inst a.po_state`
        (mp_then Any mp_tac ptr_ordinary_next_active) >>
      disch_then irule >> simp[is_terminator_def]) >>
  qabbrev_tac `z = ptr_ledger_next a i post` >> qexists_tac `z` >>
  suspend "assembly"
QED
Resume ptr_paired_prefix_param[assembly]:
  `ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  drule ptr_paired_stage_local_allocas >>
  disch_then (qspecl_then [`o1_walk_view rpolicy 2`,`rpolicy`] mp_tac) >>
  simp[] >> strip_tac >>
  `ptr_paired_sample positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    suspend "sample" >>
  `ptr_paired_params positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    suspend "params" >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, is_terminator_def,
       ptr_tagged_step_def, step_prov_def, out_prov_def,
       step_writes_def, source_memory_write_ranges_def, fixed_source_write_range_def,
       range_bytes_def] >>
  qpat_x_assum `step_inst 0 C _ _ = OK post` mp_tac >>
  qpat_x_assum `step_inst fuel C' _ _ = OK s'` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[update_var_def]
QED
Resume ptr_paired_prefix_param[sample]:
  qpat_x_assum `step_inst 0 C _ _ = OK post` mp_tac >>
  qpat_x_assum `step_inst fuel C' _ _ = OK s'` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  reverse conj_tac
  >- (fs[ptr_paired_sample_def] >>
      simp[step_taint_def, mem_taint_def, store_taint_def, adopt_reset_def,
           imm_taint_def, set_var_taint_def, GSYM update_var_def] >>
      irule ptr_history_content_masks >>
      qexists_tac `a.po_taint` >> simp[]) >>
  qpat_x_assum `ptr_mixed_vars _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `_.inst_opcode = PARAM` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> strip_tac >>
  qmatch_goalsub_abbrev_tac `step_prov PT TG _ ps` >>
  qmatch_goalsub_abbrev_tac `ptr_mixed_vars _ _ _ _ _ _ ps pt` >>
  simp[ptr_mixed_vars_def, ptr_opaque_env_def, lookup_var_def,
       step_prov_def, out_prov_def] >> metis_tac[]
QED
Resume ptr_paired_prefix_param[params]:
  qpat_x_assum `step_inst 0 C _ _ = OK post` mp_tac >>
  qpat_x_assum `step_inst fuel C' _ _ = OK s'` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  fs[ptr_paired_params_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def,
     update_var_def]
QED
Finalise ptr_paired_prefix_param
