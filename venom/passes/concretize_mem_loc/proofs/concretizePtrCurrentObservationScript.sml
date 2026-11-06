Theory concretizePtrCurrentObservation
Ancestors
  concretizePtrCurrentRangeTransport concretizePtrObservationInterface concretizePtrStageBounds
  concretizePtrForwardingTransport concretizePtrPairedPrefix
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrDeletedGapHistory concretizePtrChronologicalHistory
  concretizePtrSourceOwnership concretizePtrOwnershipErasure
  concretizePtrAllocationSize concretizePtrParamSupport
  concretizePtrPairedFields concretizePtrSharedFields
  concretizeStepStructure concretizeMemLocDefs
  venomExecProofs passSimulationDefs passSharedDefs unitLabelMapIdentity concretizePtrOpaqueRetpc
  ptrDiscipline unitMemInv unitShapeDefs venomWf o1PassContract
  contextCodegenRel codegenRel memLocDefs pointerConfinedDefs
  venomInst list finite_map pred_set words arithmetic

Theorem ptr_paired_current_static_bound:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C Ct /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom Ct = SOME eom /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions Ct.ctx_functions /\
  ptr_stage_placements Ct positions /\
  ptr_paired_prefix R lp positions lo vs C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst ==>
  in_revert_forward at.po_fn at.po_state \/
  (!off len.
    MEM (off,len) (source_memory_read_ranges at.po_inst at.po_state ++
                  source_memory_write_ranges at.po_inst at.po_state) ==>
    len = 0 \/ off + len <= eom)
Proof
  strip_tac >> Cases_on `in_revert_forward a.po_fn a.po_state`
  >- (disj1_tac >> drule_all ptr_paired_prefix_forwarding >> simp[]) >>
  disj2_tac >>
  Cases_on `a.po_inst.inst_opcode = ALLOCA`
  >- (gvs[concretize_inst_with_positions_def, AllCaseEqs()] >>
      qpat_x_assum `_ = at.po_inst`
        (mp_tac o AP_TERM ``\i:instruction. i.inst_opcode``) >>
      simp[mk_nop_inst_def, mk_assign_inst_def] >> strip_tac >>
      simp[source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `at.po_inst = a.po_inst` by metis_tac[concretize_positions_unchanged] >>
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
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]) >>
  `inst_wf a.po_inst /\ fn_shape_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
     a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
    fs[ptr_paired_sample_def, ptr_core_shared_def, ptr_shared_fields_def] >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (gvs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  drule_all ptr_source_ownership_prov_erases >> strip_tac >>
  suspend "range_supply"
QED

Resume ptr_paired_current_static_bound[range_supply]:
  markerLib.RESUME_TAC >> rpt disch_tac >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
   access_ok lo a.po_prov a.po_fn a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  qpat_assum `ptr_discipline _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_discipline_def] >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by fs[EVERY_MEM] >>
  `fn_ptr_ok P a.po_fn` by fs[EVERY_MEM] >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `FDOM a.po_prov SUBSET fn_pv P a.po_fn` by
    (fs[ptr_static_support_def, SUBSET_DEF, FLOOKUP_DEF] >>
     metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `opaque_use_ok a.po_fn /\ label_positions_ok a.po_inst` by
    (fs[fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def] >> metis_tac[]) >>
  qpat_x_assum `at.po_inst = a.po_inst` (fn th => rewrite_tac[th]) >>
  rpt gen_tac >> strip_tac >>
  Q.SUBGOAL_THEN `?mops ranges_s ranges_t.
     ((mops = mem_read_ops a.po_inst /\
       ranges_s = source_memory_read_ranges a.po_inst a.po_state /\
       ranges_t = source_memory_read_ranges a.po_inst at.po_state) \/
      (mops = mem_write_ops a.po_inst /\
       ranges_s = source_memory_write_ranges a.po_inst a.po_state /\
       ranges_t = source_memory_write_ranges a.po_inst at.po_state)) /\
     MEM (off,len) ranges_t`
    (qx_choose_then `mops` (qx_choose_then `ranges_s`
      (qx_choose_then `ranges_t` (map_every assume_tac o CONJUNCTS))))
  >- metis_tac[MEM_APPEND] >>
  suspend "range_bound"
QED

Resume ptr_paired_current_static_bound[range_bound]:
  markerLib.RESUME_TAC >> rpt disch_tac >>
  drule_all ptr_current_range_transport >>
  disch_then (qx_choose_then `off_s` strip_assume_tac)
  >- suspend "scalar_bound" >>
  suspend "descriptor_bound"
QED

Resume ptr_paired_current_static_bound[scalar_bound]:
  markerLib.RESUME_TAC >> rpt disch_tac >>
  Cases_on `len = 0` >- simp[] >>
  `off_s + len <= lo` by
    (Q.SUBGOAL_THEN
       `((ranges_s = source_memory_read_ranges a.po_inst a.po_state /\
          mops = mem_read_ops a.po_inst) \/
         (ranges_s = source_memory_write_ranges a.po_inst a.po_state /\
          mops = mem_write_ops a.po_inst))` assume_tac
     >- metis_tac[] >>
     drule_all ptr_access_range_classification >>
     strip_tac >> gvs[op_prov_def] >>
     qpat_x_assum `!ops'. _` (qspec_then `ops` mp_tac) >> simp[]) >>
  drule_all ptr_stage_fixed_region_bound >> simp[] >> decide_tac
QED

Resume ptr_paired_current_static_bound[descriptor_bound]:
  markerLib.RESUME_TAC >> rpt disch_tac >>
  Q.SUBGOAL_THEN
    `((mem_read_ops a.po_inst = SOME ops /\
       MEM (w2n x,len) (source_memory_read_ranges a.po_inst a.po_state)) \/
      (mem_write_ops a.po_inst = SOME ops /\
       MEM (w2n x,len) (source_memory_write_ranges a.po_inst a.po_state)))`
    assume_tac >- metis_tac[] >>
  drule_all ptr_paired_current_range_static_bound >> simp[]
QED

Finalise ptr_paired_current_static_bound
