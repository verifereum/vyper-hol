Theory o1CodeEndConcretizeObservation
Ancestors
  o1CodeEndConcretizeRead o1LabelFlowMiddleConcretize
  o1LabelFlowMiddleFmp concretizeStageStatic
  concretizePtrCurrentObservation concretizePtrUniversalExtension
  concretizePtrFrameRetpcShape concretizePtrCoverageStaticMem
  o1PassContract list venomWf passSimulationDefs lowerDloadRevertSuffix
  venomExecProofs venomExecSemantics venomInst codegenRel contextCodegenRel
  stepWriteFootprintBase concretizePtrOperationalOpcodes
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrSourceOwnership
  concretizePtrOwnershipErasure concretizePtrDeletedGapHistory
  concretizePtrAllocationSize concretizeStepStructure concretizeMemLocDefs
  ptrDiscipline unitShapeDefs passSharedDefs unitLabelMapIdentity
  concretizePtrParamSupport finite_map pred_set
  concretizePtrPairedFields lowerDloadReachability
  concretizePtrStagePairedBridge concretizePtrHistoryCoverage
  concretizePtrCoverageStaticMemReachability concretizePtrChronologicalHistory

Theorem concretize_codecopy_reflect:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C Ct /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ o1_inv D 2 C vs /\
  max_live_eom Ct = SOME eom /\ raw_reachable vs Ct ft j t /\
  j.inst_opcode = CODECOPY /\ j.inst_operands = [dst; Var x; sz] /\
  code_end_var ft x /\ eval_operand (Var x) t = SOME w ==>
  ?f i s. raw_reachable vs C f i s /\ i.inst_opcode = CODECOPY /\
    i.inst_operands = [dst; Var x; sz] /\ code_end_var f x /\
    eval_operand (Var x) s = SOME w /\ s.vs_labels = t.vs_labels
Proof
  rpt gen_tac >> strip_tac >>
  fs[o1_inv_def, o1_src_inv_def] >>
  `EVERY all_reachable C.ctx_functions /\
   EVERY fn_defs_reach_uses C.ctx_functions` by
    (fs[EVERY_MEM, make_ssa_input_ok_def] >> metis_tac[]) >>
  `ctx_inst_ids_distinct C` by fs[o1_ctx_shape_def] >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] ptr_stage_paired_bridge) >>
  disch_then (qx_choosel_then [`R`,`lp`,`positions`] strip_assume_tac) >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] ptr_stage_frame_retpc_shape) >>
  strip_tac >>
  `EVERY (\f. fn_inst_wf f /\ unitShapeDefs$retpc_shape_ok f /\ opaque_use_ok f /\
     first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
     ALL_DISTINCT (fn_labels f) /\
     (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
       IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `C.ctx_entry = Ct.ctx_entry` by fs[ctx_pass_stage_def] >>
  `vs.vs_vars = FEMPTY` by
    gvs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def] >>
  `!ht at. ptr_chrono_history vs Ct ht at ==>
     (?h a done tokens registry births PT TG saved entries H calls ws.
       ptr_paired_prefix R lp positions lo vs C Ct h a ht at done tokens registry births PT TG saved entries H calls ws /\
       a.po_inst.inst_opcode <> NOP /\
       at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst) \/
     (?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
       revert_forward_pair bb i j /\
       i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j)` by
    (match_mp_tac ptr_paired_history_coverage >> rpt conj_tac
     >~ [`ptr_chrono_step`]
     >- (rpt strip_tac >> drule_all ptr_paired_universal_extension >>
         disch_then ACCEPT_TAC) >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  drule ptr_reachable_has_chrono_history >> strip_tac >>
  qpat_x_assum `!ht at. _` drule >> strip_tac
  >- suspend "paired" >>
  suspend "corridor"
QED

Resume concretize_codecopy_reflect[paired]:
  markerLib.RESUME_TAC >> rpt disch_tac >>
  rename1 `ptr_paired_prefix R lp positions lo vs C Ct source_history a _ _ done tokens registry births PT TG saved entries H calls ws` >>
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
  `fn_shape_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `a.po_inst.inst_opcode <> ALLOCA` by
    (strip_tac >> gvs[concretize_inst_with_positions_def, AllCaseEqs(),
                     mk_nop_inst_def, mk_assign_inst_def, ptr_observe_def]) >>
  `j = a.po_inst` by
    (fs[ptr_observe_def] >> metis_tac[concretize_positions_unchanged]) >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn ft
     a.po_state t /\ a.po_state.vs_labels = t.vs_labels` by
    (fs[ptr_paired_sample_def, ptr_observe_def] >>
     metis_tac[concretizePtrRequestHistoryTheory.ptr_history_content_labels]) >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (gvs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  drule_all ptr_source_ownership_prov_erases >> strip_tac >>
  suspend "scalar"
QED

Resume concretize_codecopy_reflect[scalar]:
  markerLib.RESUME_TAC >> rpt disch_tac >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  qpat_assum `ptr_discipline _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_discipline_def] >>
  disch_then (qx_choose_then `P` strip_assume_tac o CONJUNCT2) >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by fs[EVERY_MEM] >>
  `fn_ptr_ok P a.po_fn` by fs[EVERY_MEM] >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `FDOM a.po_prov SUBSET fn_pv P a.po_fn` by
    (fs[ptr_static_support_def, SUBSET_DEF, FLOOKUP_DEF] >>
     metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `opaque_use_ok a.po_fn` by fs[fn_shape_ok_def] >>
  `eval_operand (Var x) a.po_state = eval_operand (Var x) t` by
    (irule code_end_concretize_read_value >>
     metis_tac[]) >>
  suspend "provenance"
QED

Resume concretize_codecopy_reflect[provenance]:
  markerLib.RESUME_TAC >> rpt disch_tac >>
  `code_end_var (concretize_function_with_positions (lp a.po_fn) a.po_fn) x` by
    (fs[ptr_paired_code_def, ptr_observe_def] >>
     metis_tac[code_end_var_same_blocks]) >>
  `code_end_var a.po_fn x` by metis_tac[concretize_code_end_backward] >>
  qexistsl [`a.po_fn`, `a.po_inst`, `a.po_state`] >>
  simp[] >>
  metis_tac[ld_frame_reachable_raw]
QED

Resume concretize_codecopy_reflect[corridor]:
  markerLib.RESUME_TAC >> rpt disch_tac >>
  gvs[ptr_observe_def] >>
  drule raw_reachable_active >>
  rewrite_tac[active_inst_def] >>
  disch_then (qx_choose_then `active_bb` strip_assume_tac) >>
  `MEM ft Ct.ctx_functions` by metis_tac[ptr_frame_context_membership] >>
  `ALL_DISTINCT (fn_labels ft)` by gvs[EVERY_MEM] >>
  `lookup_block t.vs_current_bb ft.fn_blocks = SOME active_bb` by
    (irule MEM_lookup_block >> fs[fn_labels_def]) >>
  `active_bb = bb` by metis_tac[optionTheory.SOME_11] >>
  `get_instruction bb t.vs_inst_idx = SOME j` by fs[get_instruction_def] >>
  drule_all ld_revert_pair_suffix_opcode >> simp[]
QED

Finalise concretize_codecopy_reflect
