Theory concretizePtrMixedAllocationPrefix
Ancestors
  concretizePtrMixedAllocationTransport concretizePtrPairedPrefix
  concretizePtrPairedFields concretizePtrStagePlacements concretizePtrAllocationSize
  concretizePtrExecutedCoverage
  concretizePtrStructuralTranscript concretizePtrChronologicalHistory
  concretizePtrStructuralTrace concretizePtrDeletedGapHistory removeUnusedSsaProofs
  concretizeStepStructure concretizeStepShape concretizeStepCallChecks
  concretizeStepRetpc concretizeStageShape
  o1PassContract stackPlanGen ptrDiscipline unitMemInv venomWf cfgWf
  o1ScheduleDecomp venomExecSemantics venomInst unitShapeDefs
  list finite_map words contextCodegenRel

Theorem ptr_paired_prefix_alloca_inputs:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode = ALLOCA /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  fn_inst_wf a.po_fn /\ retpc_shape_ok a.po_fn /\
  ptr_chrono_step C' at zt ==>
  ?sz out pos.
    a.po_inst.inst_operands = [Lit sz] /\
    a.po_inst.inst_outputs = [out] /\ ~retpc_var a.po_fn out /\
    FLOOKUP (lp a.po_fn) (Allocation a.po_inst.inst_id) = SOME pos /\
    FLOOKUP positions (Allocation a.po_inst.inst_id) = SOME (pos,w2n sz) /\
    (!base size. FLOOKUP a.po_state.vs_allocas a.po_inst.inst_id = SOME (base,size)
      ==> size = w2n sz)
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_placements >> strip_tac >>
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
    (qpat_x_assum `active_inst _ _ _` mp_tac >>
     simp[active_inst_def] >> strip_tac >>
     simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     qexists_tac `bb.bb_instructions` >> conj_tac
     >- (qexists_tac `bb` >> simp[]) >>
     qpat_x_assum `EL _ _ = a.po_inst` (SUBST1_TAC o SYM) >>
     irule EL_MEM >> simp[]) >>
  `inst_wf a.po_inst` by
    (qpat_x_assum `fn_inst_wf _` mp_tac >>
     qpat_x_assum `MEM a.po_inst (fn_insts _)` mp_tac >>
     simp[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[]) >>
  qpat_x_assum `inst_wf a.po_inst` mp_tac >>
  simp[inst_wf_def] >> strip_tac >>
  `?out. a.po_inst.inst_outputs = [out]` by
    (Cases_on `a.po_inst.inst_outputs` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  `~retpc_var a.po_fn out` by
    (strip_tac >> qpat_x_assum `retpc_shape_ok _` mp_tac >>
     pure_rewrite_tac[retpc_shape_ok_def] >>
     disch_then (mp_tac o cj 3) >>
     disch_then (qspecl_then [`a.po_inst`,`out`] mp_tac) >> simp[]) >>
  `fn_inst_ids_distinct a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `get_alloca_size a.po_fn (Allocation a.po_inst.inst_id) = w2n sz` by
    (irule ptr_alloca_inst_size >> simp[]) >>
  drule_all ptr_stage_alloca_mems >> strip_tac >>
  `FLOOKUP positions (Allocation a.po_inst.inst_id) = SOME (p,w2n sz)` by
    (fs[ptr_stage_placements_def] >> metis_tac[lookup_function_MEM]) >>
  `FLOOKUP (lp a.po_fn) (Allocation a.po_inst.inst_id) = SOME p` by
    (qpat_x_assum `ptr_paired_code _ _ _ _ _` mp_tac >>
     qpat_x_assum `MEM a.po_inst (fn_insts _)` mp_tac >>
     simp[ptr_paired_code_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     rpt strip_tac >> gvs[] >>
     first_x_assum (qspecl_then [`bb`,`a.po_inst`] mp_tac) >> simp[]) >>
  qexistsl_tac [`sz`,`out`,`p`] >> simp[] >>
  rpt strip_tac >> drule_all ptr_frame_current_allocation_size >> simp[]
QED
