Theory concretizePtrMcopyEndpoint
Ancestors concretizePtrMloadEndpoint concretizePtrWritePurity concretizePtrTaggedSupport
  concretizePtrMstoreProducer concretizePtrMloadIntegrationAudit
  concretizePtrOpaqueRetpc stackPlanGen stackPlanTypes
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrSourceOwnership
  concretizePtrChronologicalHistory concretizePtrAllocationSize
  ptrDiscipline passSimulationDefs venomExecProofs venomWf
  o1PassContract unitShapeDefs venomInst list
  concretizePtrDeletedGapHistory contextCodegenRel unitLabelMapIdentity
  concretizePtrLedgerAlignment concretizePtrPrefixLedger concretizePtrSharedFields
  concretizePtrValueTransport concretizeStepStructure venomExecSemantics venomState
  arithmetic concretizePtrPairedFields finite_map words memLocDefs
  concretizePtrHistoricalPlacement concretizePtrPlacementBounds
  concretizePtrStagePlacements concretizePtrComparisonTransport

Theorem ptr_paired_mcopy_endpoint_inputs:
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
  a.po_inst.inst_opcode = MCOPY /\ ptr_chrono_step C' at zt ==>
  ?dop sop nop d r dt rt n.
    a.po_inst.inst_operands = [dop;sop;nop] /\
    a.po_inst.inst_outputs = [] /\ at.po_inst = a.po_inst /\
    eval_operand dop a.po_state = SOME d /\
    eval_operand sop a.po_state = SOME r /\
    eval_operand nop a.po_state = SOME n /\
    eval_operand dop at.po_state = SOME dt /\
    eval_operand sop at.po_state = SOME rt /\
    eval_operand nop at.po_state = SOME n /\
    ptrDiscipline$op_taint a.po_taint dop = {} /\
    ptrDiscipline$op_taint a.po_taint sop = {} /\
    ptrDiscipline$op_taint a.po_taint nop = {} /\
    op_prov TG nop = NONE /\
    ptr_lookup_transport births positions (op_prov TG dop) {} (SOME d) (SOME dt) /\
    ptr_lookup_transport births positions (op_prov TG sop) {} (SOME r) (SOME rt) /\
    ~in_revert_forward a.po_fn a.po_state /\
    MEM (w2n r,w2n n) (source_memory_read_ranges a.po_inst a.po_state) /\
    (!fuel ctx. step_inst fuel ctx a.po_inst a.po_state =
      OK (mcopy (w2n d) (w2n r) (w2n n) a.po_state))
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
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]) >>
  `inst_wf a.po_inst /\ fn_shape_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  `?dop sop nop. a.po_inst.inst_operands = [dop;sop;nop] /\
    a.po_inst.inst_outputs = []` by (gvs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  suspend "inputs"
QED

Resume ptr_paired_mcopy_endpoint_inputs[inputs]:
  `~in_revert_forward a.po_fn a.po_state` by suspend "nonrevert" >>
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
  suspend "purity"
QED

Resume ptr_paired_mcopy_endpoint_inputs[nonrevert]:
  `ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `active_inst a.po_fn a.po_inst a.po_state` mp_tac >>
  simp[active_inst_def] >> strip_tac >>
  `lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> fs[fn_labels_def]) >>
  `get_instruction bb a.po_state.vs_inst_idx = SOME a.po_inst` by
    simp[get_instruction_def] >>
  simp[in_revert_forward_def] >> strip_tac >>
  drule_all memSafeRunTheory.revert_forward_at_opcode >> simp[]
QED

Resume ptr_paired_mcopy_endpoint_inputs[purity]:
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> fs[fn_shape_ok_def]) >>
  `ptrDiscipline$op_taint a.po_taint dop = {} /\
   ptrDiscipline$op_taint a.po_taint sop = {} /\
   ptrDiscipline$op_taint a.po_taint nop = {}` by
    (fs[taint_ok_def] >>
     qpat_x_assum `!op. MEM op _ /\ _ ==> _` mp_tac >> simp[] >> metis_tac[]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `fn_ptr_ok P a.po_fn` by fs[EVERY_MEM] >>
  `EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, fn_inst_wf_def, EVERY_MEM,
        fn_insts_MEM] >> metis_tac[]) >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `!x. x IN FDOM TG ==> x IN fn_pv P a.po_fn` by
    (rpt strip_tac >>
     `?tag. FLOOKUP TG x = SOME tag` by metis_tac[FLOOKUP_DEF] >>
     drule_all ptr_source_tagged_var_support >> simp[]) >>
  `mem_write_ops a.po_inst = SOME
     <|iao_ofst := dop; iao_size := SOME nop; iao_max_size := SOME nop|>` by
    simp[mem_write_ops_def] >>
  `op_prov TG nop = NONE` by
    (drule ptr_write_max_size_no_provenance >> simp[] >>
     disch_then drule >> simp[]) >>
  suspend "evaluations"
QED

Resume ptr_paired_mcopy_endpoint_inputs[evaluations]:
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  strip_tac >> suspend "transport"
QED

Resume ptr_paired_mcopy_endpoint_inputs[transport]:
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
     a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
    fs[ptr_paired_sample_def, ptr_core_shared_def, ptr_shared_fields_def] >>
  `!op. MEM op [dop;sop;nop] ==>
     ptr_lookup_transport births positions (op_prov TG op)
       (ptrDiscipline$op_taint a.po_taint op)
       (eval_operand op a.po_state) (eval_operand op at.po_state)` by
    (rpt strip_tac >> irule ptr_mixed_vars_eval >>
     simp[] >> qexistsl_tac [`a.po_fn`,`at.po_fn`] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `ptr_lookup_transport births positions (op_prov TG dop) {}
     (eval_operand dop a.po_state) (SOME dst) /\
   ptr_lookup_transport births positions (op_prov TG sop) {}
     (eval_operand sop a.po_state) (SOME src) /\
   ptr_lookup_transport births positions NONE {}
     (eval_operand nop a.po_state) (SOME sz)` by
    (qpat_x_assum `!op. MEM op [dop;sop;nop] ==> _` mp_tac >>
     simp[] >> metis_tac[]) >>
  Cases_on `eval_operand dop a.po_state` >>
  fs[ptr_lookup_transport_def] >>
  Cases_on `eval_operand sop a.po_state` >>
  fs[ptr_lookup_transport_def] >>
  Cases_on `eval_operand nop a.po_state` >>
  fs[ptr_lookup_transport_def, ptr_value_transport_scalar_empty] >>
  simp[source_memory_read_ranges_def, step_inst_non_invoke, step_inst_base_def] >>
  metis_tac[]
QED

Finalise ptr_paired_mcopy_endpoint_inputs
