Theory concretizePtrIloadFamilyExecution
Ancestors concretizeMemLocDefs concretizePtrLoadTransport
  concretizePtrMloadExecution concretizePtrMloadEndpoint
  concretizePtrMloadRecovery concretizePtrMixedLoadTransport
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

Theorem ptr_paired_iload_execution_back:
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
  a.po_inst.inst_opcode = ILOAD /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  !fuel t'. step_inst fuel C' a.po_inst at.po_state = OK t' ==>
    ?s'. step_inst fuel C a.po_inst a.po_state = OK s' /\
      ptr_mixed_vars births positions (step_prov PT TG a.po_inst s')
        (step_taint a.po_inst a.po_state s' a.po_taint)
        a.po_fn at.po_fn s' t'
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
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]) >>
  `inst_wf a.po_inst /\ fn_shape_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  `?op out. a.po_inst.inst_operands = [op] /\
    a.po_inst.inst_outputs = [out]` by (gvs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  suspend "inputs"
QED

Resume ptr_paired_iload_execution_back[inputs]:
  `~retpc_var a.po_fn out` by
    (fs[fn_shape_ok_def, retpc_shape_ok_def] >>
     spose_not_then assume_tac >>
     qpat_x_assum `!inst x. MEM inst (fn_insts a.po_fn) /\ MEM x inst.inst_outputs /\ retpc_var a.po_fn x ==> _`
       (qspecl_then [`a.po_inst`,`out`] mp_tac) >> simp[]) >>
  `ptr_nonopaque_operand a.po_fn op` by
    (`EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
       (irule ptr_nonopaque_instruction_operands >> fs[fn_shape_ok_def]) >> gvs[]) >>
  `~is_label_operand op` by
    (`label_positions_ok a.po_inst` by
        (fs[fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def] >> metis_tac[]) >>
     gvs[label_positions_ok_def]) >>
  `ptrDiscipline$op_taint a.po_taint op = {}` by
    (`taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
       (fs[ptr_discipline_def] >> metis_tac[]) >>
     fs[taint_ok_def] >>
     qpat_x_assum `!op. MEM op _ /\ _ ==> _`
       (qspec_then `op` mp_tac) >> gvs[]) >>
  `~in_revert_forward a.po_fn a.po_state` by suspend "nonrevert" >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
     a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> metis_tac[concretizePtrRequestHistoryTheory.ptr_history_content_labels]) >>
  rpt strip_tac >>
  `?y. eval_operand op at.po_state = SOME y` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def, AllCaseEqs()] >>
     metis_tac[]) >>
  `?x. eval_operand op a.po_state = SOME x` by
    (drule_all ptr_mixed_vars_eval_presence >>
     disch_then (qspec_then `op` mp_tac) >> simp[] >>
     Cases_on `eval_operand op a.po_state` >> gvs[]) >>
  `ptr_lookup_transport births positions (op_prov TG op) {}
     (SOME x) (SOME y)` by
    (drule_all ptr_mixed_vars_eval >> simp[]) >>
  suspend "read"
QED

Resume ptr_paired_iload_execution_back[nonrevert]:
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

Resume ptr_paired_iload_execution_back[read]:
  `!j. j < 32 /\ w2n x + j NOTIN a.po_taint.t_mem ==>
    read_byte (w2n x+j) a.po_state.vs_memory =
      read_byte (w2n y+j) at.po_state.vs_memory` by
    (gen_tac >> strip_tac >>
     irule (Q.INST [`ops` |-> `<|iao_ofst := op; iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w)|>`]
       (SPEC_ALL ptr_paired_read_range_masked_bytes) |> SIMP_RULE (srw_ss()) []) >>
     rpt (goal_assum (drule_at Any)) >>
     simp[mem_read_ops_def, inst_read_op_def, source_memory_read_ranges_def] >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `word_agree_except (mem_word_taint a.po_taint.t_mem (w2n x))
    (mload (w2n x) a.po_state) (mload (w2n y) at.po_state)` by
    (irule ptr_mload_masked_value >> simp[]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def,
       eval_operands_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  irule ptr_mixed_vars_update >>
  simp[step_prov_def, out_prov_def, step_taint_def, out_taint_def,
       set_prov_def, set_var_taint_def, op_taint_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  simp[ptr_value_transport_def] >>
  fs[ptr_mixed_vars_def, ptrDisciplineTheory.op_taint_def] >>
  metis_tac[]
QED

Finalise ptr_paired_iload_execution_back
