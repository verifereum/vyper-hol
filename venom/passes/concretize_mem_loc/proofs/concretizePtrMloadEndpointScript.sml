Theory concretizePtrMloadEndpoint
Ancestors concretizePtrMstoreProducer concretizePtrMloadIntegrationAudit
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

Theorem ptr_paired_mload_endpoint_inputs:
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
  ?op out x y.
    a.po_inst.inst_operands = [op] /\ a.po_inst.inst_outputs = [out] /\
    ((?v. op = Var v) \/ (?w. op = Lit w)) /\
    ~retpc_var a.po_fn out /\ ptr_nonopaque_operand a.po_fn op /\
    eval_operand op a.po_state = SOME x /\
    eval_operand op at.po_state = SOME y /\
    ptrDiscipline$op_taint a.po_taint op = {} /\
    ptr_lookup_transport births positions (op_prov TG op) {}
      (SOME x) (SOME y) /\
    ~in_revert_forward a.po_fn a.po_state
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

Resume ptr_paired_mload_endpoint_inputs[inputs]:
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
  suspend "evaluations"
QED

Resume ptr_paired_mload_endpoint_inputs[evaluations]:
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
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def, AllCaseEqs()] >>
  strip_tac >> suspend "transport"
QED

Resume ptr_paired_mload_endpoint_inputs[nonrevert]:
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

Resume ptr_paired_mload_endpoint_inputs[transport]:
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
     a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
    fs[ptr_paired_sample_def, ptr_core_shared_def, ptr_shared_fields_def] >>
  drule_all ptr_mixed_vars_eval_presence >>
  disch_then (qspec_then `op` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `eval_operand op a.po_state` >> gvs[] >>
  `ptr_lookup_transport births positions (op_prov TG op) {}
     (eval_operand op a.po_state) (eval_operand op at.po_state)` by
    (drule_all ptr_mixed_vars_eval >> simp[]) >>
  gvs[] >>
  Cases_on `op` >> gvs[is_label_operand_def]
QED

Finalise ptr_paired_mload_endpoint_inputs

Theorem ptr_paired_read_range_classification:
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
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  ~in_revert_forward a.po_fn a.po_state /\
  mem_read_ops a.po_inst = SOME ops /\
  eval_operand ops.iao_ofst a.po_state = SOME x /\
  eval_operand ops.iao_ofst at.po_state = SOME y /\
  MEM (w2n x,n) (source_memory_read_ranges a.po_inst a.po_state) /\ n <> 0 /\
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) ==>
  (op_prov TG ops.iao_ofst = NONE /\ y = x /\ w2n x + n <= lo) \/
  (?v token aid b sz pa. ops.iao_ofst = Var v /\ FLOOKUP TG v = SOME (token,aid) /\
    FLOOKUP a.po_prov v = SOME (b,sz) /\
    FLOOKUP births (token,aid) = SOME (b,sz) /\
    FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
    b <= w2n x /\ w2n x + n <= b+sz /\
    pa+sz < dimword(:256) /\ w2n y = pa + (w2n x-b))
Proof
  strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (gvs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  drule_all ptr_source_ownership_prov_erases >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `access_ok lo a.po_prov a.po_fn a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  Cases_on `op_prov a.po_prov ops.iao_ofst = NONE /\ w2n x + n <= lo`
  >- (disj1_tac >>
      `op_prov TG ops.iao_ofst = NONE` by
        (Cases_on `ops.iao_ofst` >> gvs[op_prov_def] >>
         fs[ptr_ledger_erases_def] >>
         Cases_on `FLOOKUP TG s` >> gvs[] >> metis_tac[flookup_thm]) >>
      gvs[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]) >>
  disj2_tac >>
  qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
  simp[access_ok_def] >> strip_tac >>
  qpat_x_assum `!off len. MEM _ (source_memory_read_ranges _ _) /\ _ ==> _`
    (qspecl_then [`w2n x`,`n`] mp_tac) >>
  simp[] >>
  (impl_tac >- (rpt strip_tac >> gvs[] >> decide_tac)) >> strip_tac >>
  gvs[] >>
  `?token aid. FLOOKUP TG v = SOME (token,aid)` by
    (fs[ptr_ledger_erases_def] >>
     Cases_on `FLOOKUP TG v` >> gvs[] >> PairCases_on `x'` >> metis_tac[]) >>
  `FLOOKUP births (token,aid) = SOME (b,sz)` by
    (fs[ptr_ledger_erases_def] >>
     qpat_x_assum `!v. FLOOKUP a.po_prov v = _` (qspec_then `v` mp_tac) >> simp[]) >>
  `?pa. FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
    y = x - n2w b + n2w pa` by
    gvs[ptr_lookup_transport_def, ptr_value_transport_def, op_prov_def] >>
  `ptr_stage_placements C' positions` by fs[ptr_paired_prefix_def] >>
  drule_all ptr_stage_placements_strict_bound >> strip_tac >>
  `w2n y = pa + (w2n x - b)` by
    (irule ptr_closed_relocation_value >> simp[] >>
     qexists_tac `sz` >> simp[]) >>
  qexistsl_tac [`token`,`aid`,`pa`] >> simp[] >> decide_tac
QED

Theorem ptr_paired_mload_address_classification:
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
  a.po_inst.inst_opcode = MLOAD /\ ptr_chrono_step C' at zt /\
  a.po_inst.inst_operands = [op] /\
  eval_operand op a.po_state = SOME x /\ eval_operand op at.po_state = SOME y ==>
  (op_prov TG op = NONE /\ y = x /\ w2n x + 32 <= lo) \/
  (?v token aid b sz pa. op = Var v /\ FLOOKUP TG v = SOME (token,aid) /\
    FLOOKUP a.po_prov v = SOME (b,sz) /\
    FLOOKUP births (token,aid) = SOME (b,sz) /\
    FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
    b <= w2n x /\ w2n x + 32 <= b+sz /\
    pa+sz < dimword(:256) /\ w2n y = pa + (w2n x-b))
Proof
  strip_tac >>
  drule_all ptr_paired_mload_endpoint_inputs >>
  disch_then (qx_choose_then `op0` (qx_choose_then `out` (qx_choose_then `x0`
    (qx_choose_then `y0` (map_every assume_tac o CONJUNCTS))))) >>
  `ptr_lookup_transport births positions (op_prov TG op) {} (SOME x) (SOME y) /\
   ~in_revert_forward a.po_fn a.po_state` by gvs[] >>
  gnvs[] >>
  irule (Q.INST [`ops` |-> `<|iao_ofst := op; iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w)|>`]
    (SPEC_ALL ptr_paired_read_range_classification) |> SIMP_RULE (srw_ss()) []) >>
  rpt (goal_assum (drule_at Any)) >>
  simp[mem_read_ops_def, source_memory_read_ranges_def] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Finalise ptr_paired_mload_address_classification
