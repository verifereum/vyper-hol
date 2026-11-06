Theory concretizePtrMloadRecovery
Ancestors concretizePtrMloadEndpoint concretizePtrFixedReadRecovery
  concretizePtrOwnedReadAudit concretizePtrStagePlacements concretizePtrImportOrigins
  concretizePtrOwnerFloor concretizePtrOwnerPath concretizePtrAllocationSize
  concretizePtrPairedPrefix concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrSourceOwnership
  concretizePtrHistoryObservation concretizePtrDeletedGapHistory ptrDiscipline o1PassContract unitShapeDefs
  unitTransformDefs unitLabelMapIdentity concretizeMemLocDefs memLocDefs
  o1ScheduleDecompHelpers venomWf venomInst finite_map words list arithmetic

Theorem ptr_paired_mload_masked_bytes:
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
  !j. j < 32 /\ w2n x + j NOTIN a.po_taint.t_mem ==>
    read_byte (w2n x + j) a.po_state.vs_memory =
      read_byte (w2n y + j) at.po_state.vs_memory
Proof
  strip_tac >>
  `~in_revert_forward a.po_fn a.po_state` by
    (drule_all ptr_paired_mload_endpoint_inputs >> strip_tac >> simp[]) >>
  `a.po_inst.inst_opcode <> ASSIGN` by simp[] >>
  drule_all ptr_paired_mload_address_classification >> strip_tac
  >- (rpt strip_tac >> gvs[] >>
      `j + w2n x < lo` by decide_tac >>
      drule ptr_paired_fixed_read_recovery >>
      disch_then (qspec_then `j + w2n x` mp_tac) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `ptr_stage_placements C' positions` by fs[ptr_paired_prefix_def] >>
  drule_all ptr_stage_placements_live_owner >> strip_tac >>
  `p = pa` by gvs[] >> gvs[] >>
  suspend "owned"
QED

Resume ptr_paired_mload_masked_bytes[owned]:
  `ptr_observation_reachable vs C a` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[]) >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by fs[ptr_observation_reachable_def] >>
  `MEM (ptr_owner_view d a).cf_fn C.ctx_functions` by
    (drule_all ptr_frame_sizes >> strip_tac >>
     Cases_on `d = LENGTH a.po_stack`
     >- simp[ptr_owner_view_def] >>
     `MEM (ptr_owner_view d a) a.po_stack` by
       (simp[ptr_owner_view_def] >> irule EL_MEM >> decide_tac) >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `lookup_function (ptr_owner_view d a).cf_fn.fn_name C.ctx_functions =
     SOME (ptr_owner_view d a).cf_fn` by
    (irule (iffRL lookup_function_member_iff) >>
     fs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  drule_all ptr_stage_lookup_origin >> strip_tac >> gvs[] >>
  suspend "recovery"
QED

Resume ptr_paired_mload_masked_bytes[recovery]:
  `vs.vs_allocas = FEMPTY` by
    fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions` by
    (gvs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
   EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_inst_wf_def, EVERY_MEM,
        fn_insts_MEM] >> metis_tac[]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `!obs. MEM obs h ==> access_ok lo obs.po_prov obs.po_fn obs.po_inst obs.po_state` by
    (drule ptr_structural_trace_source >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[EVERY_MEM] >>
     rpt strip_tac >> fs[ptr_observation_reachable_def, ptr_discipline_def] >>
     metis_tac[]) >>
  `allocas_from lo (ptr_owner_view d a).cf_state` by
    (drule_all ptr_reachable_owner_allocas_from >> simp[]) >>
  `lo <= b` by (fs[allocas_from_def] >> metis_tac[]) >>
  qabbrev_tac `k = w2n x - b + j` >>
  `b+k = j+w2n x /\ p+k = j+(p+w2n x)-b /\ k < sz /\ lo <= b+k` by
    (simp[Abbr `k`] >> decide_tac) >>
  `read_byte (b+k) a.po_state.vs_memory = read_byte (p+k) at.po_state.vs_memory`
    suffices_by simp[] >>
  `b+k NOTIN a.po_taint.t_mem /\ k+p = p+k` by simp[ADD_COMM] >>
  drule ptr_paired_owned_read_recovery >>
  simp[inst_read_op_def, mem_read_ops_def, ADD_COMM] >>
  metis_tac[]
QED

Finalise ptr_paired_mload_masked_bytes
