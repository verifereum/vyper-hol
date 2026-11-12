Theory concretizePtrMloadRecovery
Ancestors concretizePtrMloadEndpoint concretizePtrFixedReadRecovery
  concretizePtrOwnedReadAudit concretizePtrStagePlacements concretizePtrImportOrigins
  concretizePtrOwnerFloor concretizePtrOwnerPath concretizePtrAllocationSize
  concretizePtrPairedPrefix concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrSourceOwnership
  concretizePtrHistoryObservation concretizePtrDeletedGapHistory ptrDiscipline o1PassContract unitShapeDefs
  unitTransformDefs unitLabelMapIdentity concretizeMemLocDefs memLocDefs
  o1ScheduleDecompHelpers venomWf venomInst finite_map words list arithmetic contextCodegenRel

Theorem ptr_paired_read_range_masked_bytes:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ eom <= w2n vs.vs_initial_fmp /\
  ~in_revert_forward a.po_fn a.po_state /\ a.po_inst.inst_opcode <> ASSIGN /\
  mem_read_ops a.po_inst = SOME ops /\ inst_read_op a.po_inst = SOME ops.iao_ofst /\
  MEM ops.iao_ofst a.po_inst.inst_operands /\
  eval_operand ops.iao_ofst a.po_state = SOME x /\
  eval_operand ops.iao_ofst at.po_state = SOME y /\
  MEM (w2n x,n) (source_memory_read_ranges a.po_inst a.po_state) /\
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) ==>
  !j. j < n /\ w2n x + j NOTIN a.po_taint.t_mem ==>
    read_byte (w2n x + j) a.po_state.vs_memory =
      read_byte (w2n y + j) at.po_state.vs_memory
Proof
  cheat
QED

Theorem ptr_paired_mload_masked_bytes:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ eom <= w2n vs.vs_initial_fmp /\
  a.po_inst.inst_opcode = MLOAD /\ ptr_chrono_step C' at zt /\
  a.po_inst.inst_operands = [op] /\
  eval_operand op a.po_state = SOME x /\ eval_operand op at.po_state = SOME y ==>
  !j. j < 32 /\ w2n x + j NOTIN a.po_taint.t_mem ==>
    read_byte (w2n x + j) a.po_state.vs_memory =
      read_byte (w2n y + j) at.po_state.vs_memory
Proof
  strip_tac >>
  drule_all ptr_paired_mload_endpoint_inputs >>
  disch_then (qx_choose_then `op0` (qx_choose_then `out` (qx_choose_then `x0`
    (qx_choose_then `y0` (map_every assume_tac o CONJUNCTS))))) >>
  gnvs[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`ops` |-> `<|iao_ofst := op; iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w)|>`]
    (SPEC_ALL ptr_paired_read_range_masked_bytes) |> SIMP_RULE (srw_ss()) [ADD_COMM]) >>
  rpt (goal_assum (drule_at Any)) >>
  simp[mem_read_ops_def, inst_read_op_def, source_memory_read_ranges_def] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED
