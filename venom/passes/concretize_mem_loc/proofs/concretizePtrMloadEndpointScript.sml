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
  EVERY ssa_form C.ctx_functions /\
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
  cheat
QED

Theorem ptr_paired_current_range_classification:
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
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  eom <= w2n vs.vs_initial_fmp /\
  ~in_revert_forward a.po_fn a.po_state /\
  ((mem_read_ops a.po_inst = SOME ops /\
    MEM (w2n x,n) (source_memory_read_ranges a.po_inst a.po_state)) \/
   (mem_write_ops a.po_inst = SOME ops /\
    MEM (w2n x,n) (source_memory_write_ranges a.po_inst a.po_state))) /\
  eval_operand ops.iao_ofst a.po_state = SOME x /\
  eval_operand ops.iao_ofst at.po_state = SOME y /\ n <> 0 /\
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) ==>
  (op_prov TG ops.iao_ofst = NONE /\ y = x /\
    (w2n x + n <= lo \/ dyn_floor C vs <= w2n x)) \/
  (?v token aid b sz pa. ops.iao_ofst = Var v /\ FLOOKUP TG v = SOME (token,aid) /\
    FLOOKUP a.po_prov v = SOME (b,sz) /\
    FLOOKUP births (token,aid) = SOME (b,sz) /\
    FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
    b <= w2n x /\ w2n x + n <= b+sz /\
    pa+sz < dimword(:256) /\ w2n y = pa + (w2n x-b))
Proof
  cheat
QED

Theorem ptr_paired_read_range_classification:
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
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  eom <= w2n vs.vs_initial_fmp /\
  ~in_revert_forward a.po_fn a.po_state /\
  mem_read_ops a.po_inst = SOME ops /\
  eval_operand ops.iao_ofst a.po_state = SOME x /\
  eval_operand ops.iao_ofst at.po_state = SOME y /\
  MEM (w2n x,n) (source_memory_read_ranges a.po_inst a.po_state) /\ n <> 0 /\
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) ==>
  (op_prov TG ops.iao_ofst = NONE /\ y = x /\
    (w2n x + n <= lo \/ dyn_floor C vs <= w2n x)) \/
  (?v token aid b sz pa. ops.iao_ofst = Var v /\ FLOOKUP TG v = SOME (token,aid) /\
    FLOOKUP a.po_prov v = SOME (b,sz) /\
    FLOOKUP births (token,aid) = SOME (b,sz) /\
    FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
    b <= w2n x /\ w2n x + n <= b+sz /\
    pa+sz < dimword(:256) /\ w2n y = pa + (w2n x-b))
Proof
  strip_tac >> irule ptr_paired_current_range_classification >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  rpt (goal_assum (drule_at Any)) >> simp[]
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
  EVERY ssa_form C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ eom <= w2n vs.vs_initial_fmp /\
  a.po_inst.inst_opcode = MLOAD /\ ptr_chrono_step C' at zt /\
  a.po_inst.inst_operands = [op] /\
  eval_operand op a.po_state = SOME x /\ eval_operand op at.po_state = SOME y ==>
  (op_prov TG op = NONE /\ y = x /\
    (w2n x + 32 <= lo \/ dyn_floor C vs <= w2n x)) \/
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
