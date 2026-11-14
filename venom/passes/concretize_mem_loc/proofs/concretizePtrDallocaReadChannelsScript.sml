Theory concretizePtrDallocaReadChannels
Ancestors
  concretizePtrPairedPrefix
  concretizePtrDallocaOwnedReflection concretizePtrDallocaDemandBoundary
  concretizePtrDallocaWriterProbe concretizePtrMloadEndpoint
  concretizePtrDallocaEarlierRead concretizePtrDallocaMemoryProbe
  ptrDiscipline memLocDefs list finite_map words arithmetic pred_set

Theorem ptr_dalloca_demanded_reflection_memory:
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP TG v = SOME (token,aid) /\
  FLOOKUP endpoint.po_prov v = SOME (b,sz) /\
  FLOOKUP births (token,aid) = SOME (b,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\ k < sz /\
  ~in_revert_forward endpoint.po_fn endpoint.po_state /\
  endpoint.po_inst.inst_opcode <> ASSIGN /\
  MEM (Var v) endpoint.po_inst.inst_operands /\
  (inst_read_op endpoint.po_inst = SOME (Var v) \/ endpoint.po_inst.inst_opcode = INVOKE) /\
  (!j r op. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) ==>
  pa+k IN at.po_taint.t_mem ==> b+k IN endpoint.po_taint.t_mem
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> strip_tac >>
  irule ptr_dalloca_owned_demand_reflection_memory >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `w < LENGTH h-1` by
    (drule_all ptr_dalloca_demand_writer_index >> simp[]) >>
  `pa+k NOTIN at.po_taint.t_mem` suffices_by simp[] >>
  irule ptr_dalloca_protected_writer_demand_memory >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]
QED

Theorem ptr_dalloca_demanded_reflection:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP TG v = SOME (token,aid) /\
  FLOOKUP endpoint.po_prov v = SOME (b,sz) /\
  FLOOKUP births (token,aid) = SOME (b,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\ k < sz /\
  ~in_revert_forward endpoint.po_fn endpoint.po_state /\
  endpoint.po_inst.inst_opcode <> ASSIGN /\
  MEM (Var v) endpoint.po_inst.inst_operands /\
  (inst_read_op endpoint.po_inst = SOME (Var v) \/ endpoint.po_inst.inst_opcode = INVOKE) /\
  (!j r op. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) ==>
  pa+k IN at.po_taint.t_mem ==> b+k IN endpoint.po_taint.t_mem
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> drule ptr_paired_prefix_memory >> strip_tac >>
  strip_tac >> drule_all ptr_dalloca_demanded_reflection_memory >> simp[]
QED

Theorem ptr_dalloca_mload_read_mask_memory:
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  (!j r op. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) /\
  (!a. a < lo ==> a IN at.po_taint.t_mem ==> a IN endpoint.po_taint.t_mem) /\
  (!a. dyn_floor C vs <= a ==> a IN at.po_taint.t_mem ==> a IN endpoint.po_taint.t_mem) /\
  endpoint.po_inst.inst_opcode = MLOAD /\ ptr_chrono_step C' at zt ==>
  ?op x y. endpoint.po_inst.inst_operands = [op] /\
    eval_operand op endpoint.po_state = SOME x /\
    eval_operand op at.po_state = SOME y /\
    mem_word_taint at.po_taint.t_mem (w2n y) SUBSET
      mem_word_taint endpoint.po_taint.t_mem (w2n x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_paired_mload_endpoint_inputs_memory >> strip_tac >>
  qexistsl [`op`,`x`,`y`] >> simp[] >>
  drule_all ptr_paired_mload_address_classification_memory >> strip_tac
  >- (gvs[mem_word_taint_def, SUBSET_DEF] >> rpt strip_tac >>
      first_x_assum irule >> simp[] >> decide_tac)
  >- (gvs[mem_word_taint_def, SUBSET_DEF] >> rpt strip_tac >>
      first_x_assum irule >> simp[] >> decide_tac) >>
  simp[mem_word_taint_def, SUBSET_DEF] >> rpt strip_tac >>
  rename1 `off < 32` >>
  `w2n x+off = b+(w2n x+off-b) /\
   w2n y+off = pa+(w2n x+off-b) /\ w2n x+off-b < sz` by decide_tac >>
  `pa+(w2n x+off-b) = pa+(off+w2n x)-b` by decide_tac >>
  `pa+(w2n x+off-b) IN at.po_taint.t_mem` by metis_tac[] >>
  `b+(w2n x+off-b) IN endpoint.po_taint.t_mem` suffices_by
    metis_tac[ADD_COMM] >>
  drule ptr_dalloca_demanded_reflection_memory >> disch_then irule >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  simp[concretizeMemLocDefsTheory.inst_read_op_def, mem_read_ops_def] >>
  metis_tac[ADD_ASSOC, ADD_COMM]
QED

Theorem ptr_dalloca_mload_read_mask:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  (!j r op. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) /\
  (!a. a < lo ==> a IN at.po_taint.t_mem ==> a IN endpoint.po_taint.t_mem) /\
  (!a. dyn_floor C vs <= a ==> a IN at.po_taint.t_mem ==> a IN endpoint.po_taint.t_mem) /\
  endpoint.po_inst.inst_opcode = MLOAD /\ ptr_chrono_step C' at zt ==>
  ?op x y. endpoint.po_inst.inst_operands = [op] /\
    eval_operand op endpoint.po_state = SOME x /\
    eval_operand op at.po_state = SOME y /\
    mem_word_taint at.po_taint.t_mem (w2n y) SUBSET
      mem_word_taint endpoint.po_taint.t_mem (w2n x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> drule ptr_paired_prefix_memory >> strip_tac >>
  drule_all ptr_dalloca_mload_read_mask_memory >> simp[]
QED
