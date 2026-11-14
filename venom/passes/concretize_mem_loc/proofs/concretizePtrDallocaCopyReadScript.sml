Theory concretizePtrDallocaCopyRead
Ancestors
  concretizePtrPairedPrefix
  concretizePtrDallocaReadChannels concretizePtrMcopyEndpoint concretizePtrMloadEndpoint
  concretizePtrDallocaEarlierRead concretizePtrDallocaMemoryProbe
  ptrDiscipline memLocDefs list finite_map words arithmetic pred_set

Theorem ptr_dalloca_mcopy_read_mask_memory:
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
  endpoint.po_inst.inst_opcode = MCOPY /\ ptr_chrono_step C' at zt ==>
  ?dop sop nop d r dt rt n.
    endpoint.po_inst.inst_operands = [dop;sop;nop] /\
    eval_operand dop endpoint.po_state = SOME d /\
    eval_operand sop endpoint.po_state = SOME r /\
    eval_operand nop endpoint.po_state = SOME n /\
    eval_operand dop at.po_state = SOME dt /\
    eval_operand sop at.po_state = SOME rt /\
    eval_operand nop at.po_state = SOME n /\
    (!k. k < w2n n ==> w2n rt+k IN at.po_taint.t_mem ==>
      w2n r+k IN endpoint.po_taint.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_paired_mcopy_endpoint_inputs_memory >> strip_tac >>
  qexistsl [`dop`,`sop`,`nop`,`d`,`r`,`dt`,`rt`,`n`] >> simp[] >>
  rpt strip_tac >>
  `w2n n <> 0` by decide_tac >>
  `mem_read_ops endpoint.po_inst = SOME
    <|iao_ofst := sop; iao_size := SOME nop; iao_max_size := SOME nop|>` by
    simp[mem_read_ops_def] >>
  `(op_prov TG sop = NONE /\ rt = r /\
    (w2n r+w2n n <= lo \/ dyn_floor C vs <= w2n r)) \/
   (?v token aid b sz pa. sop = Var v /\ FLOOKUP TG v = SOME (token,aid) /\
    FLOOKUP endpoint.po_prov v = SOME (b,sz) /\
    FLOOKUP births (token,aid) = SOME (b,sz) /\
    FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
    b <= w2n r /\ w2n r+w2n n <= b+sz /\
    pa+sz < dimword(:256) /\ w2n rt = pa+(w2n r-b))` by
    (irule (SPEC_ALL ptr_paired_current_range_classification_memory
      |> Q.INST [`ops` |-> `<|iao_ofst := sop; iao_size := SOME nop; iao_max_size := SOME nop|>`]
      |> SIMP_RULE (srw_ss()) []) >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[])
  >- (gvs[] >> first_x_assum irule >> simp[] >> decide_tac)
  >- (gvs[] >> first_x_assum irule >> simp[] >> decide_tac) >>
  `w2n r+k = b+(w2n r+k-b) /\
   w2n rt+k = pa+(w2n r+k-b) /\ w2n r+k-b < sz` by decide_tac >>
  `pa+(w2n r+k-b) IN at.po_taint.t_mem` by metis_tac[ADD_COMM] >>
  `b+(w2n r+k-b) IN endpoint.po_taint.t_mem` suffices_by metis_tac[ADD_COMM] >>
  `pa+(w2n r+k-b) = k+(pa+w2n r)-b` by decide_tac >>
  drule ptr_dalloca_demanded_reflection_memory >> disch_then irule >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  simp[concretizeMemLocDefsTheory.inst_read_op_def, mem_read_ops_def] >>
  metis_tac[]
QED

Theorem ptr_dalloca_mcopy_read_mask:
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
  endpoint.po_inst.inst_opcode = MCOPY /\ ptr_chrono_step C' at zt ==>
  ?dop sop nop d r dt rt n.
    endpoint.po_inst.inst_operands = [dop;sop;nop] /\
    eval_operand dop endpoint.po_state = SOME d /\
    eval_operand sop endpoint.po_state = SOME r /\
    eval_operand nop endpoint.po_state = SOME n /\
    eval_operand dop at.po_state = SOME dt /\
    eval_operand sop at.po_state = SOME rt /\
    eval_operand nop at.po_state = SOME n /\
    (!k. k < w2n n ==> w2n rt+k IN at.po_taint.t_mem ==>
      w2n r+k IN endpoint.po_taint.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> drule ptr_paired_prefix_memory >> strip_tac >>
  drule_all ptr_dalloca_mcopy_read_mask_memory >> simp[]
QED
