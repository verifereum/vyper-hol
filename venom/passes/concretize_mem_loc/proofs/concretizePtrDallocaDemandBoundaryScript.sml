Theory concretizePtrDallocaDemandBoundary
Ancestors
  concretizePtrDallocaMemoryProbe concretizePtrDallocaEarlierRead
  concretizePtrDallocaWriterGeometry concretizePtrDallocaWriterProbe
  concretizePtrDemandWriteExclusion concretizePtrStructuralTrace
  concretizePtrHistoricalWriteExclusion
  concretizePtrStructuralTranscript concretizePtrPairedPrefix
  concretizePtrChronologicalHistory concretizeAllocationFree ptrDisciplineEmptyTaint
  ptrDiscipline memLocDefs venomExecSemantics list finite_map words arithmetic pred_set

(* MCOPY's source is an actual read at the earlier writer, not merely a
   variable whose ownership tag has survived.  These facts are the domain
   of the recursive owned-byte premise. *)
Theorem ptr_dalloca_copy_read_demand_memory:
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H ws /\
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  q < LENGTH done /\ EL q done = w /\
  (EL w h).po_inst.inst_opcode = MCOPY /\
  (EL w h).po_inst.inst_operands = [dst;src;n] /\
  eval_operand src (EL w h).po_state = SOME x /\
  eval_operand src (EL q ht).po_state = SOME y /\
  eval_operand n (EL w h).po_state = SOME len /\ off < w2n len ==>
  w < LENGTH h-1 /\
  ~in_revert_forward (EL w h).po_fn (EL w h).po_state /\
  (EL w h).po_inst.inst_opcode <> ASSIGN /\
  ((w2n y+off = w2n x+off /\ w2n x+off < lo) \/
   (w2n y+off = w2n x+off /\ dyn_floor C vs <= w2n x+off) \/
   (?u tok id base size pos ix ts rw bw PTw TGw sw ew.
     EL w H = (ts,rw,bw,PTw,TGw,sw,ew) /\
     src = Var u /\ FLOOKUP TGw u = SOME (tok,id) /\
     MEM (Var u) (EL w h).po_inst.inst_operands /\
     inst_read_op (EL w h).po_inst = SOME (Var u) /\
     FLOOKUP (EL w h).po_prov u = SOME (base,size) /\
     FLOOKUP bw (tok,id) = SOME (base,size) /\
     FLOOKUP positions (Allocation id) = SOME (pos,size) /\
     ix < size /\ w2n x+off = base+ix /\ w2n y+off = pos+ix))
Proof
  strip_tac >>
  `~in_revert_forward (EL w h).po_fn (EL w h).po_state` by
    (fs[ptr_demand_interval_def] >>
     qpat_x_assum `!j. w <= j /\ j < LENGTH h ==> _`
       (qspec_then `w` mp_tac) >> simp[] >> decide_tac) >>
  drule_all ptr_dalloca_earlier_copy_read_memory >>
  simp[concretizeMemLocDefsTheory.inst_read_op_def, mem_read_ops_def] >> metis_tac[]
QED

Theorem ptr_dalloca_copy_read_demand:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  q < LENGTH done /\ EL q done = w /\
  (EL w h).po_inst.inst_opcode = MCOPY /\
  (EL w h).po_inst.inst_operands = [dst;src;n] /\
  eval_operand src (EL w h).po_state = SOME x /\
  eval_operand src (EL q ht).po_state = SOME y /\
  eval_operand n (EL w h).po_state = SOME len /\ off < w2n len ==>
  w < LENGTH h-1 /\
  ~in_revert_forward (EL w h).po_fn (EL w h).po_state /\
  (EL w h).po_inst.inst_opcode <> ASSIGN /\
  ((w2n y+off = w2n x+off /\ w2n x+off < lo) \/
   (w2n y+off = w2n x+off /\ dyn_floor C vs <= w2n x+off) \/
   (?u tok id base size pos ix ts rw bw PTw TGw sw ew.
     EL w H = (ts,rw,bw,PTw,TGw,sw,ew) /\
     src = Var u /\ FLOOKUP TGw u = SOME (tok,id) /\
     MEM (Var u) (EL w h).po_inst.inst_operands /\
     inst_read_op (EL w h).po_inst = SOME (Var u) /\
     FLOOKUP (EL w h).po_prov u = SOME (base,size) /\
     FLOOKUP bw (tok,id) = SOME (base,size) /\
     FLOOKUP positions (Allocation id) = SOME (pos,size) /\
     ix < size /\ w2n x+off = base+ix /\ w2n y+off = pos+ix))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> drule ptr_paired_prefix_memory >> strip_tac >>
  drule_all ptr_dalloca_copy_read_demand_memory >> simp[]
QED

Theorem ptr_dalloca_copy_writer_clean_demand_memory:
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H ws /\
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  q < LENGTH done /\ EL q done = w /\
  (EL w h).po_inst.inst_opcode = MCOPY /\
  (!j r a. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/
      (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\
    FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) ==>
  pa+k NOTIN (EL (SUC q) ht).po_taint.t_mem
Proof
  strip_tac >> drule_all ptr_dalloca_writer_updates_memory >> strip_tac >>
  drule_all ptr_dalloca_writer_forward_memory >> strip_tac >>
  `b+k NOTIN (EL (SUC w) h).po_taint.t_mem` by fs[ptr_demand_interval_def] >>
  `?dst src n. (EL w h).po_inst.inst_operands = [dst;src;n] /\
      ops.iao_ofst = dst /\ sizeop = n` by
    gvs[mem_write_ops_def, AllCaseEqs()] >>
  `?rx. eval_operand src (EL w h).po_state = SOME rx` by
    (qpat_x_assum `step_inst _ C _ _ = OK _` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >> metis_tac[]) >>
  `?ry. eval_operand src (EL q ht).po_state = SOME ry` by
    (qpat_x_assum `step_inst _ C' _ _ = OK _` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >> metis_tac[]) >>
  `eval_operand n (EL w h).po_state = SOME z` by metis_tac[] >>
  `w2n ry+off IN (EL q ht).po_taint.t_mem ==>
   w2n rx+off IN (EL w h).po_taint.t_mem` by
    (strip_tac >> drule_all ptr_dalloca_copy_read_demand_memory >>
     strip_tac >> metis_tac[]) >>
  gvs[step_taint_def, mem_taint_def, step_writes_def, written_taint_def] >> metis_tac[]
QED

Theorem ptr_dalloca_copy_writer_clean_demand:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  q < LENGTH done /\ EL q done = w /\
  (EL w h).po_inst.inst_opcode = MCOPY /\
  (!j r a. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/
      (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\
    FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) ==>
  pa+k NOTIN (EL (SUC q) ht).po_taint.t_mem
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> drule ptr_paired_prefix_memory >> strip_tac >>
  drule_all ptr_dalloca_copy_writer_clean_demand_memory >> simp[]
QED

Theorem ptr_dalloca_protected_writer_demand_memory:
  ptr_paired_memory_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H ws /\
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  (!q op. q < LENGTH done /\ EL q done = w ==>
    op_taint (EL q ht).po_taint op SUBSET op_taint (EL w h).po_taint op) /\
  (!j r a. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/
      (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\
    FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) ==>
  pa+k NOTIN at.po_taint.t_mem
Proof
  strip_tac >>
  drule ptr_paired_memory_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  Cases_on `ctx_has_dalloca C`
  >- (`?q. q < LENGTH done /\ EL q done = w` by
        (drule ptr_structural_trace_actual_writer_retained >>
         disch_then (qspecl_then [`w`,`b+k`] mp_tac) >>
         fs[ptr_demand_interval_def] >> metis_tac[]) >>
      `!op. op_taint (EL q ht).po_taint op SUBSET op_taint (EL w h).po_taint op` by
        metis_tac[] >>
      `pa+k NOTIN (EL (SUC q) ht).po_taint.t_mem` by
        (Cases_on `MEM (EL w h).po_inst.inst_opcode [MSTORE;ISTORE]`
         >- (drule_all ptr_dalloca_store_writer_clean_memory >> simp[]) >>
         Cases_on `(EL w h).po_inst.inst_opcode = MCOPY`
         >- (drule_all ptr_dalloca_copy_writer_clean_demand_memory >> simp[]) >>
         `~MEM (EL w h).po_inst.inst_opcode [MSTORE;ISTORE;MCOPY]` by fs[] >>
         drule_all ptr_dalloca_other_writer_observation_clean_memory >> simp[]) >>
      `eom <= w2n vs.vs_initial_fmp` by simp[] >>
      drule_all ptr_dalloca_protected_suffix_memory >> simp[]) >>
  `EVERY (\fn. EVERY (\inst. allocation_free_opcode inst.inst_opcode)
    (fn_insts fn)) C'.ctx_functions` by
    (drule_all concretize_stage_allocation_free >> simp[]) >>
  `ptr_observation_reachable vs C' at` by metis_tac[ptr_chrono_history_reachable] >>
  `vs.vs_allocas = FEMPTY` by fs[ptr_demand_interval_def] >>
  fs[ptr_observation_reachable_def] >>
  drule_all allocation_free_reachable_taint >> simp[taint_empty_def]
QED

Theorem ptr_dalloca_protected_writer_demand:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  (!q op. q < LENGTH done /\ EL q done = w ==>
    op_taint (EL q ht).po_taint op SUBSET op_taint (EL w h).po_taint op) /\
  (!j r a. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < LENGTH h-1 /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/
      (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\
    FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) ==>
  pa+k NOTIN at.po_taint.t_mem
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> drule ptr_paired_prefix_memory >> strip_tac >>
  drule_all ptr_dalloca_protected_writer_demand_memory >> simp[]
QED
