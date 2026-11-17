Theory concretizePtrDallocaMemorySteps
Ancestors
  concretizePtrChronologicalHistory concretizePtrLifetime concretizePtrDallocaStaticFresh
  concretizePtrDallocaActualWrites concretizePtrDallocaActualFresh
  concretizePtrDallocaHistoricalRead concretizePtrDallocaHistoricalPersistent
  concretizePtrDallocaIdentitySteps concretizeStepStructure
  concretizePtrPairedPrefix concretizePtrStructuralTranscript concretizePtrStructuralTrace
  lowerDloadPtrTaintBounds lowerDloadPtrScalar ptrDiscipline venomState venomInst
  venomExecSemantics codegenRel opcodeClass memLocDefs list pred_set

Theorem ptr_dalloca_actual_written_reflection_static:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ (o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs) /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  q < LENGTH done /\ a = EL (EL q done) h /\ target = EL q ht /\
  posts = (EL (SUC (EL q done)) h).po_state /\
  postt = (EL (SUC q) ht).po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  (i < lo \/ dyn_floor C vs <= i)
  /\ (!op. op_taint target.po_taint op SUBSET op_taint a.po_taint op) /\
  (a.po_inst.inst_opcode = MCOPY ==>
    ?dop sop nop d r dt rt n.
      a.po_inst.inst_operands = [dop;sop;nop] /\
      eval_operand dop a.po_state = SOME d /\
      eval_operand sop a.po_state = SOME r /\
      eval_operand nop a.po_state = SOME n /\
      eval_operand dop target.po_state = SOME dt /\
      eval_operand sop target.po_state = SOME rt /\
      eval_operand nop target.po_state = SOME n /\
      (!k. k < w2n n ==> w2n rt+k IN target.po_taint.t_mem ==>
        w2n r+k IN a.po_taint.t_mem)) /\
  i IN written_taint target.po_taint target.po_inst target.po_state ==>
  i IN written_taint a.po_taint a.po_inst a.po_state
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_dalloca_actual_event_context_static >> strip_tac >>
  `!op. op_taint a.po_taint op SUBSET {k | k < 32}` by
    (fs[ptr_observation_reachable_def] >>
     metis_tac[dload_reachable_op_taint_bound]) >>
  `!op. op_taint target.po_taint op SUBSET {k | k < 32}` by
    (gen_tac >> irule SUBSET_TRANS >>
     qexists `op_taint a.po_taint op` >> simp[]) >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  `SUC q < LENGTH ht` by fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  `ptr_chrono_step C' target (EL (SUC q) ht)` by
    (drule ptr_structural_trace_target >> strip_tac >>
     metis_tac[ptr_chrono_history_adjacent]) >>
  `i IN range_bytes (step_writes target.po_inst target.po_state postt)` by
    (drule_all ptr_dalloca_chrono_written_footprint >> simp[]) >>
  Q.SUBGOAL_THEN `i IN range_bytes (step_writes a.po_inst a.po_state posts) \/
    i IN range_bytes (step_writes target.po_inst target.po_state postt)` assume_tac
  >- simp[] >>
  drule_all ptr_dalloca_actual_write_descriptor_static >> strip_tac >>
  qpat_x_assum `target.po_inst = a.po_inst` (fn th => fs[th]) >>
  (mp_tac (Q.INST
     [`inst` |-> `a.po_inst`, `s` |-> `a.po_state`, `tn` |-> `a.po_taint`,
      `t` |-> `target.po_state`, `un` |-> `target.po_taint`]
     ptr_dalloca_identity_written) >>
   impl_tac
   >- (conj_tac
       >- (rpt gen_tac >> strip_tac >>
           gvs[mem_write_ops_def] >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
       rpt gen_tac >> strip_tac >>
       qpat_x_assum `a.po_inst.inst_opcode = MCOPY ==> _` mp_tac >>
       simp[] >> strip_tac >> gvs[mem_write_ops_def] >>
       rpt (goal_assum (drule_at Any)) >> simp[]) >>
   simp[])
QED

Theorem ptr_dalloca_actual_written_reflection:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  q < LENGTH done /\ a = EL (EL q done) h /\ target = EL q ht /\
  posts = (EL (SUC (EL q done)) h).po_state /\
  postt = (EL (SUC q) ht).po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  (i < lo \/ dyn_floor C vs <= i)
  /\ (!op. op_taint target.po_taint op SUBSET op_taint a.po_taint op) /\
  (a.po_inst.inst_opcode = MCOPY ==>
    ?dop sop nop d r dt rt n.
      a.po_inst.inst_operands = [dop;sop;nop] /\
      eval_operand dop a.po_state = SOME d /\
      eval_operand sop a.po_state = SOME r /\
      eval_operand nop a.po_state = SOME n /\
      eval_operand dop target.po_state = SOME dt /\
      eval_operand sop target.po_state = SOME rt /\
      eval_operand nop target.po_state = SOME n /\
      (!k. k < w2n n ==> w2n rt+k IN target.po_taint.t_mem ==>
        w2n r+k IN a.po_taint.t_mem)) /\
  i IN written_taint target.po_taint target.po_inst target.po_state ==>
  i IN written_taint a.po_taint a.po_inst a.po_state
Proof
  rpt gen_tac >> mp_tac (SPEC_ALL ptr_dalloca_actual_written_reflection_static) >>
  pure_rewrite_tac[o1PassContractTheory.o1_run_state_ok_def] >>
  tautLib.TAUT_TAC
QED

Theorem ptr_dalloca_actual_memory_next_static:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ (o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs) /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  q < LENGTH done /\ a = EL (EL q done) h /\ target = EL q ht /\
  posts = (EL (SUC (EL q done)) h).po_state /\
  postt = (EL (SUC q) ht).po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  (i < lo \/ dyn_floor C vs <= i)
  /\ (!op. op_taint target.po_taint op SUBSET op_taint a.po_taint op) /\
  (a.po_inst.inst_opcode = MCOPY ==>
    ?dop sop nop d r dt rt n.
      a.po_inst.inst_operands = [dop;sop;nop] /\
      eval_operand dop a.po_state = SOME d /\
      eval_operand sop a.po_state = SOME r /\
      eval_operand nop a.po_state = SOME n /\
      eval_operand dop target.po_state = SOME dt /\
      eval_operand sop target.po_state = SOME rt /\
      eval_operand nop target.po_state = SOME n /\
      (!k. k < w2n n ==> w2n rt+k IN target.po_taint.t_mem ==>
        w2n r+k IN a.po_taint.t_mem)) /\
  ~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE /\
  ~is_terminator target.po_inst.inst_opcode /\ target.po_inst.inst_opcode <> INVOKE /\
  (i IN target.po_taint.t_mem ==> i IN a.po_taint.t_mem) ==>
  i IN (EL (SUC q) ht).po_taint.t_mem ==>
  i IN (EL (SUC (EL q done)) h).po_taint.t_mem
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  `SUC q < LENGTH ht` by
    fs[ptr_paired_samples_def, ptr_sample_list_def, EVERY_EL] >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  `SUC (EL q done) < LENGTH h` by
    (drule_all ptr_structural_trace_nop_interval >> strip_tac >> decide_tac) >>
  `ptr_chrono_step C a (EL (SUC (EL q done)) h)` by
    (drule ptr_structural_trace_source >> strip_tac >>
     metis_tac[ptr_chrono_history_adjacent]) >>
  `ptr_chrono_step C' target (EL (SUC q) ht)` by
    (drule ptr_structural_trace_target >> strip_tac >>
     metis_tac[ptr_chrono_history_adjacent]) >>
  `(EL (SUC (EL q done)) h).po_taint.t_mem =
   (step_taint a.po_inst a.po_state posts a.po_taint).t_mem` by
    (mp_tac (Q.SPECL [`C`,`a`,`EL (SUC (EL q done)) h`]
       ptr_dalloca_chrono_ordinary_taint_fields) >> simp[]) >>
  `(EL (SUC q) ht).po_taint.t_mem =
   (step_taint target.po_inst target.po_state postt target.po_taint).t_mem` by
    (mp_tac (Q.SPECL [`C'`,`target`,`EL (SUC q) ht`]
       ptr_dalloca_chrono_ordinary_taint_fields) >> simp[]) >>
  `new_site_bytes target.po_state postt SUBSET new_site_bytes a.po_state posts` by
    (drule_all ptr_dalloca_actual_fresh_bytes >> simp[]) >>
  `(i IN range_bytes (step_writes a.po_inst a.po_state posts) <=>
    i IN range_bytes (step_writes target.po_inst target.po_state postt))` by
    (drule_all ptr_dalloca_actual_write_coverage_static >> simp[]) >>
  `i IN written_taint target.po_taint target.po_inst target.po_state ==>
   i IN written_taint a.po_taint a.po_inst a.po_state` by
    (strip_tac >> drule_all ptr_dalloca_actual_written_reflection_static >> simp[]) >>
  gvs[step_taint_def, mem_taint_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ptr_dalloca_actual_memory_next:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  q < LENGTH done /\ a = EL (EL q done) h /\ target = EL q ht /\
  posts = (EL (SUC (EL q done)) h).po_state /\
  postt = (EL (SUC q) ht).po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  (i < lo \/ dyn_floor C vs <= i)
  /\ (!op. op_taint target.po_taint op SUBSET op_taint a.po_taint op) /\
  (a.po_inst.inst_opcode = MCOPY ==>
    ?dop sop nop d r dt rt n.
      a.po_inst.inst_operands = [dop;sop;nop] /\
      eval_operand dop a.po_state = SOME d /\
      eval_operand sop a.po_state = SOME r /\
      eval_operand nop a.po_state = SOME n /\
      eval_operand dop target.po_state = SOME dt /\
      eval_operand sop target.po_state = SOME rt /\
      eval_operand nop target.po_state = SOME n /\
      (!k. k < w2n n ==> w2n rt+k IN target.po_taint.t_mem ==>
        w2n r+k IN a.po_taint.t_mem)) /\
  ~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE /\
  ~is_terminator target.po_inst.inst_opcode /\ target.po_inst.inst_opcode <> INVOKE /\
  (i IN target.po_taint.t_mem ==> i IN a.po_taint.t_mem) ==>
  i IN (EL (SUC q) ht).po_taint.t_mem ==>
  i IN (EL (SUC (EL q done)) h).po_taint.t_mem
Proof
  rpt gen_tac >> mp_tac (SPEC_ALL ptr_dalloca_actual_memory_next_static) >>
  pure_rewrite_tac[o1PassContractTheory.o1_run_state_ok_def] >>
  tautLib.TAUT_TAC
QED

Theorem ptr_dalloca_memory_steps_ordinary_static:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  q < LENGTH done /\ n0 = EL q done /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ (o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs) /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  (!j r op. j < n0 /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < n0 /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < n0 /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < n0 /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) /\
  (!a. a < lo ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL n0 h).po_taint.t_mem) /\
  (!a. dyn_floor C vs <= a ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL n0 h).po_taint.t_mem) /\
  ~in_revert_forward (EL n0 h).po_fn (EL n0 h).po_state /\
  (!op. op_taint (EL q ht).po_taint op SUBSET op_taint (EL n0 h).po_taint op) /\
  (EL q ht).po_taint.t_stor SUBSET (EL n0 h).po_taint.t_stor /\
  (EL q ht).po_taint.t_trans SUBSET (EL n0 h).po_taint.t_trans /\
  (EL q ht).po_taint.t_imm SUBSET (EL n0 h).po_taint.t_imm /\
  ~is_terminator (EL n0 h).po_inst.inst_opcode /\
  (EL n0 h).po_inst.inst_opcode <> INVOKE /\
  ~is_terminator (EL q ht).po_inst.inst_opcode /\
  (EL q ht).po_inst.inst_opcode <> INVOKE ==>
  (!i. (i < lo \/ dyn_floor C vs <= i) ==>
    i IN (EL (SUC q) ht).po_taint.t_mem ==>
    i IN (EL (SUC n0) h).po_taint.t_mem) /\
  (EL (SUC q) ht).po_taint.t_stor SUBSET (EL (SUC n0) h).po_taint.t_stor /\
  (EL (SUC q) ht).po_taint.t_trans SUBSET (EL (SUC n0) h).po_taint.t_trans /\
  (EL (SUC q) ht).po_taint.t_imm SUBSET (EL (SUC n0) h).po_taint.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_memory >> strip_tac >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  `SUC q < LENGTH ht` by fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  `SUC n0 < LENGTH h` by
    (drule_all ptr_structural_trace_nop_interval >> strip_tac >> gvs[] >> decide_tac) >>
  `ptr_chrono_step C (EL n0 h) (EL (SUC n0) h)` by
    (drule ptr_structural_trace_source >> strip_tac >>
     metis_tac[ptr_chrono_history_adjacent]) >>
  `ptr_chrono_step C' (EL q ht) (EL (SUC q) ht)` by
    (drule ptr_structural_trace_target >> strip_tac >>
     metis_tac[ptr_chrono_history_adjacent]) >>
  mp_tac (Q.INST [`a` |-> `EL n0 h`, `t` |-> `EL q ht`]
    ptr_dalloca_actual_event_context_static) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `EL (EL q done) H = (tsj,rj,bj,PTj,TGj,sj,ej)` >>
  `EL n0 H = (tsj,rj,bj,PTj,TGj,sj,ej)` by simp[] >>
  `(EL n0 h).po_inst.inst_opcode = MCOPY ==>
    ?dop sop nop d r dt rt n.
    (EL n0 h).po_inst.inst_operands = [dop;sop;nop] /\
    eval_operand dop (EL n0 h).po_state = SOME d /\
    eval_operand sop (EL n0 h).po_state = SOME r /\
    eval_operand nop (EL n0 h).po_state = SOME n /\
    eval_operand dop (EL q ht).po_state = SOME dt /\
    eval_operand sop (EL q ht).po_state = SOME rt /\
    eval_operand nop (EL q ht).po_state = SOME n /\
    (!k. k < w2n n ==> w2n rt+k IN (EL q ht).po_taint.t_mem ==>
      w2n r+k IN (EL n0 h).po_taint.t_mem)` by
    (strip_tac >> drule_all ptr_dalloca_historical_mcopy_read_mask_static >> simp[]) >>
  conj_tac
  >- (qx_gen_tac `i` >> disch_tac >>
      mp_tac (Q.INST
        [`a` |-> `EL n0 h`, `target` |-> `EL q ht`,
         `posts` |-> `(EL (SUC n0) h).po_state`,
         `postt` |-> `(EL (SUC q) ht).po_state`] ptr_dalloca_actual_memory_next_static) >>
      (impl_tac >- (simp[] >> metis_tac[])) >> simp[]) >>
  mp_tac (Q.INST
    [`a` |-> `EL n0 h`, `target` |-> `EL q ht`,
     `zs` |-> `EL (SUC n0) h`, `zt` |-> `EL (SUC q) ht`]
    ptr_dalloca_historical_persistent_chrono) >>
  (impl_tac >- simp[]) >> simp[]
QED

Theorem ptr_dalloca_memory_steps_ordinary:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  q < LENGTH done /\ n0 = EL q done /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  (!j r op. j < n0 /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < n0 /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < n0 /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < n0 /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) /\
  (!a. a < lo ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL n0 h).po_taint.t_mem) /\
  (!a. dyn_floor C vs <= a ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL n0 h).po_taint.t_mem) /\
  ~in_revert_forward (EL n0 h).po_fn (EL n0 h).po_state /\
  (!op. op_taint (EL q ht).po_taint op SUBSET op_taint (EL n0 h).po_taint op) /\
  (EL q ht).po_taint.t_stor SUBSET (EL n0 h).po_taint.t_stor /\
  (EL q ht).po_taint.t_trans SUBSET (EL n0 h).po_taint.t_trans /\
  (EL q ht).po_taint.t_imm SUBSET (EL n0 h).po_taint.t_imm /\
  ~is_terminator (EL n0 h).po_inst.inst_opcode /\
  (EL n0 h).po_inst.inst_opcode <> INVOKE /\
  ~is_terminator (EL q ht).po_inst.inst_opcode /\
  (EL q ht).po_inst.inst_opcode <> INVOKE ==>
  (!i. (i < lo \/ dyn_floor C vs <= i) ==>
    i IN (EL (SUC q) ht).po_taint.t_mem ==>
    i IN (EL (SUC n0) h).po_taint.t_mem) /\
  (EL (SUC q) ht).po_taint.t_stor SUBSET (EL (SUC n0) h).po_taint.t_stor /\
  (EL (SUC q) ht).po_taint.t_trans SUBSET (EL (SUC n0) h).po_taint.t_trans /\
  (EL (SUC q) ht).po_taint.t_imm SUBSET (EL (SUC n0) h).po_taint.t_imm
Proof
  rpt gen_tac >> mp_tac (SPEC_ALL ptr_dalloca_memory_steps_ordinary_static) >>
  pure_rewrite_tac[o1PassContractTheory.o1_run_state_ok_def] >>
  tautLib.TAUT_TAC
QED

Theorem ptr_dalloca_memory_steps_static:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  q < LENGTH done /\ n0 = EL q done /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ (o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs) /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  (!j r op. j < n0 /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < n0 /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < n0 /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < n0 /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) /\
  (!a. a < lo ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL n0 h).po_taint.t_mem) /\
  (!a. dyn_floor C vs <= a ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL n0 h).po_taint.t_mem) /\
  ~in_revert_forward (EL n0 h).po_fn (EL n0 h).po_state /\
  (!op. op_taint (EL q ht).po_taint op SUBSET op_taint (EL n0 h).po_taint op) /\
  (EL q ht).po_taint.t_stor SUBSET (EL n0 h).po_taint.t_stor /\
  (EL q ht).po_taint.t_trans SUBSET (EL n0 h).po_taint.t_trans /\
  (EL q ht).po_taint.t_imm SUBSET (EL n0 h).po_taint.t_imm ==>
  (!i. (i < lo \/ dyn_floor C vs <= i) ==>
    i IN (EL (SUC q) ht).po_taint.t_mem ==>
    i IN (EL (SUC n0) h).po_taint.t_mem) /\
  (EL (SUC q) ht).po_taint.t_stor SUBSET (EL (SUC n0) h).po_taint.t_stor /\
  (EL (SUC q) ht).po_taint.t_trans SUBSET (EL (SUC n0) h).po_taint.t_trans /\
  (EL (SUC q) ht).po_taint.t_imm SUBSET (EL (SUC n0) h).po_taint.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`a` |-> `EL n0 h`, `t` |-> `EL q ht`]
    ptr_dalloca_actual_event_context_static) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `~is_terminator (EL n0 h).po_inst.inst_opcode /\
    (EL n0 h).po_inst.inst_opcode <> INVOKE`
  >- (qpat_x_assum `~is_terminator (EL n0 h).po_inst.inst_opcode /\ _`
        strip_assume_tac >>
      `~is_terminator (EL q ht).po_inst.inst_opcode /\
       (EL q ht).po_inst.inst_opcode <> INVOKE` by
        (gvs[] >> metis_tac[concretize_positions_nonterminator,
                           concretize_positions_not_invoke]) >>
      drule_all ptr_dalloca_memory_steps_ordinary_static >> simp[]) >>
  `(EL n0 h).po_inst.inst_opcode <> ALLOCA` by
    (strip_tac >> gvs[is_terminator_def]) >>
  `(EL q ht).po_inst = (EL n0 h).po_inst` by
    gvs[concretize_positions_unchanged] >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  `SUC q < LENGTH ht` by fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  `SUC n0 < LENGTH h` by
    (drule_all ptr_structural_trace_nop_interval >> strip_tac >> gvs[] >> decide_tac) >>
  `ptr_chrono_step C (EL n0 h) (EL (SUC n0) h)` by
    (drule ptr_structural_trace_source >> strip_tac >>
     metis_tac[ptr_chrono_history_adjacent]) >>
  `ptr_chrono_step C' (EL q ht) (EL (SUC q) ht)` by
    (drule ptr_structural_trace_target >> strip_tac >>
     metis_tac[ptr_chrono_history_adjacent]) >>
  mp_tac (Q.SPECL [`C`,`EL n0 h`,`EL (SUC n0) h`]
    ptr_chrono_control_taint_fields) >> simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`C'`,`EL q ht`,`EL (SUC q) ht`]
    ptr_chrono_control_taint_fields) >> simp[] >> strip_tac >>
  simp[] >> metis_tac[]
QED

Theorem ptr_dalloca_memory_steps:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  q < LENGTH done /\ n0 = EL q done /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ctx_inst_ids_distinct C /\
  callee_first names C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  (!j r op. j < n0 /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < n0 /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < n0 /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < n0 /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) /\
  (!a. a < lo ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL n0 h).po_taint.t_mem) /\
  (!a. dyn_floor C vs <= a ==> a IN (EL q ht).po_taint.t_mem ==> a IN (EL n0 h).po_taint.t_mem) /\
  ~in_revert_forward (EL n0 h).po_fn (EL n0 h).po_state /\
  (!op. op_taint (EL q ht).po_taint op SUBSET op_taint (EL n0 h).po_taint op) /\
  (EL q ht).po_taint.t_stor SUBSET (EL n0 h).po_taint.t_stor /\
  (EL q ht).po_taint.t_trans SUBSET (EL n0 h).po_taint.t_trans /\
  (EL q ht).po_taint.t_imm SUBSET (EL n0 h).po_taint.t_imm ==>
  (!i. (i < lo \/ dyn_floor C vs <= i) ==>
    i IN (EL (SUC q) ht).po_taint.t_mem ==>
    i IN (EL (SUC n0) h).po_taint.t_mem) /\
  (EL (SUC q) ht).po_taint.t_stor SUBSET (EL (SUC n0) h).po_taint.t_stor /\
  (EL (SUC q) ht).po_taint.t_trans SUBSET (EL (SUC n0) h).po_taint.t_trans /\
  (EL (SUC q) ht).po_taint.t_imm SUBSET (EL (SUC n0) h).po_taint.t_imm
Proof
  rpt gen_tac >> mp_tac (SPEC_ALL ptr_dalloca_memory_steps_static) >>
  pure_rewrite_tac[o1PassContractTheory.o1_run_state_ok_def] >>
  tautLib.TAUT_TAC
QED
