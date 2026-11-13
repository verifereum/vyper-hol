Theory concretizePtrDallocaMemoryProbe
Ancestors
  concretizePtrDallocaGhostInterface concretizePtrChronologicalHistory
  concretizePtrPrefixLedger concretizePtrDallocaWriterGeometry
  concretizePtrDallocaEarlierRead concretizePtrDallocaWriterTaint
  concretizePtrDallocaStaticFresh concretizePtrHistoricalWriteExclusion
  concretizePtrDemandWriteExclusion memLocDefs ptrDiscipline pred_set
  finite_map list words arithmetic venomExecSemantics
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrEventEmbedding
  concretizePtrStageBounds concretizePtrRequestHistory concretizePtrTaintContent
  frameAllocationOwnership frameRawEndpoints unitMemInv unitShapeDefs
  venomMemProofs venomWf o1PassContract concretizePtrOpaqueRetpc
  concretizePtrSharedFields concretizeStepStructure concretizePtrOwnerPath
  concretizePtrOperationalOpcodes concretizeAllocationFree ptrDisciplineEmptyTaint

(* Fresh source allocation masks arbitrary target taint, including stale
   taint at a reused static position.  The byte relation is the retained
   activation/birth ledger, not numerical interval inversion.  Freshness
   must be supplied for this birth, not for all historical owned bytes. *)
Theorem ptr_dalloca_fresh_owner_mask:
  ptr_chrono_step C a b /\ a.po_inst.inst_opcode = ALLOCA /\
  step_inst fuel C a.po_inst a.po_state = OK post /\
  (!k x y. ptr_ledger_owned_byte registry births token aid k x y ==>
    x IN new_site_bytes a.po_state post) ==>
  !k x y. ptr_ledger_owned_byte registry births token aid k x y /\
    y IN target_mem ==> x IN b.po_taint.t_mem
Proof
  metis_tac[ptr_chrono_step_alloca]
QED

Theorem ptr_dalloca_store_writer_clean:
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
  MEM (EL w h).po_inst.inst_opcode [MSTORE;ISTORE] /\
  (!op. op_taint (EL q ht).po_taint op SUBSET op_taint (EL w h).po_taint op) ==>
  pa+k NOTIN (EL (SUC q) ht).po_taint.t_mem
Proof
  strip_tac >> drule_all ptr_dalloca_writer_updates >> strip_tac >>
  drule_all ptr_dalloca_writer_forward >> strip_tac >>
  `b+k NOTIN (EL (SUC w) h).po_taint.t_mem` by fs[ptr_demand_interval_def] >>
  `?dst value. (EL w h).po_inst.inst_operands = [dst;value] /\
      ops.iao_ofst = dst` by
    gvs[mem_write_ops_def, AllCaseEqs()] >>
  `!ix. ix IN op_taint (EL q ht).po_taint value ==>
        ix IN op_taint (EL w h).po_taint value` by fs[SUBSET_DEF] >>
  `w2n xt+off IN written_taint (EL q ht).po_taint (EL q ht).po_inst (EL q ht).po_state ==>
   w2n x+off IN written_taint (EL w h).po_taint (EL w h).po_inst (EL w h).po_state` by
    (gvs[written_taint_def] >> metis_tac[arithmeticTheory.EQ_ADD_LCANCEL]) >>
  gvs[step_taint_def, mem_taint_def, step_writes_def] >> metis_tac[]
QED

Theorem ptr_dalloca_copy_writer_clean:
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
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\
    FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) ==>
  pa+k NOTIN (EL (SUC q) ht).po_taint.t_mem
Proof
  strip_tac >> drule_all ptr_dalloca_writer_updates >> strip_tac >>
  drule_all ptr_dalloca_writer_forward >> strip_tac >>
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
    (strip_tac >> drule_all ptr_dalloca_earlier_copy_inclusion >> simp[]) >>
  gvs[step_taint_def, mem_taint_def, step_writes_def, written_taint_def] >> metis_tac[]
QED

Theorem ptr_dalloca_suffix_nonwrites:
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
  q < LENGTH done /\ EL q done = w ==>
  !r. SUC q <= r /\ r < LENGTH ht-1 ==>
    pa+k NOTIN range_bytes
      (step_writes (EL r ht).po_inst (EL r ht).po_state
        (EL (SUC r) ht).po_state)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_embedding >>
  simp[ptr_event_embedding_def] >> strip_tac >>
  `r < LENGTH done` by decide_tac >>
  `w < EL r done` by
    (`q < r` by decide_tac >>
     qpat_x_assum `!i j. _` (qspecl_then [`q`,`r`] mp_tac) >>
     simp[EL_APPEND_EQN]) >>
  drule_all ptr_paired_historical_owned_write_exclusion >> simp[]
QED

Theorem ptr_dalloca_history_content_fmp_floor:
  ptr_observation_reachable vs C a /\
  ptr_history_content a.po_taint a.po_state t /\
  o1_ctx_shape C /\ mem_inv raw_mem_ok C vs ==>
  w2n vs.vs_initial_fmp <= w2n t.vs_fmp
Proof
  strip_tac >>
  `EVERY wf_function C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `raw_mem_ok C a.po_fn a.po_inst a.po_state` by
    (fs[ptr_observation_reachable_def] >>
     drule_all (Q.INST [`M` |-> `raw_mem_ok`] frame_reachable_mem_inv) >> simp[]) >>
  `a.po_state.vs_initial_fmp = vs.vs_initial_fmp` by
    (fs[ptr_observation_reachable_def] >>
     drule frame_reachable_initial_fmp >> simp[]) >>
  drule ptr_history_content_control >>
  simp[ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def] >>
  strip_tac >> gvs[raw_mem_ok_def]
QED

(* Equality of allocation maps suffices: fresh-byte exclusion does not need
   to reconstruct the target's globally empty allocation-map invariant. *)
Theorem ptr_dalloca_preserved_allocas_fresh_exclusion:
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA /\
  step_inst fuel C inst t = OK post /\ y < w2n t.vs_fmp ==>
  y NOTIN new_site_bytes t post
Proof
  strip_tac >>
  `post.vs_allocas = t.vs_allocas` by
    (irule step_inst_base_preserves_allocas >>
     qexists `inst` >> simp[] >>
     gvs[step_inst_non_invoke, step_inst_base_preserves_allocas]) >>
  simp[new_site_bytes_def] >>
  metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]
QED

Theorem ptr_dalloca_suffix_fresh_exclusion:
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
  max_live_eom C' = SOME eom /\ ctx_has_dalloca C /\ eom <= w2n vs.vs_initial_fmp /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  w <= EL r done /\ r < LENGTH done /\
  ~is_terminator (EL r ht).po_inst.inst_opcode /\
  (EL r ht).po_inst.inst_opcode <> INVOKE /\
  step_inst fuel C' (EL r ht).po_inst (EL r ht).po_state = OK post ==>
  pa+k NOTIN new_site_bytes (EL r ht).po_state post
Proof
  strip_tac >>
  `k < sz /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
   EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    fs[ptr_demand_interval_def] >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_embedding >>
  simp[ptr_event_embedding_def, EVERY_MEM] >> strip_tac >>
  `EL r done < LENGTH h` by
    (first_x_assum irule >> simp[MEM_EL] >> qexists `r` >> simp[]) >>
  `~in_revert_forward (EL (EL r done) h).po_fn (EL (EL r done) h).po_state` by
    (fs[ptr_demand_interval_def] >> metis_tac[]) >>
  drule_all ptr_paired_historical_event >> strip_tac >>
  `w2n vs.vs_initial_fmp <= w2n (EL r ht).po_state.vs_fmp` by
    (drule_all ptr_dalloca_history_content_fmp_floor >> simp[]) >>
  `pa+sz <= eom` by (drule_all ptr_stage_placements_endpoint_bound >> simp[]) >>
  `MEM (EL (EL r done) h).po_inst (fn_insts (EL (EL r done) h).po_fn)` by
    (drule_all ptr_dalloca_writer_instruction_facts >> simp[]) >>
  `MEM (EL (EL r done) h).po_fn C.ctx_functions` by
    (fs[ptr_observation_reachable_def] >> drule ptr_frame_context_membership >> simp[]) >>
  `inst_wf (EL (EL r done) h).po_inst` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `(EL r ht).po_inst.inst_opcode <> ALLOCA` by
    metis_tac[concretize_positions_inst_no_alloca] >>
  irule ptr_dalloca_preserved_allocas_fresh_exclusion >>
  conj_tac >- decide_tac >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem ptr_dalloca_protected_suffix:
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
  max_live_eom C' = SOME eom /\ ctx_has_dalloca C /\ eom <= w2n vs.vs_initial_fmp /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  q < LENGTH done /\ EL q done = w /\
  pa+k NOTIN (EL (SUC q) ht).po_taint.t_mem ==>
  pa+k NOTIN at.po_taint.t_mem
Proof
  strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  drule ptr_structural_trace_embedding >>
  simp[ptr_event_embedding_def] >> strip_tac >>
  `0 < LENGTH ht /\ SUC q <= LENGTH ht-1 /\ LENGTH ht-1 < LENGTH ht` by decide_tac >>
  `EL (LENGTH ht-1) ht = at` by metis_tac[listTheory.LAST_EL, arithmeticTheory.PRE_SUB1] >>
  `pa+k NOTIN (EL (LENGTH ht-1) ht).po_taint.t_mem` suffices_by simp[] >>
  irule ptr_dalloca_chrono_untainted_suffix >>
  conj_tac >- simp[] >>
  qexistsl [`C'`,`at`,`SUC q`,`vs`] >> simp[] >>
  qx_gen_tac `r` >> strip_tac >> conj_tac
  >- (`ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp` by simp[] >>
      drule_all ptr_dalloca_suffix_nonwrites >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `r < LENGTH done /\ q < r` by decide_tac >>
  `w <= EL r done` by
    (qpat_x_assum `!i j. _` (qspecl_then [`q`,`r`] mp_tac) >>
     simp[EL_APPEND_EQN] >> decide_tac) >>
  drule_all ptr_dalloca_suffix_fresh_exclusion >> simp[]
QED

Theorem ptr_dalloca_other_writer_observation_clean:
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
  ~MEM (EL w h).po_inst.inst_opcode [MSTORE;ISTORE;MCOPY] ==>
  pa+k NOTIN (EL (SUC q) ht).po_taint.t_mem
Proof
  strip_tac >> drule_all ptr_dalloca_writer_updates >> strip_tac >>
  drule_all ptr_dalloca_writer_forward >> strip_tac >>
  `pa+k IN range_bytes (step_writes (EL q ht).po_inst (EL q ht).po_state postT)` by
    (gvs[step_writes_def, range_bytes_def] >> metis_tac[]) >>
  gvs[] >> irule ptr_dalloca_other_writer_clean >> simp[]
QED

Theorem ptr_dalloca_protected_writer_boundary:
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
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\
    FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) ==>
  pa+k NOTIN at.po_taint.t_mem
Proof
  strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
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
         >- (drule_all ptr_dalloca_store_writer_clean >> simp[]) >>
         Cases_on `(EL w h).po_inst.inst_opcode = MCOPY`
         >- (drule_all ptr_dalloca_copy_writer_clean >> simp[]) >>
         `~MEM (EL w h).po_inst.inst_opcode [MSTORE;ISTORE;MCOPY]` by fs[] >>
         drule_all ptr_dalloca_other_writer_observation_clean >> simp[]) >>
      `eom <= w2n vs.vs_initial_fmp` by simp[] >>
      drule_all ptr_dalloca_protected_suffix >> simp[]) >>
  `EVERY (\fn. EVERY (\inst. allocation_free_opcode inst.inst_opcode)
    (fn_insts fn)) C'.ctx_functions` by
    (drule_all concretize_stage_allocation_free >> simp[]) >>
  `ptr_observation_reachable vs C' at` by metis_tac[ptr_chrono_history_reachable] >>
  `vs.vs_allocas = FEMPTY` by fs[ptr_demand_interval_def] >>
  fs[ptr_observation_reachable_def] >>
  drule_all allocation_free_reachable_taint >> simp[taint_empty_def]
QED
