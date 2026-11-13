Theory concretizePtrDallocaMemoryProbe
Ancestors
  concretizePtrDallocaGhostInterface concretizePtrChronologicalHistory
  concretizePtrPrefixLedger concretizePtrDallocaWriterGeometry
  concretizePtrDallocaEarlierRead concretizePtrDallocaWriterTaint
  concretizePtrDallocaStaticFresh concretizePtrHistoricalWriteExclusion
  concretizePtrDemandWriteExclusion memLocDefs ptrDiscipline pred_set
  finite_map list words arithmetic venomExecSemantics

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
