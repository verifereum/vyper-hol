Theory concretizePtrDallocaEarlierRead
Ancestors
  concretizePtrPairedPrefix
  concretizePtrDallocaWriterGeometry concretizePtrDallocaWriterProbe
  concretizePtrHistoricalWriteExclusion concretizePtrObservationInterface
  concretizePtrOwnershipErasure concretizePtrSourceOwnership
  concretizePtrPrefixLedger concretizePtrComparisonTransport
  concretizePtrDemandWriteExclusion concretizePtrRequestHistory
  concretizePtrPlacementBounds concretizePtrMloadEndpoint
  concretizePtrValueTransport concretizePtrOpaqueRetpc
  ptrDiscipline memLocDefs venomState contextCodegenRel codegenRel list finite_map words arithmetic

(* Bytewise use of the ledger interface works at retained observations,
   without asserting a restriction of the full paired-prefix predicate. *)
Theorem ptr_dalloca_read_byte_classification:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  mem_read_ops inst = SOME ops /\
  MEM (w2n x,n) (source_memory_read_ranges inst s) /\ off < n /\
  ptr_ledger_erases dyn births TG G /\
  (!aid pa sz. FLOOKUP positions (Allocation aid) = SOME (pa,sz) ==>
    pa+sz < dimword(:256)) /\
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) ==>
  (w2n y+off = w2n x+off /\ w2n x+off < lo) \/
  (w2n y+off = w2n x+off /\ dyn <= w2n x+off) \/
  (?v token aid b sz pa k.
    ops.iao_ofst = Var v /\ FLOOKUP TG v = SOME (token,aid) /\
    FLOOKUP G v = SOME (b,sz) /\ FLOOKUP births (token,aid) = SOME (b,sz) /\
    FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
    k < sz /\ w2n x+off = b+k /\ w2n y+off = pa+k)
Proof
  strip_tac >>
  Cases_on `op_prov G ops.iao_ofst = NONE /\ w2n x+n <= lo`
  >- (`op_prov TG ops.iao_ofst = NONE` by
        (Cases_on `ops.iao_ofst` >> gvs[op_prov_def] >>
         Cases_on `FLOOKUP TG s'` >> simp[] >>
         fs[ptr_ledger_erases_def] >>
         qpat_x_assum `!v. ptr_owner_erases _ _ _ _` (qspec_then `s'` mp_tac) >>
         simp[ptr_owner_erases_def] >> metis_tac[flookup_thm]) >>
      gvs[ptr_lookup_transport_def, ptr_value_transport_scalar_empty] >>
      disj1_tac >> decide_tac) >>
  `?v b sz. ops.iao_ofst = Var v /\ FLOOKUP G v = SOME (b,sz) /\
    b <= w2n x /\ w2n x+n <= b+sz` by
    (`n <> 0` by decide_tac >> fs[access_ok_def] >> metis_tac[NOT_LESS_EQUAL]) >>
  gvs[] >>
  `ptr_owner_erases dyn births (FLOOKUP TG v) (SOME (b,sz))` by
    (fs[ptr_ledger_erases_def] >> metis_tac[]) >>
  Cases_on `FLOOKUP TG v`
  >- (gvs[ptr_owner_erases_def, op_prov_def, ptr_lookup_transport_def,
          ptr_value_transport_scalar_empty] >> disj2_tac >> disj1_tac >> decide_tac) >>
  disj2_tac >> disj2_tac >> rename1 `FLOOKUP TG v = SOME tag` >> PairCases_on `tag` >>
  rename1 `FLOOKUP TG v = SOME (token,aid)` >>
  `FLOOKUP births (token,aid) = SOME (b,sz)` by fs[ptr_owner_erases_def] >>
  `?pa. FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
    y = x - n2w b + n2w pa` by
    gvs[ptr_lookup_transport_def, ptr_value_transport_def, op_prov_def] >>
  `pa+sz < dimword(:256)` by metis_tac[] >>
  `w2n y = pa+(w2n x-b)` by
    (irule ptr_closed_relocation_value >> simp[] >> qexists `sz` >> simp[] >> decide_tac) >>
  qexistsl [`token`,`aid`,`pa`,`w2n x+off-b`] >> simp[] >> decide_tac
QED

Theorem ptr_dalloca_copy_read_transport:
  ptr_mixed_vars births positions TG tn fn ft s t /\ s.vs_labels = t.vs_labels /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ taint_ok fn tn inst s /\
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [dst;src;n] /\
  eval_operand src s = SOME x /\ eval_operand src t = SOME y ==>
  ptr_lookup_transport births positions (op_prov TG src) {} (SOME x) (SOME y)
Proof
  strip_tac >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[]) >>
  `op_taint tn src = {}` by
    (fs[taint_ok_def] >> metis_tac[]) >>
  `ptr_nonopaque_operand fn src` by (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_mixed_vars_eval >> simp[]
QED

Theorem ptr_dalloca_copy_writer_destination[local]:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [dst;src;n] /\
  a IN range_bytes (step_writes inst s post) ==>
  ?dv. eval_operand dst s = SOME dv
Proof
  strip_tac >> gvs[step_writes_def, source_memory_write_ranges_def, sized_source_write_range_def,
      range_bytes_def, AllCaseEqs()] >>
  Cases_on `eval_operand dst s` >> gvs[]
QED

Theorem ptr_dalloca_earlier_copy_read_memory:
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
  ((w2n y+off = w2n x+off /\ w2n x+off < lo) \/
   (w2n y+off = w2n x+off /\ dyn_floor C vs <= w2n x+off) \/
   (?u tok id base size pos ix ts rw bw PTw TGw sw ew.
     EL w H = (ts,rw,bw,PTw,TGw,sw,ew) /\
     src = Var u /\ FLOOKUP TGw u = SOME (tok,id) /\
     FLOOKUP (EL w h).po_prov u = SOME (base,size) /\
     FLOOKUP bw (tok,id) = SOME (base,size) /\
     FLOOKUP positions (Allocation id) = SOME (pos,size) /\
     ix < size /\ w2n x+off = base+ix /\ w2n y+off = pos+ix))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~in_revert_forward (EL (EL q done) h).po_fn
      (EL (EL q done) h).po_state` by
    (fs[ptr_demand_interval_def] >>
     qpat_x_assum `!j. w <= j /\ j < LENGTH h ==> _`
       (qspec_then `w` mp_tac) >> simp[] >> decide_tac) >>
  drule_all ptr_paired_historical_event_memory >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions /\
   EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
   b+k IN range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
      (EL (SUC w) h).po_state)` by fs[ptr_demand_interval_def] >>
  drule_all ptr_dalloca_writer_instruction_facts >> strip_tac >>
  gvs[] >> drule_all ptr_dalloca_initial_writer_snapshot >> strip_tac >>
  drule_all ptr_source_ownership_prov_erases >> strip_tac >>
  `(EL (EL q done) h).po_state.vs_labels = (EL q ht).po_state.vs_labels` by
    metis_tac[ptr_history_content_labels] >>
  drule_all ptr_dalloca_copy_read_transport >> strip_tac >>
  drule_all ptr_dalloca_copy_writer_destination >> strip_tac >>
  `mem_read_ops (EL (EL q done) h).po_inst = SOME
    <|iao_ofst := src; iao_size := SOME n; iao_max_size := SOME n|> /\
   MEM (w2n x,w2n len) (source_memory_read_ranges (EL (EL q done) h).po_inst
     (EL (EL q done) h).po_state)` by
    simp[mem_read_ops_def, source_memory_read_ranges_def] >>
  `!id pos size. FLOOKUP positions (Allocation id) = SOME (pos,size) ==>
     pos+size < dimword(:256)` by
    (rpt strip_tac >> drule_all ptr_stage_placements_strict_bound >> simp[]) >>
  drule_all ptr_dalloca_demand_writer_index >> strip_tac >>
  drule_all (SPEC_ALL ptr_dalloca_read_byte_classification
    |> Q.INST [`ops` |-> `<|iao_ofst := cp_src; iao_size := SOME cp_n; iao_max_size := SOME cp_n|>`]
    |> SIMP_RULE (srw_ss()) []) >>
  simp[] >> metis_tac[]
QED

Theorem ptr_dalloca_earlier_copy_read:
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
  ((w2n y+off = w2n x+off /\ w2n x+off < lo) \/
   (w2n y+off = w2n x+off /\ dyn_floor C vs <= w2n x+off) \/
   (?u tok id base size pos ix ts rw bw PTw TGw sw ew.
     EL w H = (ts,rw,bw,PTw,TGw,sw,ew) /\
     src = Var u /\ FLOOKUP TGw u = SOME (tok,id) /\
     FLOOKUP (EL w h).po_prov u = SOME (base,size) /\
     FLOOKUP bw (tok,id) = SOME (base,size) /\
     FLOOKUP positions (Allocation id) = SOME (pos,size) /\
     ix < size /\ w2n x+off = base+ix /\ w2n y+off = pos+ix))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> drule ptr_paired_prefix_memory >> strip_tac >>
  drule_all ptr_dalloca_earlier_copy_read_memory >> simp[]
QED

(* The three incoming clauses are induction hypotheses at strictly earlier
   source observations.  Classification alone never supplies ghost inclusion. *)
Theorem ptr_dalloca_earlier_copy_inclusion:
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
  eval_operand n (EL w h).po_state = SOME len /\ off < w2n len /\
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
  w2n y+off IN (EL q ht).po_taint.t_mem ==>
  w2n x+off IN (EL w h).po_taint.t_mem
Proof
  strip_tac >> drule_all ptr_dalloca_earlier_copy_read >>
  strip_tac >> metis_tac[]
QED
