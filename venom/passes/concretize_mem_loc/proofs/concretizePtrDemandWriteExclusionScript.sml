Theory concretizePtrDemandWriteExclusion
Ancestors concretizePtrProtectedLivesets concretizePtrTokenInterval
  concretizePtrHistoricalPlacement concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrExactWriteTransport
  concretizePtrTaggedCallLiveness concretizePtrRetrospectiveLocal
  concretizePtrChronologicalHistory concretizePtrOwnerPath
  concretizePtrStageReserved concretizePtrWriteTransport
  concretizePtrSourceOwnership concretizePtrActivationBirths
  concretizePtrActivationChronology concretizePtrHistoryCfg
  concretizePtrExecutedCoverage concretizePtrAllocationSize
  concretizePtrImportOrigins concretizePtrStagePlacements
  concretizePtrLayoutOutput concretizePtrTaggedOrigins
  concretizePtrCallSeparation concretizePtrStackImports
  concretizePtrOwnershipErasure ptrDiscipline
  concretizePtrRuntimeGeneration concretizePtrProductionCoverage
  concretizeAnalysisBoundary concretizeAnalysisScanCoverage
  concretizeAnalysisWriteSafety basePtrDefs
  concretizeMemLocTransitionProofs concretizeMemLocDefs
  staticLayoutAllocatorProofs o1PassContract venomPassDispatcher
  contextCodegenRel o1ScheduleDecompHelpers venomWf venomInst option pair
  list rich_list finite_map arithmetic

(* Keep the initializing writer selected by ProtectedLivesets: token
   continuity is proved on its interval, not on a second chosen history. *)
Theorem ptr_demand_protected_token_interval:
  ptr_structural_transcript R vs C C' h endpoint ht at done tokens registry
    births PT TG saved entries H /\ vs.vs_allocas = FEMPTY /\
  o1_ctx_shape C /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  (!obs. MEM obs h ==> access_ok lo obs.po_prov obs.po_fn obs.po_inst obs.po_state) /\
  ~in_revert_forward endpoint.po_fn endpoint.po_state /\
  endpoint.po_inst.inst_opcode <> ASSIGN /\ d <= LENGTH endpoint.po_stack /\
  FLOOKUP (ptr_owner_view d endpoint).cf_state.vs_allocas aid = SOME (b,sz) /\
  lo <= b+k /\ k < sz /\ b+k NOTIN endpoint.po_taint.t_mem /\
  MEM (Var v) endpoint.po_inst.inst_operands /\
  (inst_read_op endpoint.po_inst = SOME (Var v) \/ endpoint.po_inst.inst_opcode = INVOKE) /\
  FLOOKUP endpoint.po_prov v = SOME (b,sz) /\
  EL (LENGTH endpoint.po_stack-d) tokens = token /\
  fn = (ptr_owner_view d endpoint).cf_fn /\
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  mems = (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed.cu_context nm))) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME out.fpo_function /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  o1_run_state_ok vs /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  EVERY fn_inst_wf C.ctx_functions ==>
  ?w. w+1 < LENGTH h /\
    b+k IN range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
      (EL (SUC w) h).po_state) /\
    b+k NOTIN (EL (SUC w) h).po_taint.t_mem /\
    (!j. w < j /\ j+1 < LENGTH h ==>
      b+k NOTIN range_bytes (step_writes (EL j h).po_inst (EL j h).po_state
        (EL (SUC j) h).po_state)) /\
    (!t. w < t /\ t < LENGTH h ==>
      ?xs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
        observed.cu_context fn bp (cfg_analyze fn)) (Allocation aid) = SOME xs /\
        MEM ((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
          (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx) xs) /\
    (!j. w <= j /\ j < LENGTH h ==>
      d <= LENGTH (EL j h).po_stack /\
      FLOOKUP (ptr_owner_view d (EL j h)).cf_state.vs_allocas aid = SOME (b,sz) /\
      ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
      EL (LENGTH (EL j h).po_stack-d) (FST (EL j H)) = token) /\
    ml_used_gen (Allocation aid) bp mems (ptr_owner_view d (EL w h)).cf_inst /\
    ml_read_gen (Allocation aid) bp mems (ptr_owner_view d endpoint).cf_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  `b <= b+k /\ b+k < b+sz` by decide_tac >>
  drule_all ptr_endpoint_actual_protected_livesets >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  `LENGTH h-1 < LENGTH h /\ EL (LENGTH h-1) h = endpoint /\
   EL (LENGTH h-1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    (Cases_on `h` >> Cases_on `H` >> gvs[LAST_EL]) >>
  `!j. w <= j /\ j < LENGTH h ==>
    EL (LENGTH (EL j h).po_stack-d) (FST (EL j H)) = token` by
    (`!j. w <= j /\ j <= LENGTH h-1 ==>
       ?tsj rj bj PTj TGj sj ej.
         EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
         EL (LENGTH (EL j h).po_stack-d) tsj = token` by
       (drule ptr_transcript_bottom_token_interval >>
        disch_then (qspecl_then [`w`,`LENGTH h-1`,`d`] mp_tac) >>
        simp[]) >>
     rpt strip_tac >> first_x_assum (qspec_then `j` mp_tac) >>
     (impl_tac >- decide_tac) >> strip_tac >> simp[]) >>
  qexists `w` >> asm_rewrite_tac[] >> rpt strip_tac >> metis_tac[]
QED

(* A single writer witness, including the premises needed by its production
   geometry. This is proof data, not an assertion of paired execution. *)
Definition ptr_demand_interval_def:
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w <=>
  (ptr_structural_transcript R vs C C' h endpoint ht at done tokens registry
    births PT TG saved entries H /\ vs.vs_allocas = FEMPTY /\
  o1_ctx_shape C /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  (!obs. MEM obs h ==> access_ok lo obs.po_prov obs.po_fn obs.po_inst obs.po_state) /\
  ~in_revert_forward endpoint.po_fn endpoint.po_state /\
  endpoint.po_inst.inst_opcode <> ASSIGN /\ d <= LENGTH endpoint.po_stack /\
  FLOOKUP (ptr_owner_view d endpoint).cf_state.vs_allocas aid = SOME (b,sz) /\
  lo <= b+k /\ k < sz /\ b+k NOTIN endpoint.po_taint.t_mem /\
  MEM (Var v) endpoint.po_inst.inst_operands /\
  (inst_read_op endpoint.po_inst = SOME (Var v) \/ endpoint.po_inst.inst_opcode = INVOKE) /\
  FLOOKUP endpoint.po_prov v = SOME (b,sz) /\
  EL (LENGTH endpoint.po_stack-d) tokens = token /\
  fn = (ptr_owner_view d endpoint).cf_fn /\
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  mems = (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed.cu_context nm))) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME out.fpo_function /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  o1_run_state_ok vs /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  EVERY fn_inst_wf C.ctx_functions) /\
  (w+1 < LENGTH h /\
    b+k IN range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
      (EL (SUC w) h).po_state) /\
    b+k NOTIN (EL (SUC w) h).po_taint.t_mem /\
    (!j. w < j /\ j+1 < LENGTH h ==>
      b+k NOTIN range_bytes (step_writes (EL j h).po_inst (EL j h).po_state
        (EL (SUC j) h).po_state)) /\
    (!t. w < t /\ t < LENGTH h ==>
      ?xs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
        observed.cu_context fn bp (cfg_analyze fn)) (Allocation aid) = SOME xs /\
        MEM ((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
          (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx) xs) /\
    (!j. w <= j /\ j < LENGTH h ==>
      d <= LENGTH (EL j h).po_stack /\
      FLOOKUP (ptr_owner_view d (EL j h)).cf_state.vs_allocas aid = SOME (b,sz) /\
      ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
      EL (LENGTH (EL j h).po_stack-d) (FST (EL j H)) = token) /\
    ml_used_gen (Allocation aid) bp mems (ptr_owner_view d (EL w h)).cf_inst /\
    ml_read_gen (Allocation aid) bp mems (ptr_owner_view d endpoint).cf_inst)
End

Theorem ptr_demand_interval_exists:
  ptr_structural_transcript R vs C C' h endpoint ht at done tokens registry
    births PT TG saved entries H /\ vs.vs_allocas = FEMPTY /\
  o1_ctx_shape C /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  (!obs. MEM obs h ==> access_ok lo obs.po_prov obs.po_fn obs.po_inst obs.po_state) /\
  ~in_revert_forward endpoint.po_fn endpoint.po_state /\
  endpoint.po_inst.inst_opcode <> ASSIGN /\ d <= LENGTH endpoint.po_stack /\
  FLOOKUP (ptr_owner_view d endpoint).cf_state.vs_allocas aid = SOME (b,sz) /\
  lo <= b+k /\ k < sz /\ b+k NOTIN endpoint.po_taint.t_mem /\
  MEM (Var v) endpoint.po_inst.inst_operands /\
  (inst_read_op endpoint.po_inst = SOME (Var v) \/ endpoint.po_inst.inst_opcode = INVOKE) /\
  FLOOKUP endpoint.po_prov v = SOME (b,sz) /\
  EL (LENGTH endpoint.po_stack-d) tokens = token /\
  fn = (ptr_owner_view d endpoint).cf_fn /\
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  mems = (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed.cu_context nm))) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME out.fpo_function /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  o1_run_state_ok vs /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  EVERY fn_inst_wf C.ctx_functions ==>
  ?w. ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_demand_protected_token_interval >> strip_tac >>
  qexists `w` >> simp[ptr_demand_interval_def]
QED

Theorem ptr_demand_interval_owner_at[local]:
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\ w < j /\ j+1 < LENGTH h ==>
  d <= LENGTH (EL j h).po_stack /\
  FLOOKUP (ptr_owner_view d (EL j h)).cf_state.vs_allocas aid = SOME (b,sz) /\
  EL (LENGTH (EL j h).po_stack-d) (FST (EL j H)) = token /\
  (ptr_owner_view d (EL j h)).cf_fn = fn /\
  b+k NOTIN range_bytes (step_writes (EL j h).po_inst (EL j h).po_state
    (EL (SUC j) h).po_state) /\
  ?xs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
    observed.cu_context fn bp (cfg_analyze fn)) (Allocation aid) = SOME xs /\
    MEM ((ptr_owner_view d (EL j h)).cf_state.vs_current_bb,
      (ptr_owner_view d (EL j h)).cf_state.vs_inst_idx) xs
Proof
  pure_rewrite_tac[ptr_demand_interval_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  `LENGTH h-1 < LENGTH h /\ EL (LENGTH h-1) h = endpoint` by
    (Cases_on `h` >> gvs[LAST_EL]) >>
  `(ptr_owner_view d (EL j h)).cf_fn = fn` by
    (`(ptr_owner_view d (EL j h)).cf_fn =
      (ptr_owner_view d (EL (LENGTH h-1) h)).cf_fn` by
       (irule ptr_owner_view_interval_function >> simp[] >>
        metis_tac[]) >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  `w <= j /\ j < LENGTH h` by decide_tac >>
  qpat_x_assum `!j. w <= j /\ j < LENGTH h ==> _`
    (qspec_then `j` strip_assume_tac) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem ptr_demand_interval_reserved_prefix[local]:
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
  ptr_stage_placements C' positions /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\ fixed_region_reserved lo C ==>
  lo <= pa+k
Proof
  pure_rewrite_tac[ptr_demand_interval_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule ptr_stage_placements_reserved_prefix >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem ptr_demand_fixed_write_exclusion[local]:
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
  ptr_stage_placements C' positions /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\ fixed_region_reserved lo C /\
  ptr_lookup_transport bj positions (op_prov TGj ops.iao_ofst)
    (op_taint tn ops.iao_ofst) (eval_operand ops.iao_ofst src) (eval_operand ops.iao_ofst tgt) /\
  ptr_lookup_transport bj positions (op_prov TGj sizeop)
    (op_taint tn sizeop) (eval_operand sizeop src) (eval_operand sizeop tgt) /\
  mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
  ((?u. ops.iao_ofst = Var u) \/ (?y. ops.iao_ofst = Lit y)) /\
  ((?u. sizeop = Var u) \/ (?y. sizeop = Lit y)) /\
  eval_operand ops.iao_ofst src = SOME x /\ eval_operand sizeop src = SOME z /\
  op_prov TGj ops.iao_ofst = NONE /\ op_taint tn ops.iao_ofst = {} /\
  op_prov TGj sizeop = NONE /\ op_taint tn sizeop = {} /\
  w2n x + w2n z <= lo ==>
  pa+k NOTIN range_bytes (step_writes inst tgt postt)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lo <= pa+k` by (drule_all ptr_demand_interval_reserved_prefix >> simp[]) >>
  `!q. q IN range_bytes (step_writes inst tgt postt) ==> q < lo` by
    (gen_tac >> strip_tac >>
     irule (INST_TYPE [alpha |-> ``:num``] ptr_write_transport_fixed_containment) >>
     rpt (goal_assum (drule_at Any)) >> asm_rewrite_tac[]) >>
  first_x_assum (qspec_then `pa+k` mp_tac) >> simp[]
QED

Theorem ptr_demand_interval_snapshot[local]:
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\ w < j /\ j+1 < LENGTH h /\
  EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) ==>
  ptr_source_ownership vs C (TAKE (SUC j) h) (EL j h) tsj rj bj PTj TGj sj /\
  FLOOKUP bj (token,aid) = SOME (b,sz)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_demand_interval_owner_at >> strip_tac >>
  qhdtm_x_assum `ptr_demand_interval` mp_tac >>
  pure_rewrite_tac[ptr_demand_interval_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_structural_transcript_ownership >>
  disch_then (qspec_then `j` mp_tac) >>
  simp[ptr_snapshot_ownership_def] >> strip_tac >>
  asm_rewrite_tac[] >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule_all ptr_source_birth_caches_slices >>
  simp[ptr_birth_slices_def] >>
  disch_then (qspecl_then [`d`,`aid`] mp_tac) >>
  qpat_x_assum `(EL (LENGTH (EL j h).po_stack - d) (FST (EL j H))) = token`
    mp_tac >> asm_rewrite_tac[] >> strip_tac >> asm_rewrite_tac[]
QED

Theorem ptr_demand_same_owner_write_exclusion[local]:
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\ w < j /\ j+1 < LENGTH h /\
  EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
  ptr_lookup_transport bj positions (op_prov TGj ops.iao_ofst)
    (op_taint (EL j h).po_taint ops.iao_ofst)
    (eval_operand ops.iao_ofst src) (eval_operand ops.iao_ofst tgt) /\
  ptr_lookup_transport bj positions (op_prov TGj sizeop)
    (op_taint (EL j h).po_taint sizeop)
    (eval_operand sizeop src) (eval_operand sizeop tgt) /\
  (!op. IS_SOME (eval_operand op src) = IS_SOME (eval_operand op tgt)) /\
  src.vs_labels = tgt.vs_labels /\
  mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
  eval_operand ops.iao_ofst src = SOME x /\ eval_operand sizeop src = SOME z /\
  op_prov TGj ops.iao_ofst = SOME (token,aid) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  op_prov TGj sizeop = NONE /\ op_taint (EL j h).po_taint sizeop = {} /\
  b <= w2n x /\ w2n x + w2n z <= b+sz /\ pa+sz < dimword(:256) /\
  (MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] ==>
    LENGTH posts.vs_returndata = LENGTH postt.vs_returndata) /\
  b+k NOTIN range_bytes (step_writes inst src posts) ==>
  pa+k NOTIN range_bytes (step_writes inst tgt postt)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_demand_interval_snapshot >> strip_tac >>
  drule_all ptr_demand_interval_owner_at >> strip_tac >>
  `k < sz` by fs[ptr_demand_interval_def] >>
  drule_all ptr_write_transport_owner_exact >>
  asm_rewrite_tac[]
QED


Theorem ptr_demand_owner_layout:
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\ w < j /\ j+1 < LENGTH h /\ A = EL j h /\
  e <= LENGTH A.po_stack /\ owner = (ptr_owner_view e A).cf_fn /\
  FLOOKUP (ptr_owner_view e A).cf_state.vs_allocas xid = SOME (xb,xsz) /\
  ptr_stage_placements C' positions /\
  FLOOKUP positions (Allocation xid) = SOME (xp,xsz) /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) obs st owner result /\
  lookup_function owner.fn_name C.ctx_functions = SOME owner /\
  lookup_function owner.fn_name C'.ctx_functions = SOME result.fpo_function /\
  ctx_fn_names obs.cu_context = ctx_fn_names C /\
  o1_walk_view rpolicy 2 C' owner obs ==>
  owner.fn_eom = NONE /\ fn_ptr_ok P owner /\ wf_function owner /\
  ssa_form owner /\ all_reachable owner /\ fn_inst_wf owner /\
  EVERY inst_wf (fn_insts owner) /\ ptr_history_cfg_ok owner (cfg_analyze owner) /\
  MEM (Allocation xid,xp,xsz) result.fpo_function.fn_mems_used /\
  ?reserved items.
    concretize_function_fuel_in_context (concretize_memloc_fuel owner)
      obs.cu_context reserved owner = SOME result.fpo_function /\
    static_alloca_items owner = SOME items /\ MEM (Allocation xid,xsz) items /\
    (!c p size. MEM (c,p,size) (imported_mems_used obs.cu_context owner) ==>
      ~MEM c (MAP (\i. Allocation i.inst_id)
        (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts owner))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `ptr_demand_interval` mp_tac >>
  pure_rewrite_tac[ptr_demand_interval_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM owner C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `owner.fn_eom = NONE /\ fn_ptr_ok P owner /\ wf_function owner /\
   ssa_form owner /\ all_reachable owner /\ fn_inst_wf owner /\
   EVERY inst_wf (fn_insts owner)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `ptr_history_cfg_ok owner (cfg_analyze owner)` by
    metis_tac[ptr_history_cfg_analyze_ok] >>
  asm_rewrite_tac[] >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  `ptr_observation_reachable vs C A` by
    (drule ptr_chrono_history_reachable >> simp[EVERY_EL] >>
     disch_then (qspec_then `j` mp_tac) >> asm_rewrite_tac[] >> simp[]) >>
  `frame_reachable vs C A.po_stack A.po_params A.po_prov A.po_taint
    A.po_fn A.po_inst A.po_state` by
    fs[ptr_observation_reachable_def] >>
  drule_all ptr_frame_table_source >> strip_tac >>
  drule_all ptr_frame_sizes >> strip_tac >>
  `ptr_table_source owner (ptr_owner_view e A).cf_state /\
   alloca_sizes_match owner (ptr_owner_view e A).cf_state` by
    (Cases_on `e = LENGTH A.po_stack`
     >- (simp[ptr_owner_view_def] >> metis_tac[]) >>
     `MEM (ptr_owner_view e A) A.po_stack` by
       (simp[ptr_owner_view_def] >> irule EL_MEM >>
        qpat_x_assum `A = EL j h` (fn th => fs[th]) >> decide_tac) >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `?i. MEM i (fn_insts owner) /\ i.inst_opcode = ALLOCA /\
       i.inst_id = xid` by metis_tac[ptr_table_source_def] >>
  `xsz = get_alloca_size owner (Allocation xid)` by
    metis_tac[alloca_sizes_match_def] >>
  `fn_inst_ids_distinct owner` by fs[wf_function_def] >>
  `?reserved. concretize_function_fuel_in_context (concretize_memloc_fuel owner)
    obs.cu_context reserved owner = SOME result.fpo_function` by
    (qpat_x_assum `fn_pass_step _ _ obs st owner result` mp_tac >>
     simp[fn_pass_step_def, execute_configured_fn_pass_concretize,
          AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all ptr_concretize_static_items >> strip_tac >>
  `MEM (Allocation xid,xsz) items` by
    (drule_all static_alloca_items_ALLOCA_exact >> strip_tac >>
     rename1 `i.inst_operands = [Lit n]` >>
     `xsz = w2n n` by metis_tac[ptr_alloca_inst_size] >>
     drule static_alloca_items_MEM >>
     disch_then (qspec_then `(Allocation xid,xsz)` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `MEM (Allocation xid,xp,xsz) result.fpo_function.fn_mems_used` by
    (drule_all ptr_step_alloca_mems >> strip_tac >>
     `MEM result.fpo_function C'.ctx_functions` by
       metis_tac[lookup_function_MEM] >>
     `FLOOKUP positions (Allocation xid) = SOME (p,xsz)` by
       (fs[ptr_stage_placements_def] >> metis_tac[]) >>
     metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  `!c p size. MEM (c,p,size) (imported_mems_used obs.cu_context owner) ==>
    ~MEM c (MAP (\i. Allocation i.inst_id)
      (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts owner)))` by
    (rpt gen_tac >> strip_tac >>
     pure_rewrite_tac[MEM_MAP, MEM_FILTER] >>
     CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
     rename1 `is_alloca_op z.inst_opcode` >>
     `z.inst_opcode = ALLOCA` by
       (qpat_x_assum `is_alloca_op z.inst_opcode` mp_tac >>
        Cases_on `z.inst_opcode` >> simp[is_alloca_op_def]) >>
     drule_all ptr_stage_local_not_imported >>
     simp[MEM_MAP] >> qexists_tac `(c,p,size')` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `xsz = _` SUBST_ALL_TAC >>
  qpat_x_assum `owner = _` SUBST_ALL_TAC >>
  qpat_x_assum `A = EL j h` SUBST_ALL_TAC >>
  asm_rewrite_tac[] >> qexistsl [`reserved`,`items`] >>
  metis_tac[]
QED

Theorem ptr_demand_other_owner_separation:
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\ w < j /\ j+1 < LENGTH h /\ A = EL j h /\
  EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
  ptr_stage_placements C' positions /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  inst_write_op A.po_inst = SOME (Var dv) /\
  FLOOKUP TGj dv = SOME (tokB,bid) /\
  FLOOKUP A.po_prov dv = SOME (db,sb) /\
  FLOOKUP positions (Allocation bid) = SOME (pb,sb) /\
  0 < sb /\ (tokB <> token \/ bid <> aid) ==>
  reserved_intervals_disjoint (pa,sz) (pb,sb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_demand_interval_owner_at >> strip_tac >>
  drule_all ptr_demand_interval_snapshot >> strip_tac >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
     (o1_walk_view rpolicy 2) C C' /\
   EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
   ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
   o1_run_state_ok vs /\ ~ctx_has_dalloca C /\
   ptr_structural_transcript R vs C C' h endpoint ht at done tokens registry
     births PT TG saved entries H` by fs[ptr_demand_interval_def] >>
  `?e owner output p.
    e <= LENGTH A.po_stack /\ EL (LENGTH A.po_stack-e) tsj = tokB /\
    owner = (ptr_owner_view e A).cf_fn /\
    FLOOKUP (ptr_owner_view e A).cf_state.vs_allocas bid = SOME (db,sb) /\
    lookup_function owner.fn_name C'.ctx_functions = SOME output /\
    FLOOKUP positions (Allocation bid) = SOME (p,sb)` by
    (qpat_x_assum `A = EL j h` SUBST_ALL_TAC >>
     `j <= j /\ j < LENGTH h` by decide_tac >>
     drule_all ptr_transcript_historical_placement >>
     strip_tac >> metis_tac[]) >>
  `ptr_ledger_source_activations vs C (TAKE (SUC j) h) (EL j h) tsj rj` by
    metis_tac[ptr_source_ownership_caches, ptr_source_birth_caches_activations] >>
  `LENGTH tsj = SUC (LENGTH A.po_stack) /\ ALL_DISTINCT tsj` by
    metis_tac[ptr_source_activations_length, ptr_source_activations_distinct] >>
  `frame_reachable vs C A.po_stack A.po_params A.po_prov A.po_taint
    A.po_fn A.po_inst A.po_state` by
    metis_tac[ptr_source_activations_sound, ptr_chrono_history_reachable,
      ptr_observation_reachable_def] >>
  `MEM owner C.ctx_functions` by
    (drule_all ptr_frame_table_source >> strip_tac >>
     Cases_on `e = LENGTH A.po_stack`
     >- (simp[ptr_owner_view_def] >> metis_tac[]) >>
     `MEM (ptr_owner_view e A) A.po_stack` by
       (simp[ptr_owner_view_def] >> irule EL_MEM >>
        qpat_x_assum `A = EL j h` (fn th => fs[th]) >> decide_tac) >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `lookup_function owner.fn_name C.ctx_functions = SOME owner` by
    (fs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def] >> metis_tac[lookup_function_member_iff]) >>
  drule_all ptr_stage_lookup_origin >> strip_tac >>
  `fn' = owner /\ p = pb` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  qpat_x_assum `fn' = owner` SUBST_ALL_TAC >>
  `fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
   lookup_function fn.fn_name C.ctx_functions = SOME fn /\
   lookup_function fn.fn_name C'.ctx_functions = SOME out.fpo_function /\
   ctx_fn_names observed.cu_context = ctx_fn_names C /\
   o1_walk_view rpolicy 2 C' fn observed` by fs[ptr_demand_interval_def] >>
  `owner.fn_eom = NONE /\ fn_ptr_ok P owner /\ wf_function owner /\
   ssa_form owner /\ all_reachable owner /\ fn_inst_wf owner /\
   EVERY inst_wf (fn_insts owner) /\ ptr_history_cfg_ok owner (cfg_analyze owner) /\
   MEM (Allocation bid,pb,sb) out'.fpo_function.fn_mems_used /\
   ?reservedB itemsB.
     concretize_function_fuel_in_context (concretize_memloc_fuel owner)
       observed'.cu_context reservedB owner = SOME out'.fpo_function /\
     static_alloca_items owner = SOME itemsB /\ MEM (Allocation bid,sb) itemsB /\
     (!c p size. MEM (c,p,size) (imported_mems_used observed'.cu_context owner) ==>
       ~MEM c (MAP (\i. Allocation i.inst_id)
         (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts owner))))` by
    (irule ptr_demand_owner_layout >>
     goal_assum (drule_at (Pat `ptr_demand_interval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `fn_pass_step _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (_,_)`)) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `fn.fn_eom = NONE /\ fn_ptr_ok P fn /\ wf_function fn /\
   ssa_form fn /\ all_reachable fn /\ fn_inst_wf fn /\
   EVERY inst_wf (fn_insts fn) /\ ptr_history_cfg_ok fn (cfg_analyze fn) /\
   MEM (Allocation aid,pa,sz) out.fpo_function.fn_mems_used /\
   ?reservedA itemsA.
     concretize_function_fuel_in_context (concretize_memloc_fuel fn)
       observed.cu_context reservedA fn = SOME out.fpo_function /\
     static_alloca_items fn = SOME itemsA /\ MEM (Allocation aid,sz) itemsA /\
     (!c p size. MEM (c,p,size) (imported_mems_used observed.cu_context fn) ==>
       ~MEM c (MAP (\i. Allocation i.inst_id)
         (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn))))` by
    (irule ptr_demand_owner_layout >>
     goal_assum (drule_at (Pat `ptr_demand_interval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `fn_pass_step _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (_,_)`)) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  qpat_x_assum `A = EL j h` (fn th => SUBST_ALL_TAC (SYM th) >> mk_asm "observation" th) >>
  `0 < sz /\ bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn` by
    (fs[ptr_demand_interval_def] >> decide_tac) >>
  `EL (LENGTH A.po_stack-d) tsj = token` by
    (qpat_x_assum `EL (LENGTH A.po_stack-d) (FST (EL j H)) = token` mp_tac >> simp[]) >>
  Cases_on `e = d`
  >- (qpat_x_assum `e = d` SUBST_ALL_TAC >>
      `tokB = token /\ owner = fn /\ bid <> aid /\
       out'.fpo_function = out.fpo_function /\ itemsB = itemsA` by
        metis_tac[optionTheory.SOME_11] >>
      Cases_on `d = LENGTH A.po_stack`
      >- suspend "active_same_depth" >>
      `d < LENGTH A.po_stack` by
        (qpat_x_assum `d <= LENGTH A.po_stack` mp_tac >>
         qpat_x_assum `d <> LENGTH A.po_stack` mp_tac >> decide_tac) >>
      `SUC (LENGTH A.po_stack-(d+1)) = LENGTH A.po_stack-d` by
        (qpat_x_assum `d < LENGTH A.po_stack` mp_tac >> simp[]) >>
      `LENGTH A.po_stack-(d+1) < LENGTH A.po_stack /\
       EL (SUC (LENGTH A.po_stack-(d+1))) tsj = tokB /\
       fn = (EL (LENGTH A.po_stack-(d+1)) A.po_stack).cf_fn` by
        (simp[] >> qpat_x_assum `(ptr_owner_view d A).cf_fn = fn` mp_tac >>
         simp[ptr_owner_view_def]) >>
      `EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions` by
        fs[ptr_demand_interval_def] >>
      drule_all ptr_source_tagged_owner_call_liveset >>
      disch_then (qspec_then `observed.cu_context` strip_assume_tac) >>
      `MEM ((ptr_owner_view d A).cf_state.vs_current_bb,
            (ptr_owner_view d A).cf_state.vs_inst_idx) xs'` by
        simp[ptr_owner_view_def] >>
      `MEM (Allocation bid,sb) itemsA /\
       MEM (Allocation bid,pb,sb) out.fpo_function.fn_mems_used` by metis_tac[] >>
      qpat_x_assum `fn = (EL _ A.po_stack).cf_fn` kall_tac >>
      qpat_x_assum `bp = bp_analyze_fuel _ _ _` SUBST_ALL_TAC >>
      irule ptr_output_local_local_separation >> simp[] >>
      goal_assum (drule_at (Pat `concretize_function_fuel_in_context _ _ _ fn = SOME out.fpo_function`)) >>
      goal_assum (drule_at (Pat `fn_pass_step _ _ observed s fn out`)) >>
      simp[] >>
      qexistsl [`P`,`Allocation aid`,
        `((ptr_owner_view d A).cf_state.vs_current_bb,
          (ptr_owner_view d A).cf_state.vs_inst_idx)`,`Allocation bid`] >>
      simp[] >> metis_tac[]) >>
  suspend "distinct_depths"
QED

Resume ptr_demand_other_owner_separation[active_same_depth]:
  `fn = A.po_fn /\ tokB = HD tsj` by
    (fs[ptr_owner_view_def, GSYM HD] >> metis_tac[]) >>
  `EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions` by
    fs[ptr_demand_interval_def] >>
  `dv IN pointer_derived_vars fn (ptr_bp_alloc_roots fn bid)` by
    (irule (INST_TYPE [alpha |-> ``:num``] ptr_tag_roots_local_wf) >> simp[] >>
     goal_assum (drule_at (Pat `FLOOKUP TGj dv = SOME (_,_)`)) >>
     qexists `PTj` >> conj_tac
     >- (rpt strip_tac >> spose_not_then strip_assume_tac >>
         `MEM (SOME (tokB,bid)) PTj` by metis_tac[EL_MEM] >>
         drule_all ptr_source_params_fresh_current >> simp[]) >>
     drule_all ptr_source_tag_roots_current >>
     disch_then (qspec_then `(tokB,bid)` mp_tac) >> simp[]) >>
  `!i. MEM i (fn_insts fn) ==>
    MEM i (bp_scan_insts fn (cfg_analyze fn).cfg_dfs_pre)` by
    metis_tac[bp_scan_production_complete] >>
  `?off. MEM (Ptr (Allocation bid) off)
    (bp_get_ptrs (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) dv)` by
    (irule ptr_bp_production_coverage >> metis_tac[]) >>
  `MEM (Allocation bid) (find_base_allocas_opt bp (inst_write_op A.po_inst))` by
    (asm_rewrite_tac[] >>
     simp[find_base_allocas_opt_def, GSYM bp_bases_find_base_allocas, bp_bases_def, MEM_MAP] >>
     metis_tac[ptr_base_def]) >>
  `active_inst fn A.po_inst A.po_state` by
    (`ptr_observation_reachable vs C A` by simp[ptr_observation_reachable_def] >>
     drule (cj 1 ptr_owner_view_active) >>
     disch_then (qspec_then `LENGTH A.po_stack` mp_tac) >>
     simp[ptr_owner_view_def]) >>
  `?ys. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
      observed.cu_context fn bp (cfg_analyze fn)) (Allocation bid) = SOME ys /\
    MEM (A.po_state.vs_current_bb,A.po_state.vs_inst_idx) ys` by
    (irule ptr_active_write_liveset >> metis_tac[]) >>
  `MEM (A.po_state.vs_current_bb,A.po_state.vs_inst_idx) xs` by
    (qpat_x_assum `MEM (_,_) xs` mp_tac >> simp[ptr_owner_view_def]) >>
  `MEM (Allocation bid,sb) itemsA /\
   MEM (Allocation bid,pb,sb) out.fpo_function.fn_mems_used` by metis_tac[] >>
  qpat_x_assum `fn = A.po_fn` kall_tac >>
  qpat_x_assum `bp = bp_analyze_fuel _ _ _` SUBST_ALL_TAC >>
  irule ptr_output_local_local_separation >> simp[] >>
  goal_assum (drule_at (Pat `concretize_function_fuel_in_context _ _ _ fn = SOME out.fpo_function`)) >>
  goal_assum (drule_at (Pat `fn_pass_step _ _ observed s fn out`)) >>
  simp[] >>
  qexistsl [`P`,`Allocation aid`,
    `(A.po_state.vs_current_bb,A.po_state.vs_inst_idx)`,`Allocation bid`] >>
  simp[] >> metis_tac[]
QED

Resume ptr_demand_other_owner_separation[distinct_depths]:
  `ptr_chrono_history vs C h endpoint` by
    (drule ptr_structural_transcript_erasure >>
     strip_tac >> drule ptr_structural_trace_source >> simp[]) >>
  `j < LENGTH h` by decide_tac >>
  Cases_on `d < e`
  >- (`d < LENGTH A.po_stack /\
       LENGTH A.po_stack-e <= LENGTH A.po_stack-(d+1)` by decide_tac >>
      `ptr_owner_view d A = EL (LENGTH A.po_stack-(d+1)) A.po_stack` by
        simp[ptr_owner_view_def] >>
      `EL (LENGTH A.po_stack-e)
        ((A.po_fn,A.po_state)::MAP (\f. (f.cf_fn,f.cf_state)) A.po_stack) =
        (owner,(ptr_owner_view e A).cf_state)` by
        (Cases_on `e = LENGTH A.po_stack` >>
         simp[ptr_owner_view_def] >>
         `0 < LENGTH A.po_stack-e /\
          PRE (LENGTH A.po_stack-e) = LENGTH A.po_stack-(e+1)` by decide_tac >>
         simp[EL_MAP, EL_CONS]) >>
      qpat_x_assum `bp = bp_analyze_fuel _ _ _` SUBST_ALL_TAC >>
      `?pc. MEM (Allocation bid,pc,sb) (imported_mems_used observed.cu_context fn) /\
        reserved_intervals_disjoint (pa,sz) (pc,sb)` by
        (irule ptr_output_suspended_descendant_separation >> simp[] >>
         (conj_tac >- first_assum ACCEPT_TAC) >>
         (conj_tac >- (qexists `P` >> asm_rewrite_tac[])) >>
         goal_assum (drule_at (Pat `ptr_chrono_history _ _ _ _`)) >>
         goal_assum (drule_at (Pat `concretize_function_fuel_in_context _ _ _ fn = SOME out.fpo_function`)) >>
         goal_assum (drule_at (Pat `fn_pass_step _ _ observed s fn out`)) >>
         goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
         qexists `Allocation aid` >>
         goal_assum (drule_at (Pat `FLOOKUP _ (Allocation aid) = SOME xs`)) >>
         qexistsl [`db`,`owner`,`(ptr_owner_view e A).cf_state`,
           `LENGTH A.po_stack-e`,`LENGTH A.po_stack-(d+1)`,`names`,`j`] >>
         asm "observation" (fn th => rewrite_tac[GSYM th]) >>
         asm_rewrite_tac[] >>
         qpat_assum `ptr_owner_view d A = _` (fn th => rewrite_tac[GSYM th]) >>
         asm_rewrite_tac[] >> simp[]) >>
      `MEM (Allocation bid,pc,sb) out.fpo_function.fn_mems_used` by
        (irule ptr_stage_import_retained >>
         goal_assum (drule_at (Pat `fn_pass_step _ _ observed s fn out`)) >>
         asm_rewrite_tac[] >> metis_tac[]) >>
      `MEM out.fpo_function C'.ctx_functions` by metis_tac[lookup_function_MEM] >>
      `FLOOKUP positions (Allocation bid) = SOME (pc,sb)` by
        (fs[ptr_stage_placements_def] >> metis_tac[]) >>
      `pc = pb` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
      metis_tac[]) >>
  `e < d /\ e < LENGTH A.po_stack /\
   LENGTH A.po_stack-d <= LENGTH A.po_stack-(e+1)` by decide_tac >>
  `ptr_owner_view e A = EL (LENGTH A.po_stack-(e+1)) A.po_stack` by
    simp[ptr_owner_view_def] >>
  `EL (LENGTH A.po_stack-d)
    ((A.po_fn,A.po_state)::MAP (\f. (f.cf_fn,f.cf_state)) A.po_stack) =
    (fn,(ptr_owner_view d A).cf_state)` by
    (Cases_on `d = LENGTH A.po_stack`
     >- (simp[ptr_owner_view_def] >>
         qpat_x_assum `(ptr_owner_view d A).cf_fn = fn` mp_tac >>
         simp[ptr_owner_view_def]) >>
     simp[ptr_owner_view_def] >>
     `0 < LENGTH A.po_stack-d /\
      PRE (LENGTH A.po_stack-d) = LENGTH A.po_stack-(d+1)` by decide_tac >>
     simp[EL_MAP, EL_CONS] >>
     qpat_x_assum `(ptr_owner_view d A).cf_fn = fn` mp_tac >>
     simp[ptr_owner_view_def]) >>
  `SUC (LENGTH A.po_stack-(e+1)) = LENGTH A.po_stack-e` by
    (qpat_x_assum `e < LENGTH A.po_stack` mp_tac >> simp[]) >>
  `EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions` by
    fs[ptr_demand_interval_def] >>
  `owner = (EL (LENGTH A.po_stack-(e+1)) A.po_stack).cf_fn` by metis_tac[] >>
  pop_assum (mk_asm "owner_function") >>
  qpat_x_assum `owner = (ptr_owner_view e A).cf_fn` kall_tac >>
  `?pc. MEM (Allocation aid,pc,sz) (imported_mems_used observed'.cu_context owner) /\
    reserved_intervals_disjoint (pb,sb) (pc,sz)` by
    (irule ptr_output_tagged_ancestor_destination_separation >> simp[] >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- (qexists `P` >> asm_rewrite_tac[])) >>
     goal_assum (drule_at (Pat `ptr_chrono_history _ _ _ _`)) >>
     goal_assum (drule_at (Pat `concretize_function_fuel_in_context _ _ _ owner = SOME out'.fpo_function`)) >>
     goal_assum (drule_at (Pat `fn_pass_step _ _ observed' s' owner out'`)) >>
     goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
     asm "observation" (fn th =>
       qpat_assum `ptr_source_ownership _ _ _ A _ _ _ _ _ _`
         (assume_tac o PURE_REWRITE_RULE [th])) >>
     goal_assum (drule_at (Pat `ptr_source_ownership _ _ _ (EL j h) _ _ _ _ _ _`)) >>
     qexists `bid` >>
     qexistsl [`b`,`fn`,`(ptr_owner_view d A).cf_state`,
       `LENGTH A.po_stack-d`,`LENGTH A.po_stack-(e+1)`,`names`,`dv`] >>
     asm "observation" (fn th => rewrite_tac[GSYM th]) >>
     asm_rewrite_tac[] >> asm "owner_function" (fn th => simp[th])) >>
  `MEM (Allocation aid,pc,sz) out'.fpo_function.fn_mems_used` by
    (irule ptr_stage_import_retained >>
     goal_assum (drule_at (Pat `fn_pass_step _ _ observed' s' owner out'`)) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `MEM out'.fpo_function C'.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `FLOOKUP positions (Allocation aid) = SOME (pc,sz)` by
    (fs[ptr_stage_placements_def] >> metis_tac[]) >>
  `pc = pa` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  fs[staticLayoutDefsTheory.reserved_intervals_disjoint_def] >> decide_tac
QED

Finalise ptr_demand_other_owner_separation

(* Conditional paired ordinary-write consumer. Operand classification, word
   bounds, and paired CALL returndata lengths are inputs, not consequences
   of the structural transcript. The initializing writer w is unchanged. *)
Theorem ptr_demand_ordinary_write_exclusion:
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\ w < j /\ j+1 < LENGTH h /\
  EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
  ptr_stage_placements C' positions /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  fixed_region_reserved lo C /\
  ptr_lookup_transport bj positions (op_prov TGj ops.iao_ofst)
    (op_taint (EL j h).po_taint ops.iao_ofst)
    (eval_operand ops.iao_ofst src) (eval_operand ops.iao_ofst tgt) /\
  ptr_lookup_transport bj positions (op_prov TGj sizeop)
    (op_taint (EL j h).po_taint sizeop)
    (eval_operand sizeop src) (eval_operand sizeop tgt) /\
  (!op. IS_SOME (eval_operand op src) = IS_SOME (eval_operand op tgt)) /\
  src.vs_labels = tgt.vs_labels /\
  mem_write_ops (EL j h).po_inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
  ((?u. ops.iao_ofst = Var u) \/ (?y. ops.iao_ofst = Lit y)) /\
  ((?u. sizeop = Var u) \/ (?y. sizeop = Lit y)) /\
  eval_operand ops.iao_ofst src = SOME x /\ eval_operand sizeop src = SOME z /\
  op_prov TGj sizeop = NONE /\ op_taint (EL j h).po_taint sizeop = {} /\
  (MEM (EL j h).po_inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] ==>
    LENGTH posts.vs_returndata = LENGTH postt.vs_returndata) /\
  b+k NOTIN range_bytes (step_writes (EL j h).po_inst src posts) /\
  ((op_prov TGj ops.iao_ofst = NONE /\
    op_taint (EL j h).po_taint ops.iao_ofst = {} /\ w2n x + w2n z <= lo) \/
   (?dv tokB bid db sb pb.
     ops.iao_ofst = Var dv /\ FLOOKUP TGj dv = SOME (tokB,bid) /\
     FLOOKUP (EL j h).po_prov dv = SOME (db,sb) /\
     FLOOKUP positions (Allocation bid) = SOME (pb,sb) /\
     db <= w2n x /\ w2n x + w2n z <= db+sb /\ pb+sb < dimword(:256))) ==>
  pa+k NOTIN range_bytes (step_writes (EL j h).po_inst tgt postt)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `_ \/ _` strip_assume_tac
  >- (drule_all ptr_demand_fixed_write_exclusion >> simp[]) >>
  drule_all ptr_demand_interval_snapshot >> strip_tac >>
  `EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions`
    by fs[ptr_demand_interval_def] >>
  `FLOOKUP bj (tokB,bid) = SOME (db,sb)` by
    (drule_all ptr_source_ownership_prov_erases >>
     simp[concretizePtrPrefixLedgerTheory.ptr_ledger_erases_def] >> strip_tac >>
     qpat_x_assum `!v. FLOOKUP (EL j h).po_prov v = _`
       (qspec_then `dv` mp_tac) >> simp[ptr_owner_project_def]) >>
  `op_prov TGj ops.iao_ofst = SOME (tokB,bid)` by simp[op_prov_def] >>
  Cases_on `tokB = token /\ bid = aid`
  >- (qpat_x_assum `tokB = token /\ bid = aid` strip_assume_tac >>
      qpat_x_assum `tokB = token` SUBST_ALL_TAC >>
      qpat_x_assum `bid = aid` SUBST_ALL_TAC >>
      `db = b /\ sb = sz /\ pb = pa` by metis_tac[SOME_11, PAIR_EQ] >>
      qpat_x_assum `db = b` SUBST_ALL_TAC >>
      qpat_x_assum `sb = sz` SUBST_ALL_TAC >>
      qpat_x_assum `pb = pa` SUBST_ALL_TAC >>
      drule_all ptr_demand_same_owner_write_exclusion >> simp[]) >>
  spose_not_then assume_tac >>
  drule_all ptr_write_transport_owner_containment >> strip_tac >>
  first_x_assum (qspec_then `postt` strip_assume_tac) >>
  `pb <= pa+k /\ pa+k < pb+sb /\ 0 < sb` by
    (first_x_assum drule >> decide_tac) >>
  `inst_write_op (EL j h).po_inst = SOME (Var dv)` by
    simp[inst_write_op_def] >>
  `reserved_intervals_disjoint (pa,sz) (pb,sb)` by
    (irule ptr_demand_other_owner_separation >> simp[] >>
     goal_assum (drule_at (Pat `ptr_demand_interval _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `inst_write_op _ = SOME _`)) >>
     goal_assum (drule_at (Pat `EL _ H = _`)) >>
     goal_assum (drule_at (Pat `ptr_stage_placements _ _`)) >>
     simp[] >> metis_tac[]) >>
  pop_assum mp_tac >>
  simp[staticLayoutDefsTheory.reserved_intervals_disjoint_def] >>
  `k < sz` by fs[ptr_demand_interval_def] >> decide_tac
QED
