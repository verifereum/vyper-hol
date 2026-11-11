Theory concretizeAnalysisSafeKill
Ancestors venomWfProps
  concretizeAnalysisRuntimeSizes concretizeAnalysisReverseInstance
  concretizeAnalysisSuccessfulWrites concretizePtrReadCoverage
  concretizeAnalysisExclusiveWriters concretizeAnalysisKillApplicability
  frameHistoryDefinitions concretizePtrParamSupport contextCodegenRel
  removeUnusedSsaProofs venomInst concretizeMemLocDefs basePtrDefs cfgAnalysis
  frameOriginHistory frameOriginReachable o1PassContract ptrDiscipline
  venomWf memLocDefs finite_map list pair

Theorem concretize_production_kill_covers:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  o1_run_state_ok vs0 /\
  joint_origin_history vs0 C stk PG G tn fn inst s oms om hs h /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ all_reachable fn /\
  o1_walk_view rpolicy 2 C' fn observed /\
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  sizes = (\a. if context_alloca_size fn
    (imported_mems_used observed.cu_context fn) a = 0 then NONE
    else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a)) /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  MEM (Var v) inst.inst_operands /\ inst.inst_opcode <> PHI /\
  ptr_ml_can_kill (Allocation aid) bp sizes inst /\
  step_inst fuel C inst s = OK s' /\ access_ok lo G fn inst s /\
  ~in_revert_forward fn s ==>
  ?b sz. FLOOKUP G v = SOME (b,sz) /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
    !byte. b <= byte /\ byte < b + sz ==>
      byte IN range_bytes (step_writes inst s s')
Proof
  strip_tac >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    metis_tac[joint_origin_history_erasure, origin_frame_erasure] >>
  `EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions` by
    (gvs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[EVERY_MEM, fn_inst_wf_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[]) >>
  `MEM fn C.ctx_functions` by metis_tac[ptr_frame_current_static] >>
  `fn_ptr_ok P fn` by fs[EVERY_MEM] >>
  `active_inst fn inst s` by
    metis_tac[joint_origin_history_projection, frame_history_active] >>
  `MEM inst (fn_insts fn)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[MEM_EL]) >>
  `allocation_exclusive P fn v` by
    (irule production_kill_allocation_exclusive >> metis_tac[]) >>
  `find_base_allocas_opt bp (inst_write_op inst) = [Allocation aid]` by
    gvs[ptr_ml_can_kill_def] >>
  `?site. FLOOKUP om v = SOME (OriginLocal aid,site) /\
    FLOOKUP G v = SOME site /\ FLOOKUP s.vs_allocas aid = SOME site` by
    (irule joint_origin_history_singleton_write_cached_site >> metis_tac[]) >>
  PairCases_on `site` >>
  `context_alloca_size fn (imported_mems_used observed.cu_context fn)
      (Allocation aid) = site1` by
    (drule_all concretize_runtime_context_size >> simp[]) >>
  `inst_write_size inst = SOME site1` by
    (gvs[ptr_ml_can_kill_def] >> metis_tac[]) >>
  qexistsl_tac [`site0`, `site1`] >> simp[] >>
  metis_tac[successful_full_write_covers]
QED

Theorem concretize_protected_cached_byte_no_kill:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  o1_run_state_ok vs0 /\
  joint_origin_history vs0 C stk PG G tn fn inst s oms om hs h /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ all_reachable fn /\
  o1_walk_view rpolicy 2 C' fn observed /\
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  sizes = (\a. if context_alloca_size fn
    (imported_mems_used observed.cu_context fn) a = 0 then NONE
    else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a)) /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  MEM (Var v) inst.inst_operands /\ inst.inst_opcode <> PHI /\
  step_inst fuel C inst s = OK s' /\ access_ok lo G fn inst s /\
  ~in_revert_forward fn s /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  b <= byte /\ byte < b + sz /\
  byte NOTIN range_bytes (step_writes inst s s') ==>
  ~ptr_ml_can_kill (Allocation aid) bp sizes inst
Proof
  rpt strip_tac >> drule_all concretize_production_kill_covers >>
  strip_tac >> gvs[]
QED
