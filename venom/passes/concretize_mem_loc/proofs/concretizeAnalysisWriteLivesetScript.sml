Theory concretizeAnalysisWriteLiveset
Ancestors concretizeAnalysisStoreMark concretizeAnalysisPastUse
  concretizeAnalysisUsedDemand concretizeAnalysisIncomingDemand concretizeAnalysisTemporalDemand
  frameWriteOwnership frameActivationSeparation frameActivationCache
  concretizeAnalysisScanCoverage frameOriginCacheReach concretizePtrOrdering
  concretizeAnalysisLivenessPaths venomInst concretizePtrIncomingOrigins
  frameOriginHistory frameOriginReachable ptrDiscipline o1PassContract
  concretizeMemLocDefs venomWf finite_map list arithmetic
  contextCodegenRel frameJointTrace unitTransformDefs frameJointTransition frameAllocationOwnership

Theorem concretize_write_owner_liveset:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  o1_walk_view rpolicy 2 C' owner observed /\
  joint_config_reachable vs0 C (JointConfig stk PG G tn fn inst s oms om hs h) /\
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h) ev qnext /\
  ~in_revert_forward fn s /\
  byte IN joint_writes (JointConfig stk PG G tn fn inst s oms om hs h) ev /\ lo <= byte /\
  activation_cache (JointConfig stk PG G tn fn inst s oms om hs h) d owner aid (b,sz) /\
  b <= byte /\ byte < b+sz /\
  activation_location (JointConfig stk PG G tn fn inst s oms om hs h) d owner p ==>
  ?addrs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel owner)
    observed.cu_context owner
    (bp_analyze_fuel (concretize_memloc_fuel owner) (cfg_analyze owner) owner)
    (cfg_analyze owner)) (Allocation aid) = SOME addrs /\ MEM p addrs
Proof
  strip_tac >>
  `vs0.vs_allocas = FEMPTY` by gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `joint_origin_history vs0 C stk PG G tn fn inst s oms om hs h` by
    gvs[joint_config_reachable_def] >>
  `origin_frame_reachable vs0 C stk PG G tn fn inst s oms om` by
    metis_tac[joint_origin_history_erasure] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    metis_tac[origin_frame_erasure] >>
  `access_ok lo G fn inst s` by metis_tac[ptr_discipline_def] >>
  drule_all joint_write_owner_identity >> strip_tac >>
  drule_all origin_frame_current_lookup >> strip_tac >>
  Cases_on `tag`
  >- suspend "local"
  >- suspend "incoming"
  >> suspend "dynamic"
QED

Resume concretize_write_owner_liveset[local]:
  rename1 `FLOOKUP om v = SOME (OriginLocal localid,(b,sz))` >>
  `FLOOKUP s.vs_allocas localid = SOME (b,sz)` by
    metis_tac[origin_frame_current_cache] >>
  `activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
    (LENGTH stk) fn localid (b,sz)` by simp[activation_cache_current] >>
  `d = LENGTH stk /\ owner = fn /\ aid = localid /\ b = b /\ sz = sz` by
    (irule joint_activation_cache_byte_unique >>
     (conj_tac >- (qexists_tac `byte` >> simp[])) >>
     goal_assum (drule_at (Pat `joint_config_reachable _ _ _`)) >> simp[]) >>
  gvs[] >>
  `EVERY wf_function C.ctx_functions` by
    gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `MEM fn C.ctx_functions` by metis_tac[frame_allocation_ownership] >>
  `wf_function fn /\ all_reachable fn /\ ssa_form fn` by metis_tac[EVERY_MEM] >>
  `Allocation aid IN bp_bases
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) v` by
    (drule_all origin_frame_current_production_coverage >> simp[]) >>
  `MEM (Allocation aid) (find_base_allocas_opt
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (inst_write_op inst))` by metis_tac[write_base_marked_key] >>
  gvs[activation_location_def] >>
  simp[context_mem_livesets_def, mem_liveness_analyze_fuel_def] >>
  pairarg_tac >> simp[] >>
  gvs[active_inst_def] >>
  qpat_x_assum `bb.bb_label = _` (fn th => fs[GSYM th]) >>
  irule ml_mark_stores_live_write_at >>
  goal_assum (drule_at (Pat `MEM _ fn.fn_blocks`)) >> simp[]
QED

Resume concretize_write_owner_liveset[incoming]:
  drule_all joint_incoming_production_argument >> strip_tac >>
  `activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
    (LENGTH stk - SUC k) (EL k stk).cf_fn aid' (b,sz)` by
    simp[activation_cache_saved] >>
  `d = LENGTH stk - SUC k /\ owner = (EL k stk).cf_fn /\ aid = aid' /\
    b = b /\ sz = sz` by
    (irule joint_activation_cache_byte_unique >>
     (conj_tac >- (qexists_tac `byte` >> simp[])) >>
     goal_assum (drule_at (Pat `joint_config_reachable _ _ _`)) >> simp[]) >>
  gvs[] >>
  `LENGTH stk - SUC k < LENGTH stk /\
   LENGTH stk - SUC (LENGTH stk - SUC k) = k` by decide_tac >>
  gvs[activation_location_def] >>
  simp[context_mem_livesets_def, mem_liveness_analyze_fuel_def] >>
  pairarg_tac >> simp[] >>
  `MEM (Allocation aid) (ml_lookup liveat
      ((EL k stk).cf_state.vs_current_bb,(EL k stk).cf_state.vs_inst_idx)) /\
   MEM (Allocation aid) (ml_lookup used
      ((EL k stk).cf_state.vs_current_bb,(EL k stk).cf_state.vs_inst_idx))` by
    (first_x_assum irule >> goal_assum (drule_at Any) >>
     simp[ptr_incr_ssort_ordered, enumeralTheory.OL]) >>
  qpat_x_assum `active_inst _ _ _` mp_tac >>
  simp[active_inst_def] >> strip_tac >>
  qpat_x_assum `bb.bb_label = _` (fn th => fs[GSYM th]) >>
  irule ml_production_marked_membership >> simp[] >>
  goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[ptr_incr_ssort_ordered, enumeralTheory.OL]
QED

Resume concretize_write_owner_liveset[dynamic]:
  qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
  simp[ptr_discipline_def] >> strip_tac >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[]) >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[origin_frame_current_not_dynamic]
QED

Finalise concretize_write_owner_liveset
