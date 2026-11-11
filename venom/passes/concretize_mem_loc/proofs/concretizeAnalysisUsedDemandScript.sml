Theory concretizeAnalysisUsedDemand
Ancestors concretizeAnalysisTemporalDemand concretizeAnalysisIncomingDemand
  concretizeAnalysisImportedDemand concretizeAnalysisLivenessPaths
  concretizePtrOrdering concretizeMemLocDefs frameJointTrace frameActivationCache
  contextCodegenRel venomWf finite_map list pred_set enumeral o1PassContract
  frameOriginHistory frameOriginReachable frameAllocationOwnership frameJointTransition
  concretizeAnalysisScanCoverage ptrDiscipline concretizeAnalysisLivenessTransfer
  concretizeAnalysisWriteSafety frameHistoryCfg

(* The only conversion from analysis facts to the executable allocator input. *)
Theorem context_liveset_intersection:
  ml_iterate_fuel (concretize_memloc_fuel fn) bp
    (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used ctx nm)))
    (\a. if context_alloca_size fn (imported_mems_used ctx fn) a = 0 then NONE
         else SOME (context_alloca_size fn (imported_mems_used ctx fn) a))
    [] (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  active_inst fn inst s /\
  MEM a (ml_lookup la (s.vs_current_bb,s.vs_inst_idx)) /\
  MEM a (ml_lookup us (s.vs_current_bb,s.vs_inst_idx)) ==>
  ?addrs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
    ctx fn bp (cfg_analyze fn)) a = SOME addrs /\
    MEM (s.vs_current_bb,s.vs_inst_idx) addrs
Proof
  strip_tac >>
  simp[context_mem_livesets_def, mem_liveness_analyze_fuel_def] >>
  gvs[active_inst_def] >>
  qpat_x_assum `bb.bb_label = _` (fn th => fs[GSYM th]) >>
  irule ml_production_marked_membership >> simp[] >>
  goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[ptr_incr_ssort_ordered, OL]
QED

Theorem activation_context_liveset_intersection:
  ml_iterate_fuel (concretize_memloc_fuel fn) bp
    (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used ctx nm)))
    (\a. if context_alloca_size fn (imported_mems_used ctx fn) a = 0 then NONE
         else SOME (context_alloca_size fn (imported_mems_used ctx fn) a))
    [] (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us) /\
  activation_location q d fn p /\
  MEM a (ml_lookup la p) /\ MEM a (ml_lookup us p) ==>
  ?addrs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
    ctx fn bp (cfg_analyze fn)) a = SOME addrs /\ MEM p addrs
Proof
  Cases_on `q` >> simp[activation_location_def] >> rpt strip_tac >>
  gvs[] >> metis_tac[context_liveset_intersection]
QED

Theorem concretize_untainted_local_read_liveset:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  joint_trace vs0 C q0 es qs q /\ m <= n /\ n <= j /\ j <= LENGTH es /\
  EL m (q0::qs) = JointConfig stkm PGm Gm tnm fn instm sm omsm omm hsm hm /\
  active_inst fn instm sm /\ LENGTH stkm = d /\
  ml_used_gen (Allocation aid) bp
    (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed.cu_context nm))) instm /\
  (!k. m <= k /\ k <= n ==> d <= activation_depth (EL k (q0::qs))) /\
  EL n (q0::qs) = JointConfig stk0 PG0 G0 tn0 fn inst0 s0 oms0 om0 hs0 h0 /\
  LENGTH stk0 = d /\ activation_location (EL n (q0::qs)) d fn p /\
  EL j (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\ LENGTH stk = d /\
  FLOOKUP om v = SOME (OriginLocal aid,(b,sz)) /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  b <= byte /\ byte < b + sz /\ byte IN joint_reads (EL j (q0::qs)) /\ lo <= byte /\
  byte NOTIN joint_mem_taint (EL j (q0::qs)) /\ ~in_revert_forward fn s /\
  (!k. n <= k /\ k < j ==> byte NOTIN joint_writes (EL k (q0::qs)) (EL k es)) ==>
  ?addrs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
    observed.cu_context fn bp (cfg_analyze fn)) (Allocation aid) = SOME addrs /\ MEM p addrs
Proof
  strip_tac >>
  `wf_function fn /\ all_reachable fn` by
    (`MEM fn C.ctx_functions` by
       (drule trace_config_at >> disch_then (qspec_then `m` mp_tac) >>
        impl_tac >- decide_tac >> simp[] >>
        strip_tac >> gvs[joint_config_reachable_def] >>
        drule joint_origin_history_erasure >> strip_tac >>
        drule origin_frame_erasure >> strip_tac >>
        metis_tac[frame_allocation_ownership]) >>
     gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM]) >>
  `?la us. ml_iterate_fuel (concretize_memloc_fuel fn) bp
    (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed.cu_context nm)))
    (\a. if context_alloca_size fn (imported_mems_used observed.cu_context fn) a = 0
         then NONE else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a))
    [] (cfg_analyze fn) fn FEMPTY FEMPTY = (la,us)` by
    metis_tac[pairTheory.pair_CASES] >>
  `MEM (Allocation aid) (ml_lookup la (s0.vs_current_bb,s0.vs_inst_idx))` by
    (gvs[] >> irule concretize_untainted_local_read_liveat >> simp[] >>
     goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >>
     simp[ptr_incr_ssort_ordered, OL] >>
     goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `o1_walk_view _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `callee_first _ _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP om _ = _`)) >>
     goal_assum (drule_at (Pat `mem_read_ops _ = _`)) >>
     goal_assum (drule_at (Pat `EL n _ = _`)) >>
     goal_assum (drule_at (Pat `EL j _ = _`)) >>
     qexists_tac `byte` >> simp[] >> metis_tac[]) >>
  `p = (s0.vs_current_bb,s0.vs_inst_idx)` by
    gvs[activation_location_def] >>
  `MEM (Allocation aid) (ml_lookup us p)` by
    (irule joint_activation_used_past_generator >> simp[] >>
     goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >>
     simp[ptr_incr_ssort_ordered, OL] >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `active_inst _ _ _`)) >>
     goal_assum (drule_at (Pat `EL _ _ = _`)) >>
     qexists_tac `n` >> gvs[] >> decide_tac) >>
  irule activation_context_liveset_intersection >> conj_tac
  >- (goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >> simp[]) >>
  goal_assum (drule_at (Pat `activation_location _ _ _ _`))
QED

Theorem concretize_untainted_incoming_read_liveset:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs q /\ n <= j /\ j <= LENGTH es /\
  EL j (q0::qs) = JointConfig stk PG G tn current inst s oms om hs h /\
  FLOOKUP om v = SOME (OriginParameter param,(b,sz)) /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  b <= byte /\ byte < b + sz /\ lo <= byte /\ byte IN joint_reads (EL j (q0::qs)) /\
  byte NOTIN joint_mem_taint (EL j (q0::qs)) /\ ~in_revert_forward current s /\
  (!t. n <= t /\ t < j ==> byte NOTIN joint_writes (EL t (q0::qs)) (EL t es)) ==>
  ?k aid owner d.
    k < LENGTH stk /\ owner = (EL k stk).cf_fn /\ d = LENGTH stk - SUC k /\
    FLOOKUP (EL k stk).cf_state.vs_allocas aid = SOME (b,sz) /\
    activation_cache (EL n (q0::qs)) d owner aid (b,sz) /\
    (!p observed bp m stkm PGm Gm tnm instm sm omsm omm hsm hm.
      activation_location (EL n (q0::qs)) d owner p /\
      o1_walk_view rpolicy 2 C' owner observed /\
      bp = bp_analyze_fuel (concretize_memloc_fuel owner) (cfg_analyze owner) owner /\
      m <= n /\
      EL m (q0::qs) = JointConfig stkm PGm Gm tnm owner instm sm omsm omm hsm hm /\
      active_inst owner instm sm /\ LENGTH stkm = d /\
      ml_used_gen (Allocation aid) bp
        (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed.cu_context nm))) instm /\
      (!t. m <= t /\ t <= n ==> d <= activation_depth (EL t (q0::qs))) ==>
      ?addrs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel owner)
        observed.cu_context owner bp (cfg_analyze owner)) (Allocation aid) = SOME addrs /\ MEM p addrs)
Proof
  strip_tac >> drule_all concretize_untainted_incoming_read_liveat >> strip_tac >>
  qexistsl_tac [`k`,`aid`,`owner`,`d`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `bp = _` SUBST_ALL_TAC >>
  qpat_x_assum `owner = _` kall_tac >> qpat_x_assum `d = _` kall_tac >>
  `MEM owner C.ctx_functions` by
    (drule trace_config_at >> disch_then (qspec_then `m` mp_tac) >>
     impl_tac >- decide_tac >> simp[] >>
     strip_tac >> gvs[joint_config_reachable_def] >>
     drule joint_origin_history_erasure >> strip_tac >>
     drule origin_frame_erasure >> strip_tac >>
     metis_tac[frame_allocation_ownership]) >>
  `wf_function owner /\ all_reachable owner` by
    gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `?la us. ml_iterate_fuel (concretize_memloc_fuel owner)
    (bp_analyze_fuel (concretize_memloc_fuel owner) (cfg_analyze owner) owner)
    (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed.cu_context nm)))
    (\a. if context_alloca_size owner (imported_mems_used observed.cu_context owner) a = 0
         then NONE else SOME (context_alloca_size owner (imported_mems_used observed.cu_context owner) a))
    [] (cfg_analyze owner) owner FEMPTY FEMPTY = (la,us)` by
    metis_tac[pairTheory.pair_CASES] >>
  `MEM (Allocation aid) (ml_lookup la p)` by
    (first_x_assum irule >> simp[ptr_incr_ssort_ordered, OL] >>
     goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >>
     simp[ptr_incr_ssort_ordered, OL]) >>
  `MEM (Allocation aid) (ml_lookup us p)` by
    (irule joint_activation_used_past_generator >> simp[] >>
     goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >>
     simp[ptr_incr_ssort_ordered, OL] >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `active_inst _ _ _`)) >>
     goal_assum (drule_at (Pat `EL _ _ = _`)) >>
     qexists_tac `n` >> gvs[] >> decide_tac) >>
  irule activation_context_liveset_intersection >> conj_tac
  >- (goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >> simp[]) >>
  goal_assum (drule_at (Pat `activation_location _ _ _ _`))
QED

Theorem joint_local_write_used_generator:
  joint_config_reachable vs0 ctx
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  o1_ctx_shape ctx /\ ptr_discipline lo ctx vs0 /\
  EVERY ssa_form ctx.ctx_functions /\ EVERY all_reachable ctx.ctx_functions /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var u /\
  FLOOKUP om u = SOME (OriginLocal aid,site) ==>
  ml_used_gen (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) mems inst
Proof
  strip_tac >> gvs[joint_config_reachable_def] >>
  drule joint_origin_history_erasure >> strip_tac >>
  `EVERY wf_function ctx.ctx_functions` by
    gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `MEM fn ctx.ctx_functions` by
    (drule joint_origin_history_projection >> strip_tac >>
     metis_tac[frame_history_cfg_invariant]) >>
  `wf_function fn /\ all_reachable fn /\ ssa_form fn /\
   EVERY wf_function ctx.ctx_functions` by
    gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `Allocation aid IN bp_bases
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) u` by
    (irule origin_frame_current_production_coverage >>
     fs[ptr_discipline_def] >>
     `EVERY (fn_ptr_ok P) ctx.ctx_functions` by
       (fs[EVERY_MEM] >> metis_tac[]) >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `MEM (Var u) inst.inst_operands` by metis_tac[write_ops_operand] >>
  simp[ml_used_gen_def, ml_operand_gen_def] >>
  disj1_tac >> qexists_tac `Var u` >> gvs[bp_bases_find_base_allocas]
QED

Theorem concretize_untainted_local_read_past_write_liveset:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn /\
  joint_trace vs0 C q0 es qs q /\ m <= n /\ n <= j /\ j <= LENGTH es /\
  EL m (q0::qs) = JointConfig stkm PGm Gm tnm fn instm sm omsm omm hsm hm /\
  active_inst fn instm sm /\ LENGTH stkm = d /\
  mem_write_ops instm = SOME opsm /\ opsm.iao_ofst = Var u /\
  FLOOKUP omm u = SOME (OriginLocal aid,site) /\
  (!k. m <= k /\ k <= n ==> d <= activation_depth (EL k (q0::qs))) /\
  EL n (q0::qs) = JointConfig stk0 PG0 G0 tn0 fn inst0 s0 oms0 om0 hs0 h0 /\
  LENGTH stk0 = d /\ activation_location (EL n (q0::qs)) d fn p /\
  EL j (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\ LENGTH stk = d /\
  FLOOKUP om v = SOME (OriginLocal aid,(b,sz)) /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  b <= byte /\ byte < b + sz /\ byte IN joint_reads (EL j (q0::qs)) /\ lo <= byte /\
  byte NOTIN joint_mem_taint (EL j (q0::qs)) /\ ~in_revert_forward fn s /\
  (!k. n <= k /\ k < j ==> byte NOTIN joint_writes (EL k (q0::qs)) (EL k es)) ==>
  ?addrs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
    observed.cu_context fn bp (cfg_analyze fn)) (Allocation aid) = SOME addrs /\ MEM p addrs
Proof
  strip_tac >>
  `joint_config_reachable vs0 C
    (JointConfig stkm PGm Gm tnm fn instm sm omsm omm hsm hm)` by
    metis_tac[trace_config_at, arithmeticTheory.LESS_EQ_TRANS] >>
  `ml_used_gen (Allocation aid) bp
    (\nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed.cu_context nm))) instm` by
    (gvs[] >> irule joint_local_write_used_generator >>
     goal_assum (drule_at (Pat `joint_config_reachable _ _ _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP omm _ = _`)) >>
     goal_assum (drule_at (Pat `mem_write_ops _ = _`)) >>
     goal_assum (drule_at (Pat `ptr_discipline _ _ _`)) >> simp[]) >>
  drule_all concretize_untainted_local_read_liveset >> simp[]
QED
