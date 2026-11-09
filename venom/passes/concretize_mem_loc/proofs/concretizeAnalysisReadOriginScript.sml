Theory concretizeAnalysisReadOrigin
Ancestors venomWfProps
  concretizeAnalysisScanCoverage concretizePtrIncomingOrigins frameOriginCacheReach
  frameAllocationOwnership frameReadOwnership frameJointDemand frameJointTransition frameJointTrace
  frameOriginHistory frameOriginReachable ptrDiscipline o1PassContract
  basePtrDefs cfgAnalysis venomWf venomInst venomInstProps removeUnusedSsaProofs list finite_map pred_set

Theorem joint_current_production_origin:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY wf_function ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\ ~ctx_has_dalloca ctx /\
  wf_function fn /\ all_reachable fn /\ ssa_form fn /\ FLOOKUP G v = SOME site ==>
  (?aid. FLOOKUP om v = SOME (OriginLocal aid,site) /\
    FLOOKUP s.vs_allocas aid = SOME site /\
    Allocation aid IN bp_bases
      (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) v) \/
  (?p k aid. FLOOKUP om v = SOME (OriginParameter p,site) /\
    v IN pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn) /\
    k < LENGTH stk /\ FLOOKUP (EL k stk).cf_state.vs_allocas aid = SOME site)
Proof
  strip_tac >> drule joint_origin_history_erasure >> strip_tac >>
  drule_all origin_frame_current_lookup >> strip_tac >> Cases_on `tag`
  >- (disj1_tac >> metis_tac[origin_frame_current_cache,
        origin_frame_current_production_coverage])
  >- (disj2_tac >> metis_tac[origin_frame_current_incoming,
        joint_incoming_allocation_owner]) >>
  metis_tac[origin_frame_current_not_dynamic]
QED

Theorem shape_context_inst_wf[local]:
  o1_ctx_shape ctx ==>
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions
Proof
  simp[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def,
       fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem joint_read_production_origin:
  joint_trace vs0 ctx q0 es qs q /\ o1_ctx_shape ctx /\
  ptr_discipline lo ctx vs0 /\ EVERY ssa_form ctx.ctx_functions /\
  EVERY all_reachable ctx.ctx_functions /\ ~ctx_has_dalloca ctx /\
  j <= LENGTH es /\
  EL j (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  byte IN joint_reads (EL j (q0::qs)) /\ lo <= byte /\
  ~in_revert_forward fn s ==>
  ?P ops v b sz.
    EVERY (fn_ptr_ok P) ctx.ctx_functions /\
    mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
    FLOOKUP G v = SOME (b,sz) /\ b <= byte /\ byte < b + sz /\
    ((?aid. FLOOKUP om v = SOME (OriginLocal aid,(b,sz)) /\
      FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      Allocation aid IN bp_bases
        (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) v) \/
     (?p k aid. FLOOKUP om v = SOME (OriginParameter p,(b,sz)) /\
      v IN pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn) /\
      k < LENGTH stk /\ FLOOKUP (EL k stk).cf_state.vs_allocas aid = SOME (b,sz)))
Proof
  strip_tac >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_trace_def, joint_chain_length] >>
  `joint_config_reachable vs0 ctx (EL j (q0::qs))` by
    (drule joint_trace_prefix_reachable >> strip_tac >>
     Cases_on `j` >> gvs[EVERY_EL] >>
     rename1 `SUC k <= LENGTH qs` >> `k < LENGTH qs` by decide_tac >> metis_tac[]) >>
  `joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h` by
    gvs[joint_config_reachable_def] >>
  drule joint_origin_history_erasure >> strip_tac >>
  drule origin_frame_erasure >> strip_tac >>
  `MEM fn ctx.ctx_functions` by metis_tac[frame_allocation_ownership] >>
  `EVERY wf_function ctx.ctx_functions` by
    gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions` by
    metis_tac[shape_context_inst_wf] >>
  `wf_function fn /\ all_reachable fn /\ ssa_form fn` by metis_tac[EVERY_MEM] >>
  fs[ptr_discipline_def] >>
  `EVERY (fn_ptr_ok P) ctx.ctx_functions` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `access_ok lo G fn inst s` by metis_tac[] >>
  `byte IN range_bytes (source_memory_read_ranges inst s)` by gvs[joint_reads_def] >>
  drule_all access_ok_read_site >> strip_tac >>
  qexistsl_tac [`P`,`ops`,`v`,`b`,`sz`] >> simp[] >>
  irule joint_current_production_origin >> metis_tac[]
QED
