Theory concretizeAnalysisRuntimeItems
Ancestors concretizeAnalysisOpenCallSummary concretizeAnalysisStageSizes
  concretizeAnalysisOwnership concretizeAnalysisCollection frameHistoryCfg
  concretizeAnalysisSizes staticLayoutAllocatorProofs concretizeMemLocDefs
  frameActivationCache frameJointTransition frameJointTrace frameOriginHistory
  frameOriginReachable frameExecutionHistory frameAllocationSizes
  o1PassContract venomWf venomInst venomExecProps removeUnusedSsaProofs
  finite_map list pred_set

Theorem source_alloca_sizes_positive_item:
  static_alloca_items fn = SOME items /\
  FLOOKUP (source_alloca_sizes fn) aid = SOME sz /\ 0 < sz ==>
  MEM (Allocation aid,sz) items
Proof
  strip_tac >>
  qpat_x_assum `FLOOKUP _ _ = _` mp_tac >>
  simp[source_alloca_sizes_def, FLOOKUP_FUN_FMAP] >>
  strip_tac >>
  qpat_x_assum `get_alloca_size _ _ = _` mp_tac >>
  simp[get_alloca_size_def] >>
  Cases_on `FIND (\inst. is_alloca_op inst.inst_opcode /\ inst.inst_id = i.inst_id)
    (FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks))` >> simp[] >>
  strip_tac >> gvs[] >>
  `is_alloca_op x.inst_opcode /\ x.inst_id = i.inst_id` by
    (drule FIND_P >> simp[]) >>
  `x.inst_opcode = ALLOCA` by
    (Cases_on `x.inst_opcode` >> gvs[is_alloca_op_def]) >>
  `MEM x (fn_insts fn)` by
    (drule FIND_MEM >> simp[fn_insts_def, fn_insts_blocks_flat]) >>
  drule_all static_alloca_items_ALLOCA_exact >> strip_tac >>
  gvs[] >> drule static_alloca_items_MEM >>
  strip_tac >> metis_tac[]
QED

Theorem activation_cache_static_item:
  joint_config_reachable vs0 C q /\ o1_run_state_ok vs0 /\
  EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) C.ctx_functions /\
  activation_cache q d owner aid (b,sz) /\ b <= byte /\ byte < b + sz /\
  static_alloca_items owner = SOME items ==>
  MEM (Allocation aid,sz) items
Proof
  Cases_on `q` >> simp[joint_config_reachable_def] >> strip_tac >>
  drule joint_origin_history_erasure >> strip_tac >> drule origin_frame_erasure >> strip_tac >>
  `0 < sz` by decide_tac >>
  irule source_alloca_sizes_positive_item >> simp[] >>
  goal_assum (drule_at (Pat `static_alloca_items _ = _`)) >> simp[] >>
  qpat_x_assum `activation_cache _ _ _ _ _` mp_tac >>
  simp[activation_cache_def] >> strip_tac >> gvs[]
  >- metis_tac[o1_frame_source_sizes_lookup] >>
  `LENGTH l - SUC d < LENGTH l` by decide_tac >>
  `MEM (EL (LENGTH l - SUC d) l) l` by metis_tac[EL_MEM] >>
  drule_all o1_frame_source_sizes_saved >>
  metis_tac[cache_sizes_ok_lookup]
QED

Theorem activation_cache_source_static_item:
  joint_config_reachable vs0 C q /\ o1_run_state_ok vs0 /\
  o1_ctx_shape C /\ ctx_inst_ids_distinct C /\
  activation_cache q d owner aid (b,sz) /\ b <= byte /\ byte < b + sz ==>
  ?items. static_alloca_items owner = SOME items /\
    MEM (Allocation aid,sz) items
Proof
  strip_tac >>
  `EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) C.ctx_functions` by
    (gvs[EVERY_MEM, o1_ctx_shape_def] >> rpt strip_tac >>
     metis_tac[o1_fn_shape_def, source_member_ids_distinct]) >>
  `EVERY wf_function C.ctx_functions` by
    (gvs[EVERY_MEM, o1_ctx_shape_def] >> metis_tac[o1_fn_shape_def]) >>
  `MEM owner C.ctx_functions` by
    (Cases_on `q` >> gvs[joint_config_reachable_def] >>
     drule joint_origin_history_erasure >> strip_tac >>
     drule origin_frame_erasure >> strip_tac >>
     drule frame_reachable_has_history >> strip_tac >>
     drule_all frame_history_cfg_invariant >> strip_tac >>
     qpat_x_assum `activation_cache _ _ _ _ _` mp_tac >>
     simp[activation_cache_def] >> strip_tac >> gvs[] >>
     gvs[LIST_REL_EL_EQN] >>
     `LENGTH l - SUC d < LENGTH l` by decide_tac >> metis_tac[]) >>
  drule_all source_static_alloca_items_total >> strip_tac >>
  goal_assum (drule_at (Pat `static_alloca_items _ = _`)) >>
  irule activation_cache_static_item >>
  goal_assum (drule_at (Pat `joint_config_reachable _ _ _`)) >>
  goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

Theorem joint_open_call_runtime_summary:
  joint_trace vs0 C q0 es qs q /\ o1_ctx_shape C /\ c < j /\ j <= LENGTH es /\
  EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 caller invoke s0 oms0 om0 hs0 h0 /\
  joint_transition C (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
  EL j (q0::qs) = JointConfig stk PG G tn owner inst s oms om hs h /\
  (!k. c < k /\ k <= j ==> LENGTH stk0 < activation_depth (EL k (q0::qs))) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  o1_run_state_ok vs0 /\ static_alloca_items owner = SOME items /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ b <= byte /\ byte < b + sz /\
  o1_walk_view rpolicy 2 C' caller observed ==>
  ?root name ops g p.
    invoke.inst_opcode = INVOKE /\ invoke.inst_operands = Label name :: ops /\
    lookup_function name C.ctx_functions = SOME root /\
    source_call C caller root /\ RTC (source_call C) root owner /\
    lookup_function root.fn_name observed.cu_context.ctx_functions = SOME g /\
    MEM (Allocation aid,p,sz) g.fn_mems_used
Proof
  strip_tac >>
  `EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) C.ctx_functions` by
    (gvs[EVERY_MEM, o1_ctx_shape_def] >> rpt strip_tac >>
     metis_tac[o1_fn_shape_def, source_member_ids_distinct]) >>
  `SUC (j-1) = j /\ j-1 < LENGTH es` by decide_tac >>
  `joint_config_reachable vs0 C (EL j (q0::qs))` by
    (drule joint_trace_edge_at >> disch_then (qspec_then `j-1` mp_tac) >>
     pure_asm_rewrite_tac[] >> metis_tac[]) >>
  `activation_cache (EL j (q0::qs)) (LENGTH stk) owner aid (b,sz)` by
    simp[activation_cache_current] >>
  `MEM (Allocation aid,sz) items` by
    (irule activation_cache_static_item >>
     goal_assum (drule_at (Pat `joint_config_reachable _ _ _`)) >>
     goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `static_alloca_items _ = _`)) >>
     simp[] >> metis_tac[]) >>
  drule_all joint_open_call_observed_summary >> simp[]
QED
