Theory concretizeAnalysisRuntimeItems
Ancestors concretizeAnalysisOpenCallSummary concretizeAnalysisStageSizes
  concretizeAnalysisOwnership concretizeAnalysisCollection frameHistoryCfg
  concretizeAnalysisSizes staticLayoutAllocatorProofs concretizeMemLocDefs
  frameDemandOwnership frameOpenCall frameActivationCache frameJointTransition frameJointTrace frameOriginHistory
  frameOriginReachable frameExecutionHistory frameAllocationSizes frameResolvedTrace
  contextCodegenRel o1PassContract venomWf venomInst venomExecProps removeUnusedSsaProofs
  finite_map list pred_set arithmetic

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

Theorem activation_cache_source_owner:
  joint_config_reachable vs0 C q /\ o1_ctx_shape C /\
  activation_cache q d owner aid (b,sz) ==>
  MEM owner C.ctx_functions
Proof
  strip_tac >>
  `EVERY wf_function C.ctx_functions` by
    (gvs[EVERY_MEM, o1_ctx_shape_def] >> metis_tac[o1_fn_shape_def]) >>
  Cases_on `q` >> gvs[joint_config_reachable_def] >>
  drule joint_origin_history_erasure >> strip_tac >>
  drule origin_frame_erasure >> strip_tac >>
  drule frame_reachable_has_history >> strip_tac >>
  drule_all frame_history_cfg_invariant >> strip_tac >>
  qpat_x_assum `activation_cache _ _ _ _ _` mp_tac >>
  simp[activation_cache_def] >> strip_tac >> gvs[] >>
  gvs[LIST_REL_EL_EQN] >>
  `LENGTH l - SUC d < LENGTH l` by decide_tac >> metis_tac[]
QED

Theorem allocation_birth_source_instruction:
  joint_transition C q ev q' /\ allocation_birth C q ev d owner aid site ==>
  ?inst. MEM inst (fn_insts owner) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id = aid
Proof
  Cases_on `q` >>
  simp[allocation_birth_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[Once joint_transition_cases] >> strip_tac >> gvs[] >>
  rename1 `inst.inst_opcode = ALLOCA` >>
  rename1 `active_inst owner inst pre` >>
  `MEM inst (fn_insts owner)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_flat,
         MEM_FLAT, MEM_MAP] >> metis_tac[EL_MEM]) >>
  metis_tac[]
QED

Theorem runtime_chain_endpoint[local]:
  !es q0 qs q. joint_chain C q0 es qs q ==>
    EL (LENGTH es) (q0::qs) = q
Proof
  Induct >> Cases_on `qs` >> simp[joint_chain_def] >> metis_tac[]
QED

Theorem activation_cache_source_instruction:
  joint_config_reachable vs0 C q /\ o1_run_state_ok vs0 /\
  activation_cache q d owner aid site ==>
  ?inst. MEM inst (fn_insts owner) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id = aid
Proof
  strip_tac >>
  `vs0.vs_allocas = FEMPTY` by gvs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def] >>
  `?q0 es qs. joint_trace vs0 C q0 es qs q` by
    metis_tac[joint_reachable_iff_trace] >>
  `LENGTH es = LENGTH qs` by
    metis_tac[joint_trace_def, joint_chain_length] >>
  `EL (LENGTH es) (q0::qs) = q` by
    metis_tac[joint_trace_def, runtime_chain_endpoint] >>
  `?t. t < LENGTH es /\
    allocation_birth C (EL t (q0::qs)) (EL t es) d owner aid site` by
    metis_tac[joint_cache_birth, LESS_EQ_REFL] >>
  drule_all joint_trace_edge_at >> strip_tac >>
  metis_tac[allocation_birth_source_instruction]
QED

Theorem activation_cache_source_size:
  joint_config_reachable vs0 C q /\ o1_run_state_ok vs0 /\
  EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) C.ctx_functions /\
  activation_cache q d owner aid (b,sz) ==>
  FLOOKUP (source_alloca_sizes owner) aid = SOME sz
Proof
  Cases_on `q` >> simp[joint_config_reachable_def] >> strip_tac >>
  drule joint_origin_history_erasure >> strip_tac >>
  drule origin_frame_erasure >> strip_tac >>
  qpat_x_assum `activation_cache _ _ _ _ _` mp_tac >>
  simp[activation_cache_def] >> strip_tac >> gvs[]
  >- metis_tac[o1_frame_source_sizes_lookup] >>
  `LENGTH l - SUC d < LENGTH l` by decide_tac >>
  `MEM (EL (LENGTH l - SUC d) l) l` by metis_tac[EL_MEM] >>
  drule_all o1_frame_source_sizes_saved >>
  metis_tac[cache_sizes_ok_lookup]
QED

Theorem activation_cache_static_item:
  joint_config_reachable vs0 C q /\ o1_run_state_ok vs0 /\
  EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) C.ctx_functions /\
  activation_cache q d owner aid (b,sz) /\ b <= byte /\ byte < b + sz /\
  static_alloca_items owner = SOME items ==>
  MEM (Allocation aid,sz) items
Proof
  strip_tac >>
  `0 < sz` by decide_tac >>
  drule_all activation_cache_source_size >> strip_tac >>
  metis_tac[source_alloca_sizes_positive_item]
QED

Theorem activation_cache_source_allocation:
  joint_config_reachable vs0 C q /\ o1_run_state_ok vs0 /\
  o1_ctx_shape C /\ ctx_inst_ids_distinct C /\
  activation_cache q d owner aid (b,sz) ==>
  MEM owner C.ctx_functions /\
  ?inst n. MEM inst (fn_insts owner) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = aid /\ inst.inst_operands = [Lit n] /\ w2n n = sz
Proof
  strip_tac >>
  `MEM owner C.ctx_functions` by metis_tac[activation_cache_source_owner] >>
  simp[] >>
  `EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) C.ctx_functions` by
    (gvs[EVERY_MEM, o1_ctx_shape_def] >> rpt strip_tac >>
     metis_tac[o1_fn_shape_def, source_member_ids_distinct]) >>
  `?inst. MEM inst (fn_insts owner) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id = aid` by
    metis_tac[activation_cache_source_instruction] >>
  `fn_inst_wf owner /\ fn_inst_ids_distinct owner` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `?n. inst.inst_operands = [Lit n]` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_flat,
         EVERY_MEM, MEM_FLAT, MEM_MAP] >>
     `inst_wf inst` by metis_tac[] >> gvs[inst_wf_def]) >>
  `FLOOKUP (source_alloca_sizes owner) aid = SOME sz` by
    metis_tac[activation_cache_source_size] >>
  drule_all source_alloca_sizes_literal >> strip_tac >>
  qexistsl_tac [`inst`, `n`] >> gvs[]
QED

Theorem activation_cache_source_static_item:
  joint_config_reachable vs0 C q /\ o1_run_state_ok vs0 /\
  o1_ctx_shape C /\ ctx_inst_ids_distinct C /\
  activation_cache q d owner aid (b,sz) ==>
  ?items. static_alloca_items owner = SOME items /\
    MEM (Allocation aid,sz) items
Proof
  strip_tac >>
  drule_all activation_cache_source_allocation >> strip_tac >>
  drule_all source_static_alloca_items_total >> strip_tac >>
  drule_all static_alloca_items_ALLOCA_exact >> strip_tac >> gvs[] >>
  drule static_alloca_items_MEM >> strip_tac >> metis_tac[]

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

Theorem joint_open_call_activation_summary:
  joint_trace vs0 C q0 es qs q /\ o1_ctx_shape C /\ c < n /\ n <= LENGTH es /\
  EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 caller invoke s0 oms0 om0 hs0 h0 /\
  joint_transition C (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
  (!k. c < k /\ k <= n ==> LENGTH stk0 < activation_depth (EL k (q0::qs))) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  o1_run_state_ok vs0 /\ static_alloca_items owner = SOME items /\
  activation_cache (EL n (q0::qs)) d owner aid (b,sz) /\ LENGTH stk0 < d /\
  b <= byte /\ byte < b + sz /\ o1_walk_view rpolicy 2 C' caller observed ==>
  ?root name ops g p.
    invoke.inst_opcode = INVOKE /\ invoke.inst_operands = Label name :: ops /\
    lookup_function name C.ctx_functions = SOME root /\
    source_call C caller root /\ RTC (source_call C) root owner /\
    lookup_function root.fn_name observed.cu_context.ctx_functions = SOME g /\
    MEM (Allocation aid,p,sz) g.fn_mems_used
Proof
  strip_tac >>
  `?t. c < t /\ t <= n /\ activation_depth (EL t (q0::qs)) = d /\
    activation_cache (EL t (q0::qs)) d owner aid (b,sz) /\
    (!k. t < k /\ k <= n ==> d < activation_depth (EL k (q0::qs)))` by
    (irule joint_activation_cache_exposure >> simp[activation_depth_def] >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >> simp[]) >>
  Cases_on `EL t (q0::qs)` >>
  gvs[activation_depth_def, activation_cache_current] >>
  irule joint_open_call_runtime_summary >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `EL t _ = _`)) >>
  goal_assum (drule_at (Pat `EL _ _ = JointConfig _ _ _ _ caller invoke _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = _`)) >>
  simp[] >> metis_tac[LESS_EQ_TRANS]
QED


Theorem resolved_current_source_allocation:
  joint_config_reachable vs0 C
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  o1_run_state_ok vs0 /\ o1_ctx_shape C /\ ctx_inst_ids_distinct C /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  FLOOKUP rv v = SOME ((token,aid),(b,sz)) ==>
  ?k owner ai n. k < LENGTH (birth::ids) /\ EL k (birth::ids) = token /\
    activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
      (LENGTH stk - k) owner aid (b,sz) /\
    MEM owner C.ctx_functions /\ MEM ai (fn_insts owner) /\
    ai.inst_opcode = ALLOCA /\ ai.inst_id = aid /\
    ai.inst_operands = [Lit n] /\ w2n n = sz
Proof
  strip_tac >> drule_all resolved_current_owner >> strip_tac >>
  drule_all activation_cache_source_allocation >> strip_tac >>
  gvs[] >> goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

Theorem resolved_saved_source_allocation:
  joint_config_reachable vs0 C
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  o1_run_state_ok vs0 /\ o1_ctx_shape C /\ ctx_inst_ids_distinct C /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) (ann::anns) /\ k < LENGTH stk /\
  FLOOKUP (SND (EL k anns)) v = SOME ((token,aid),(b,sz)) ==>
  ?j owner ai n. j < LENGTH (birth::ids) /\ EL j (birth::ids) = token /\
    activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
      (LENGTH stk - j) owner aid (b,sz) /\
    MEM owner C.ctx_functions /\ MEM ai (fn_insts owner) /\
    ai.inst_opcode = ALLOCA /\ ai.inst_id = aid /\
    ai.inst_operands = [Lit n] /\ w2n n = sz
Proof
  strip_tac >> drule_all resolved_saved_owner >> strip_tac >>
  drule_all activation_cache_source_allocation >> strip_tac >>
  gvs[] >> goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

Theorem joint_trace_prefix_source_allocation:
  joint_trace vs0 C q0 es qs q /\ k <= LENGTH es /\
  o1_run_state_ok vs0 /\ o1_ctx_shape C /\ ctx_inst_ids_distinct C /\
  activation_cache (EL k (q0::qs)) d owner aid (b,sz) ==>
  MEM owner C.ctx_functions /\
  ?ai n. MEM ai (fn_insts owner) /\ ai.inst_opcode = ALLOCA /\
    ai.inst_id = aid /\ ai.inst_operands = [Lit n] /\ w2n n = sz
Proof
  strip_tac >>
  `LENGTH qs = LENGTH es` by metis_tac[joint_trace_def, joint_chain_length] >>
  drule joint_trace_prefix_reachable >> rewrite_tac[EVERY_EL] >>
  disch_then (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
  drule_all activation_cache_source_allocation >> simp[]
QED
