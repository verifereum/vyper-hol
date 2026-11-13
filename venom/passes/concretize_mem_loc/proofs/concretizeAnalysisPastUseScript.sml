Theory concretizeAnalysisPastUse
Ancestors
  concretizeAnalysisUsedDemand concretizeAnalysisIncomingDemand
  concretizeAnalysisTemporalDemand frameOriginHistory ptrDiscipline
  concretizePtrIncomingOrigins frameOriginCacheReach frameWriteOwnership
  frameJointTaint frameDemandOwnership frameDemandLastWrite frameOriginReachable frameJointTrace frameJointTransition
  frameActivationSeparation frameActivationCache venomInst o1PassContract cfgWf venomWf finite_map list arithmetic

Theorem joint_write_past_owner_generator:
  joint_trace vs0 C q0 es qs q /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  vs0.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  l <= m /\ m < LENGTH es /\ activation_depth (EL l (q0::qs)) = d /\
  (!k. l <= k /\ k <= m ==>
    d <= activation_depth (EL k (q0::qs)) /\
    activation_cache (EL k (q0::qs)) d owner aid (b,sz)) /\
  EL m (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  ~in_revert_forward fn s /\ lo <= byte /\ b <= byte /\ byte < b + sz /\
  byte IN joint_writes (EL m (q0::qs)) (EL m es) ==>
  ?c stk0 PG0 G0 tn0 instc sc oms0 om0 hs0 h0.
    l <= c /\ c <= m /\ LENGTH stk0 = d /\
    EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 owner instc sc oms0 om0 hs0 h0 /\
    active_inst owner instc sc /\
    ml_used_gen (Allocation aid)
      (bp_analyze_fuel (concretize_memloc_fuel owner) (cfg_analyze owner) owner)
      mems instc
Proof
  strip_tac >>
  `joint_config_reachable vs0 C
    (JointConfig stk PG G tn fn inst s oms om hs h)` by
    (drule trace_config_at >> disch_then (qspec_then `m` mp_tac) >> simp[]) >>
  `joint_origin_history vs0 C stk PG G tn fn inst s oms om hs h` by
    gvs[joint_config_reachable_def] >>
  `origin_frame_reachable vs0 C stk PG G tn fn inst s oms om` by
    metis_tac[joint_origin_history_erasure] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    metis_tac[origin_frame_erasure] >>
  `access_ok lo G fn inst s` by metis_tac[ptr_discipline_def] >>
  `activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
    d owner aid (b,sz)` by metis_tac[LESS_EQ_REFL] >>
  `?q'. joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h)
    (EL m es) q'` by
    (drule joint_trace_edge_at >> disch_then (qspec_then `m` mp_tac) >> simp[] >>
     metis_tac[]) >>
  `byte IN joint_writes (JointConfig stk PG G tn fn inst s oms om hs h) (EL m es)`
    by metis_tac[] >>
  drule_all joint_write_owner_identity >> strip_tac >>
  drule_all origin_frame_current_lookup >> strip_tac >>
  Cases_on `tag`
  >- suspend "local"
  >- suspend "incoming"
  >> suspend "dynamic"
QED

Resume joint_write_past_owner_generator[local]:
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
  `active_inst fn inst s` by
    (qpat_x_assum `origin_frame_reachable _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once origin_frame_reachable_cases] >> metis_tac[]) >>
  `ml_used_gen (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) mems inst` by
    (irule joint_local_write_used_generator >>
     goal_assum (drule_at (Pat `joint_config_reachable _ _ _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP om _ = _`)) >>
     goal_assum (drule_at (Pat `mem_write_ops _ = _`)) >>
     goal_assum (drule_at (Pat `ptr_discipline _ _ _`)) >> simp[]) >>
  qexists_tac `m` >>
  goal_assum (drule_at (Pat `EL _ _ = JointConfig _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED

Resume joint_write_past_owner_generator[incoming]:
  drule_all joint_incoming_used_generator >>
  disch_then (qspec_then `mems` strip_assume_tac) >>
  `activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
    (LENGTH stk - SUC k) (EL k stk).cf_fn aid' (b,sz)` by
    simp[activation_cache_saved] >>
  `d = LENGTH stk - SUC k /\ owner = (EL k stk).cf_fn /\ aid = aid' /\
    b = b /\ sz = sz` by
    (irule joint_activation_cache_byte_unique >>
     (conj_tac >- (qexists_tac `byte` >> simp[])) >>
     goal_assum (drule_at (Pat `joint_config_reachable _ _ _`)) >> simp[]) >>
  `m <= LENGTH es` by decide_tac >>
  `!t. l <= t /\ t <= m ==> d <= activation_depth (EL t (q0::qs))`
    by metis_tac[] >>
  `owner' = owner` by metis_tac[] >>
  `aid' = aid` by simp[] >>
  drule_all joint_saved_used_generator_occurrence >> strip_tac >>
  qpat_x_assum `owner' = owner` SUBST_ALL_TAC >>
  qpat_x_assum `aid' = aid` SUBST_ALL_TAC >> qexists_tac `c` >>
  goal_assum (drule_at (Pat `EL _ _ = JointConfig _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> decide_tac
QED

Resume joint_write_past_owner_generator[dynamic]:
  qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
  simp[ptr_discipline_def] >> strip_tac >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[]) >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[origin_frame_current_not_dynamic]
QED

Finalise joint_write_past_owner_generator

Theorem allocation_birth_next_depth[local]:
  joint_transition C p ev q /\ allocation_birth C p ev d owner aid site ==>
  activation_depth q = d
Proof
  Cases_on `p` >> simp[allocation_birth_def] >> rpt strip_tac >>
  gvs[joint_transition_ordinary, activation_depth_def]
QED

Theorem joint_untainted_cache_past_owner_generator:
  joint_trace vs0 C q0 es qs q /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  vs0.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ j <= LENGTH es /\
  activation_cache (EL j (q0::qs)) d owner aid (b,sz) /\
  b <= byte /\ byte < b + sz /\ lo <= byte /\
  byte NOTIN joint_mem_taint (EL j (q0::qs)) /\
  (!k stk PG G tn fn inst s oms om hs h.
    k < j /\ EL k (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h ==>
    ~in_revert_forward fn s) ==>
  ?t c stk0 PG0 G0 tn0 instc sc oms0 om0 hs0 h0.
    t < c /\ c < j /\ LENGTH stk0 = d /\
    allocation_birth C (EL t (q0::qs)) (EL t es) d owner aid (b,sz) /\
    EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 owner instc sc oms0 om0 hs0 h0 /\
    active_inst owner instc sc /\
    ml_used_gen (Allocation aid)
      (bp_analyze_fuel (concretize_memloc_fuel owner) (cfg_analyze owner) owner)
      mems instc /\
    (!k. t < k /\ k <= j ==> d <= activation_depth (EL k (q0::qs)) /\
      activation_cache (EL k (q0::qs)) d owner aid (b,sz))
Proof
  strip_tac >> drule_all joint_untainted_cache_last_write >> strip_tac >>
  `m < LENGTH es /\ t < LENGTH es /\ SUC t <= m` by decide_tac >>
  `joint_transition C (EL t (q0::qs)) (EL t es) (EL (SUC t) (q0::qs))` by
    metis_tac[joint_trace_edge_at] >>
  `activation_depth (EL (SUC t) (q0::qs)) = d` by
    metis_tac[allocation_birth_next_depth] >>
  Cases_on `EL m (q0::qs)` >>
  rename1 `EL m (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h` >>
  `~in_revert_forward fn s` by metis_tac[] >>
  `!k. SUC t <= k /\ k <= m ==> d <= activation_depth (EL k (q0::qs)) /\
    activation_cache (EL k (q0::qs)) d owner aid (b,sz)` by
    (rpt gen_tac >> strip_tac >>
     `t < k /\ k <= j` by decide_tac >> metis_tac[]) >>
  `byte IN joint_writes (EL m (q0::qs)) (EL m es)` by metis_tac[] >>
  drule_all joint_write_past_owner_generator >>
  disch_then (qspec_then `mems` strip_assume_tac) >>
  qexistsl_tac [`t`,`c`] >>
  goal_assum (drule_at (Pat `EL _ _ = JointConfig _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> decide_tac
QED

Theorem joint_untainted_cache_used:
  joint_trace vs0 C q0 es qs q /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  vs0.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ n <= LENGTH es /\
  activation_cache (EL n (q0::qs)) d owner aid (b,sz) /\
  activation_location (EL n (q0::qs)) d owner p /\
  b <= byte /\ byte < b + sz /\ lo <= byte /\
  byte NOTIN joint_mem_taint (EL n (q0::qs)) /\
  (!k stk PG G tn fn inst s oms om hs h.
    k < n /\ EL k (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h ==>
    ~in_revert_forward fn s) /\
  wf_function owner /\ all_reachable owner /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  bp = bp_analyze_fuel (concretize_memloc_fuel owner) (cfg_analyze owner) owner /\
  ml_iterate_fuel (concretize_memloc_fuel owner) bp mems sizes pallocas
    (cfg_analyze owner) owner FEMPTY FEMPTY = (la,us) ==>
  MEM (Allocation aid) (ml_lookup us p)
Proof
  strip_tac >> drule_all joint_untainted_cache_past_owner_generator >>
  disch_then (qspec_then `mems` strip_assume_tac) >>
  `c <= n` by decide_tac >>
  `!k. c <= k /\ k <= n ==> d <= activation_depth (EL k (q0::qs))` by
    (rpt strip_tac >> `t < k /\ k <= n` by decide_tac >> metis_tac[]) >>
  irule joint_activation_used_past_generator >>
  goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `EL _ _ = JointConfig _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >> simp[] >>
  metis_tac[]
QED

Theorem joint_untainted_demand_owner_used:
  joint_trace vs0 C q0 es qs q /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  vs0.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ n <= j /\ j <= LENGTH es /\
  activation_cache (EL n (q0::qs)) d owner aid (b,sz) /\
  activation_location (EL n (q0::qs)) d owner p /\
  b <= byte /\ byte < b + sz /\ lo <= byte /\
  byte NOTIN joint_mem_taint (EL j (q0::qs)) /\
  (!k. n <= k /\ k < j ==>
    byte NOTIN joint_writes (EL k (q0::qs)) (EL k es)) /\
  (!k stk PG G tn fn inst s oms om hs h.
    k < n /\ EL k (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h ==>
    ~in_revert_forward fn s) /\
  wf_function owner /\ all_reachable owner /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  bp = bp_analyze_fuel (concretize_memloc_fuel owner) (cfg_analyze owner) owner /\
  ml_iterate_fuel (concretize_memloc_fuel owner) bp mems sizes pallocas
    (cfg_analyze owner) owner FEMPTY FEMPTY = (la,us) ==>
  MEM (Allocation aid) (ml_lookup us p)
Proof
  strip_tac >>
  `byte NOTIN joint_mem_taint (EL n (q0::qs))` by
    metis_tac[joint_trace_mem_taint] >>
  `n <= LENGTH es` by decide_tac >>
  irule joint_untainted_cache_used >>
  goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ptr_discipline _ _ _`)) >>
  goal_assum (drule_at (Pat `byte NOTIN joint_mem_taint _`)) >> simp[] >>
  metis_tac[]
QED
