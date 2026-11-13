Theory concretizeAnalysisImportedDemand
Ancestors concretizeAnalysisRuntimeItems concretizeAnalysisLivenessPaths
  concretizeAnalysisCollection concretizePtrOrdering frameJointTransition
  concretizeMemLocDefs o1PassContract venomExecProps venomWf venomInst
  enumeral finite_map list pred_set pair contextCodegenRel
  frameJointTrace frameActivationCache frameOpenCall concretizeAnalysisOwnership concretizeAnalysisCallProjection

(* Metadata is consumed as an ordered set, but ordering loses no keys. *)
Theorem active_invoke_context_liveset:
  wf_function fn /\ all_reachable fn /\ active_inst fn inst s /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: ops /\
  MEM (a,p,sz) (callee_mems_used ctx nm) ==>
  ?addrs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
    ctx fn bpr (cfg_analyze fn)) a = SOME addrs /\
    MEM (s.vs_current_bb,s.vs_inst_idx) addrs
Proof
  strip_tac >>
  `!xs. set (incr_ssort alloc_to xs) = set xs` by
    metis_tac[set_OWL_thm, OWL] >>
  `MEM a (incr_ssort alloc_to (MAP FST (callee_mems_used ctx nm)))` by
    (gvs[EXTENSION, MEM_MAP] >> metis_tac[pairTheory.FST]) >>
  simp[context_mem_livesets_def, mem_liveness_analyze_fuel_def] >>
  pairarg_tac >> gvs[active_inst_def] >>
  `MEM a (ml_lookup liveat (bb.bb_label,s.vs_inst_idx)) /\
   MEM a (ml_lookup used (bb.bb_label,s.vs_inst_idx))` by
    (irule ml_production_invoke_generators >> simp[] >>
     goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >>
     simp[ptr_incr_ssort_ordered, OL] >> metis_tac[]) >>
  qpat_x_assum `bb.bb_label = _` (fn th => rewrite_tac[GSYM th]) >>
  irule ml_production_marked_membership >> simp[] >>
  goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[ptr_incr_ssort_ordered, OL] >> metis_tac[]
QED

Theorem concretize_open_call_runtime_liveset:
  joint_trace vs0 C q0 es qs q /\ o1_ctx_shape C /\ c < j /\ j <= LENGTH es /\
  EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 caller invoke s0 oms0 om0 hs0 h0 /\
  joint_transition C (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
  EL j (q0::qs) = JointConfig stk PG G tn owner inst s oms om hs h /\
  (!k. c < k /\ k <= j ==> LENGTH stk0 < activation_depth (EL k (q0::qs))) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  o1_run_state_ok vs0 /\ all_reachable caller /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ b <= byte /\ byte < b + sz /\
  o1_walk_view rpolicy 2 C' caller observed ==>
  ?addrs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel caller)
    observed.cu_context caller
    (bp_analyze_fuel (concretize_memloc_fuel caller) (cfg_analyze caller) caller)
    (cfg_analyze caller)) (Allocation aid) = SOME addrs /\
    MEM (s0.vs_current_bb,s0.vs_inst_idx) addrs
Proof
  strip_tac >>
  `SUC (j-1) = j /\ j-1 < LENGTH es` by decide_tac >>
  `joint_config_reachable vs0 C (EL j (q0::qs))` by
    (drule joint_trace_edge_at >> disch_then (qspec_then `j-1` mp_tac) >>
     pure_asm_rewrite_tac[] >> metis_tac[]) >>
  `activation_cache (EL j (q0::qs)) (LENGTH stk) owner aid (b,sz)` by
    simp[activation_cache_current] >>
  `?items. static_alloca_items owner = SOME items` by
    (drule_all activation_cache_source_static_item >> metis_tac[]) >>
  drule_all joint_open_call_runtime_summary >> strip_tac >>
  `root.fn_name = name` by
    (qpat_x_assum `lookup_function name _ = _` mp_tac >>
     simp[lookup_function_def] >> strip_tac >> drule FIND_P >> simp[]) >>
  `MEM caller C.ctx_functions` by gvs[source_call_def] >>
  `active_inst caller invoke s0` by
    (qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_call_iff] >> metis_tac[]) >>
  `wf_function caller` by
    (gvs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  irule active_invoke_context_liveset >> simp[] >>
  goal_assum (drule_at (Pat `active_inst _ _ _`)) >> simp[] >>
  gvs[callee_mems_used_def] >> metis_tac[]
QED

Theorem concretize_open_call_runtime_liveset_context:
  joint_trace vs0 C q0 es qs q /\ o1_ctx_shape C /\ c < j /\ j <= LENGTH es /\
  EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 caller invoke s0 oms0 om0 hs0 h0 /\
  joint_transition C (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
  EL j (q0::qs) = JointConfig stk PG G tn owner inst s oms om hs h /\
  (!k. c < k /\ k <= j ==> LENGTH stk0 < activation_depth (EL k (q0::qs))) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  o1_run_state_ok vs0 /\ EVERY all_reachable C.ctx_functions /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ b <= byte /\ byte < b + sz /\
  o1_walk_view rpolicy 2 C' caller observed ==>
  ?addrs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel caller)
    observed.cu_context caller
    (bp_analyze_fuel (concretize_memloc_fuel caller) (cfg_analyze caller) caller)
    (cfg_analyze caller)) (Allocation aid) = SOME addrs /\
    MEM (s0.vs_current_bb,s0.vs_inst_idx) addrs
Proof
  strip_tac >>
  `all_reachable caller` by
    (drule_all joint_open_call_path_at >> strip_tac >>
     gvs[source_call_def, EVERY_MEM]) >>
  fs[] >> irule concretize_open_call_runtime_liveset >> simp[] >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `o1_walk_view _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `callee_first _ _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = _`)) >>
  goal_assum (drule_at (Pat `joint_transition _ _ _ _`)) >>
  goal_assum (drule_at (Pat `EL _ _ = JointConfig _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> qexists_tac `byte` >> simp[]
QED

Theorem concretize_open_call_activation_liveset_context:
  joint_trace vs0 C q0 es qs q /\ o1_ctx_shape C /\ c < n /\ n <= LENGTH es /\
  EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 caller invoke s0 oms0 om0 hs0 h0 /\
  joint_transition C (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
  (!k. c < k /\ k <= n ==> LENGTH stk0 < activation_depth (EL k (q0::qs))) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  o1_run_state_ok vs0 /\ EVERY all_reachable C.ctx_functions /\
  activation_cache (EL n (q0::qs)) d owner aid (b,sz) /\ LENGTH stk0 < d /\
  b <= byte /\ byte < b + sz /\ o1_walk_view rpolicy 2 C' caller observed ==>
  ?addrs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel caller)
    observed.cu_context caller
    (bp_analyze_fuel (concretize_memloc_fuel caller) (cfg_analyze caller) caller)
    (cfg_analyze caller)) (Allocation aid) = SOME addrs /\
    MEM (s0.vs_current_bb,s0.vs_inst_idx) addrs
Proof
  strip_tac >>
  `?t. c < t /\ t <= n /\ activation_depth (EL t (q0::qs)) = d /\
    activation_cache (EL t (q0::qs)) d owner aid (b,sz) /\
    (!k. t < k /\ k <= n ==> d < activation_depth (EL k (q0::qs)))` by
    (irule joint_activation_cache_exposure >> simp[activation_depth_def] >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >> simp[]) >>
  Cases_on `EL t (q0::qs)` >>
  gvs[activation_depth_def, activation_cache_current] >>
  irule concretize_open_call_runtime_liveset_context >> simp[] >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `EL t _ = _`)) >>
  goal_assum (drule_at (Pat `EL _ _ = JointConfig _ _ _ _ caller invoke _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = _`)) >>
  goal_assum (drule_at (Pat `o1_walk_view _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `callee_first _ _`)) >>
  simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED
