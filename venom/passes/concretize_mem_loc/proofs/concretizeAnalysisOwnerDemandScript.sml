Theory concretizeAnalysisOwnerDemand
Ancestors
  concretizeAnalysisTemporalDemand concretizeAnalysisIncomingDemand
  concretizeAnalysisReadOrigin frameActivationSeparation frameJointTrace
  frameJointTransition frameOriginHistory frameActivationCache o1PassContract
  ptrDiscipline unitTransformDefs venomInst finite_map list arithmetic

Theorem concretize_untainted_owner_read_liveat:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs q /\ n <= j /\ j <= LENGTH es /\
  EL j (q0::qs) = JointConfig stk PG G tn current inst s oms om hs h /\
  byte IN joint_reads (EL j (q0::qs)) /\ lo <= byte /\
  byte NOTIN joint_mem_taint (EL j (q0::qs)) /\ ~in_revert_forward current s /\
  (!k. n <= k /\ k < j ==> byte NOTIN joint_writes (EL k (q0::qs)) (EL k es)) /\
  activation_cache (EL j (q0::qs)) d owner aid (b,sz) /\
  b <= byte /\ byte < b + sz /\
  activation_location (EL n (q0::qs)) d owner p /\
  o1_walk_view rpolicy 2 C' owner observed /\
  bp = bp_analyze_fuel (concretize_memloc_fuel owner) (cfg_analyze owner) owner /\
  sizes = (\a. if context_alloca_size owner
    (imported_mems_used observed.cu_context owner) a = 0 then NONE
    else SOME (context_alloca_size owner (imported_mems_used observed.cu_context owner) a)) /\
  (!nm. OL alloc_to (mems nm)) /\ OL alloc_to pallocas /\
  ml_iterate_fuel (concretize_memloc_fuel owner) bp mems sizes pallocas
    (cfg_analyze owner) owner FEMPTY FEMPTY = (la,us) ==>
  MEM (Allocation aid) (ml_lookup la p)
Proof
  strip_tac >>
  `joint_config_reachable vs0 C (EL j (q0::qs))` by
    metis_tac[trace_config_at] >>
  `vs0.vs_allocas = FEMPTY` by gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  drule_all joint_read_production_origin >> strip_tac
  >- suspend "local"
  >> suspend "incoming"
QED

Resume concretize_untainted_owner_read_liveat[local]:
  `activation_cache (EL j (q0::qs)) (LENGTH stk) current aid' (b',sz')` by
    simp[activation_cache_def] >>
  `d = LENGTH stk /\ owner = current /\ aid = aid' /\ b = b' /\ sz = sz'` by
    (irule joint_activation_cache_byte_unique >>
     conj_tac >- (qexists_tac `byte` >> simp[]) >>
     goal_assum (drule_at (Pat `joint_config_reachable _ _ _`)) >> simp[]) >>
  gvs[] >> irule concretize_untainted_local_read_liveat_at_location >>
  goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `activation_location _ _ _ _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP om _ = _`)) >>
  goal_assum (drule_at (Pat `mem_read_ops _ = _`)) >>
  goal_assum (drule_at (Pat `EL j (_::_) = _`)) >>
  goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `o1_walk_view _ _ _ _ _`)) >>
  qexists_tac `byte` >> simp[] >> metis_tac[]
QED

Resume concretize_untainted_owner_read_liveat[incoming]:
  drule_all concretize_untainted_incoming_read_liveat >> strip_tac >>
  `d' < LENGTH stk /\ LENGTH stk - SUC d' = k' /\
    LENGTH stk - SUC (LENGTH stk - SUC k') = k'` by decide_tac >>
  `activation_cache (EL j (q0::qs)) d' owner' aid'' (b',sz')` by
    simp[activation_cache_def] >>
  `d = d' /\ owner = owner' /\ aid = aid'' /\ b = b' /\ sz = sz'` by
    (irule joint_activation_cache_byte_unique >>
     conj_tac >- (qexists_tac `byte` >> simp[]) >>
     goal_assum (drule_at (Pat `joint_config_reachable _ _ _`)) >> simp[]) >>
  qpat_x_assum `owner = owner'` SUBST_ALL_TAC >>
  qpat_x_assum `aid = aid''` SUBST_ALL_TAC >>
  qpat_x_assum `d = d'` SUBST_ALL_TAC >>
  first_x_assum irule >> conj_tac >- simp[] >>
  goal_assum (drule_at (Pat `ml_iterate_fuel _ _ _ _ _ _ _ _ _ = _`)) >> simp[] >>
  qexists_tac `observed` >> metis_tac[]
QED

Finalise concretize_untainted_owner_read_liveat
