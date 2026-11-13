Theory frameDemandOwnership
Ancestors
  frameActivationCache frameAllocationOwnership frameAllocationEffects
  frameJointTransition frameJointTrace frameOriginCache frameOriginHistory
  frameOriginReachable ptrDisciplineEmptyTaint ptrDiscipline
  venomExecSemantics venomState venomInst venomMemProps
  frameJointDemand concretizeAnalysisBoundary finite_map list

(* Birth records cache installation, not a physical memory write. *)
Definition allocation_birth_def:
  allocation_birth ctx (JointConfig stk PG G tn current inst s oms om hs h)
    ev d owner aid site <=>
  d = LENGTH stk /\ owner = current /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id = aid /\ FLOOKUP s.vs_allocas aid = NONE /\
  ?fuel post. ev = SOME (OriginOrdinary fuel post) /\
    step_inst fuel ctx inst s = OK post /\
    FLOOKUP post.vs_allocas aid = SOME site
End

Theorem exec_alloca_cache_predecessor:
  exec_alloca inst s sz = OK post /\ FLOOKUP post.vs_allocas aid = SOME site ==>
  FLOOKUP s.vs_allocas aid = SOME site \/
  (inst.inst_id = aid /\ FLOOKUP s.vs_allocas aid = NONE)
Proof
  simp[exec_alloca_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE, AllCaseEqs()]
QED

Theorem step_cache_predecessor:
  step_inst fuel ctx inst s = OK post /\ inst.inst_opcode <> INVOKE /\
  FLOOKUP post.vs_allocas aid = SOME site ==>
  FLOOKUP s.vs_allocas aid = SOME site \/
  (inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
   FLOOKUP s.vs_allocas aid = NONE)
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[step_inst_base_def, AllCaseEqs()] >>
      metis_tac[exec_alloca_cache_predecessor]) >>
  `post.vs_allocas = s.vs_allocas` by metis_tac[step_inst_base_preserves_allocas] >>
  gvs[]
QED

Theorem joint_cache_predecessor:
  !ctx q ev q'. joint_transition ctx q ev q' ==>
  !d owner aid site. activation_cache q' d owner aid site ==>
    activation_cache q d owner aid site \/ allocation_birth ctx q ev d owner aid site
Proof
  ho_match_mp_tac joint_transition_ind >> rpt conj_tac
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume joint_cache_predecessor[next]:
  rpt strip_tac >> fs[activation_cache_def] >>
  simp[activation_cache_def, allocation_birth_def]
  >- (drule_all step_cache_predecessor >> strip_tac >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Resume joint_cache_predecessor[block]:
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `s'.vs_allocas = s.vs_allocas` by
    (gvs[step_inst_non_invoke] >> metis_tac[step_inst_base_preserves_allocas]) >>
  drule enters_block_allocas >> strip_tac >>
  fs[activation_cache_def] >> simp[activation_cache_def]
QED

Resume joint_cache_predecessor[call]:
  rpt strip_tac >>
  `s1.vs_allocas = FEMPTY` by
    (drule setup_callee_empty_allocas >> drule enters_block_allocas >> simp[]) >>
  fs[activation_cache_def] >>
  Cases_on `d = LENGTH stk` >> gvs[activation_cache_def] >>
  `LENGTH stk - d = SUC (LENGTH stk - SUC d)` by decide_tac >>
  gvs[]
QED

Resume joint_cache_predecessor[ret]:
  rpt strip_tac >> drule return_bind_cache >> strip_tac >>
  fs[activation_cache_def] >> simp[activation_cache_def] >>
  `LENGTH stk - d = SUC (LENGTH stk - SUC d)` by decide_tac >>
  simp[]
QED

Finalise joint_cache_predecessor

(* The general backwards alternative also applies if an initial cache is
   deliberately supplied.  Binding existence at adjacent indices is obtained
   by predecessor inversion, not by equating reused depths. *)
Theorem joint_cache_birth_or_initial:
  !j. joint_trace vs0 ctx q0 es qs q /\ j <= LENGTH es /\
  activation_cache (EL j (q0::qs)) d owner aid site ==>
  (!i. i <= j ==> activation_cache (EL i (q0::qs)) d owner aid site) \/
  ?t. t < j /\ allocation_birth ctx (EL t (q0::qs)) (EL t es) d owner aid site /\
      (!i. t < i /\ i <= j ==> activation_cache (EL i (q0::qs)) d owner aid site)
Proof
  Induct
  >- (rpt strip_tac >> disj1_tac >> rpt strip_tac >> `i = 0` by decide_tac >> gvs[]) >>
  rpt strip_tac >>
  `j < LENGTH es` by decide_tac >>
  `joint_transition ctx (EL j (q0::qs)) (EL j es) (EL (SUC j) (q0::qs))` by
    metis_tac[joint_trace_edge_at] >>
  drule joint_cache_predecessor >> disch_then drule >> strip_tac
  >- (first_x_assum drule >> simp[] >> strip_tac
      >- (disj1_tac >> rpt strip_tac >> Cases_on `i = SUC j` >> gvs[]) >>
      disj2_tac >> qexists_tac `t` >> simp[] >> rpt strip_tac >>
      Cases_on `i = SUC j` >> gvs[]) >>
  disj2_tac >> qexists_tac `j` >> simp[] >> rpt strip_tac >>
  `i = SUC j` by decide_tac >> gvs[]
QED

Theorem joint_initial_cache_empty:
  joint_initial vs0 ctx q0 /\ vs0.vs_allocas = FEMPTY ==>
  ~activation_cache q0 d owner aid site
Proof
  simp[Once joint_initial_cases] >> rpt strip_tac >> gvs[activation_cache_def] >>
  drule enters_block_allocas >> strip_tac >> gvs[]
QED

Theorem joint_cache_birth:
  joint_trace vs0 ctx q0 es qs q /\ vs0.vs_allocas = FEMPTY /\
  j <= LENGTH es /\ activation_cache (EL j (q0::qs)) d owner aid site ==>
  ?t. t < j /\ allocation_birth ctx (EL t (q0::qs)) (EL t es) d owner aid site /\
      (!i. t < i /\ i <= j ==>
        d <= activation_depth (EL i (q0::qs)) /\
        activation_cache (EL i (q0::qs)) d owner aid site)
Proof
  strip_tac >> drule_all joint_cache_birth_or_initial >> strip_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
      metis_tac[joint_initial_cache_empty, joint_trace_def]) >>
  qexists_tac `t` >> simp[] >> metis_tac[activation_cache_depth]
QED

Theorem joint_provenance_activation_owner:
  joint_config_reachable vs0 ctx
    (JointConfig stk PG G tn current inst s oms om hs h) /\
  ~ctx_has_dalloca ctx /\ FLOOKUP G v = SOME site ==>
  ?d owner aid. activation_cache
    (JointConfig stk PG G tn current inst s oms om hs h) d owner aid site
Proof
  strip_tac >> fs[joint_config_reachable_def] >>
  drule joint_origin_history_erasure >> strip_tac >>
  drule origin_frame_erasure >> strip_tac >>
  drule_all frame_provenance_owner >> strip_tac
  >- (gvs[cache_has_site_def] >> qexistsl_tac [`LENGTH stk`,`current`,`aid`] >>
      simp[activation_cache_current]) >>
  gvs[saved_has_site_def] >>
  qexistsl_tac [`LENGTH stk - SUC k`,`(EL k stk).cf_fn`,`aid`] >>
  simp[activation_cache_saved]
QED

Theorem joint_provenance_birth:
  joint_trace vs0 ctx q0 es qs q /\ vs0.vs_allocas = FEMPTY /\
  j <= LENGTH es /\
  EL j (q0::qs) = JointConfig stk PG G tn current inst s oms om hs h /\
  ~ctx_has_dalloca ctx /\ FLOOKUP G v = SOME site ==>
  ?d owner aid t.
    t < j /\ allocation_birth ctx (EL t (q0::qs)) (EL t es) d owner aid site /\
    (!i. t < i /\ i <= j ==>
      d <= activation_depth (EL i (q0::qs)) /\
      activation_cache (EL i (q0::qs)) d owner aid site)
Proof
  strip_tac >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_trace_def, joint_chain_length] >>
  `joint_config_reachable vs0 ctx (EL j (q0::qs))` by
    (drule joint_trace_prefix_reachable >> strip_tac >>
     Cases_on `j` >> gvs[EVERY_EL] >>
     rename1 `SUC k <= LENGTH qs` >> `k < LENGTH qs` by decide_tac >> metis_tac[]) >>
  `?d owner aid. activation_cache (EL j (q0::qs)) d owner aid site` by
    (gvs[] >> metis_tac[joint_provenance_activation_owner]) >>
  drule_all joint_cache_birth >> strip_tac >>
  qexistsl_tac [`d`,`owner`,`aid`,`t`] >> simp[]
QED

Theorem joint_demand_owner_birth:
  joint_trace vs0 ctx q0 es qs q /\ vs0.vs_allocas = FEMPTY /\
  n <= j /\ j <= LENGTH es /\
  EL j (q0::qs) = JointConfig stk PG G tn current inst s oms om hs h /\
  ~ctx_has_dalloca ctx /\ FLOOKUP G v = SOME site /\
  byte IN joint_reads (EL j (q0::qs)) /\
  (!k. n <= k /\ k < j ==>
    byte NOTIN joint_writes (EL k (q0::qs)) (EL k es)) ==>
  ?d owner aid t.
    t < j /\ allocation_birth ctx (EL t (q0::qs)) (EL t es) d owner aid site /\
    (!i. t < i /\ i <= j ==>
      d <= activation_depth (EL i (q0::qs)) /\
      activation_cache (EL i (q0::qs)) d owner aid site) /\
    byte IN joint_reads (EL j (q0::qs)) /\
    (!k. MAX n (SUC t) <= k /\ k < j ==>
      byte NOTIN joint_writes (EL k (q0::qs)) (EL k es))
Proof
  strip_tac >> drule_all joint_provenance_birth >> strip_tac >>
  qexistsl_tac [`d`,`owner`,`aid`,`t`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED
