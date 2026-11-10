Theory concretizeLayoutOwnerPairs
Ancestors concretizeLayoutLocalDemand concretizeLayoutCommonCall concretizeLayoutWriteCall
  concretizeAnalysisTemporalDemand frameOpenCall frameActivationCache frameJointTrace
  frameJointTransition frameDemandTaint unitTransformDefs ptrDiscipline o1PassContract venomInst venomWf list arithmetic

Theorem concretize_write_demand_activation_disjoint:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs q /\ activation_depth q0 = 0 /\
  n < LENGTH es /\ n <= j /\ j <= LENGTH es /\
  EL n (q0::qs) = JointConfig stkN PGN GN tnN writer instN sN omsN omN hsN hN /\
  ~in_revert_forward writer sN /\
  byteB IN joint_writes (EL n (q0::qs)) (EL n es) /\ lo <= byteB /\
  EL j (q0::qs) = JointConfig stkJ PGJ GJ tnJ reader instJ sJ omsJ omJ hsJ hJ /\
  byteA IN joint_reads (EL j (q0::qs)) /\ lo <= byteA /\
  byteA NOTIN joint_mem_taint (EL j (q0::qs)) /\ ~in_revert_forward reader sJ /\
  (!k. n <= k /\ k < j ==> byteA NOTIN joint_writes (EL k (q0::qs)) (EL k es)) /\
  activation_cache (EL j (q0::qs)) dA ownerA aidA (bA,szA) /\
  activation_cache (EL n (q0::qs)) dB ownerB aidB (bB,szB) /\
  bA <= byteA /\ byteA < bA+szA /\ bB <= byteB /\ byteB < bB+szB /\
  (dA <> dB \/ aidA <> aidB) /\
  canonical_metadata C C' (Allocation aidA) pA szA /\
  canonical_metadata C C' (Allocation aidB) pB szB ==>
  pA+szA <= pB \/ pB+szB <= pA
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `vs0.vs_allocas = FEMPTY` by gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `activation_cache (EL n (q0::qs)) dA ownerA aidA (bA,szA)` by
    (irule (cj 2 joint_untainted_demand_cache) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `activation_cache (EL j _) _ _ _ _`)) >>
     qexists_tac `byteA` >> simp[] >> qexists_tac `n` >> simp[]) >>
  Cases_on `dA = dB`
  >- (`ownerA = ownerB` by
        (qpat_x_assum `EL n (_::_) = _` (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
         gvs[activation_cache_def] >> metis_tac[]) >>
      qpat_x_assum `dA = dB` SUBST_ALL_TAC >>
      qpat_x_assum `ownerA = ownerB` SUBST_ALL_TAC >>
      `aidA <> aidB` by metis_tac[] >>
      drule_all concretize_same_activation_write_demand_disjoint >> simp[]) >>
  `dA <= activation_depth (EL n (q0::qs)) /\
   dB <= activation_depth (EL n (q0::qs))` by metis_tac[activation_cache_depth] >>
  Cases_on `dA < dB`
  >- suspend "demand_ancestor" >>
  suspend "write_ancestor"
QED

Resume concretize_write_demand_activation_disjoint[demand_ancestor]:
  `?c stk PG G tn invoke s oms om hs h.
    c < n /\ LENGTH stk = dA /\ EL c es = NONE /\
    EL c (q0::qs) = JointConfig stk PG G tn ownerA invoke s oms om hs h /\
    joint_transition C (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
    activation_cache (EL c (q0::qs)) dA ownerA aidA (bA,szA) /\
    invoke.inst_opcode = INVOKE /\
    (!k. c < k /\ k <= n ==> dA < activation_depth (EL k (q0::qs)))` by
    (irule joint_activation_cache_open_call >> simp[] >>
     conj_tac >- (gvs[] >> decide_tac) >> metis_tac[]) >>
  qpat_x_assum `LENGTH stk = dA` (SUBST_ALL_TAC o SYM) >>
  drule_all concretize_common_call_activation_disjoint >> simp[]
QED

Resume concretize_write_demand_activation_disjoint[write_ancestor]:
  `dB < dA` by
    (qpat_x_assum `~(dA < dB)` mp_tac >>
     qpat_x_assum `dA <> dB` mp_tac >> decide_tac) >>
  `?c stk PG G tn invoke s oms om hs h.
    c < n /\ LENGTH stk = dB /\ EL c es = NONE /\
    EL c (q0::qs) = JointConfig stk PG G tn ownerB invoke s oms om hs h /\
    joint_transition C (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
    activation_cache (EL c (q0::qs)) dB ownerB aidB (bB,szB) /\
    invoke.inst_opcode = INVOKE /\
    (!k. c < k /\ k <= n ==> dB < activation_depth (EL k (q0::qs)))` by
    (irule joint_activation_cache_open_call >> simp[] >>
     conj_tac >- (gvs[] >> decide_tac) >> metis_tac[]) >>
  qpat_x_assum `LENGTH stk = dB` (SUBST_ALL_TAC o SYM) >>
  drule_all concretize_common_call_write_activation_disjoint >> simp[]
QED

Finalise concretize_write_demand_activation_disjoint
