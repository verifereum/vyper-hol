Theory concretizeLayoutDemand
Ancestors concretizeAnalysisOwnerDemand concretizeAnalysisImportedDemand
  concretizeAnalysisTemporalDemand frameOpenCall frameJointTrace frameJointTransition
  frameActivationCache o1PassContract ptrDiscipline venomInst finite_map list arithmetic

Theorem concretize_common_call_activation_livesets:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs q /\ c < n /\ n <= j /\ j <= LENGTH es /\
  EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 caller invoke s0 oms0 om0 hs0 h0 /\
  joint_transition C (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
  (!k. c < k /\ k <= n ==> LENGTH stk0 < activation_depth (EL k (q0::qs))) /\
  activation_cache (EL n (q0::qs)) dB ownerB aidB (bB,szB) /\ LENGTH stk0 < dB /\
  bB <= byteB /\ byteB < bB + szB /\
  EL j (q0::qs) = JointConfig stkJ PGJ GJ tnJ reader instJ sJ omsJ omJ hsJ hJ /\
  byteA IN joint_reads (EL j (q0::qs)) /\ lo <= byteA /\
  byteA NOTIN joint_mem_taint (EL j (q0::qs)) /\ ~in_revert_forward reader sJ /\
  (!k. n <= k /\ k < j ==> byteA NOTIN joint_writes (EL k (q0::qs)) (EL k es)) /\
  activation_cache (EL j (q0::qs)) (LENGTH stk0) caller aidA (bA,szA) /\
  bA <= byteA /\ byteA < bA + szA /\ o1_walk_view rpolicy 2 C' caller observed ==>
  ?addrsA addrsB.
    FLOOKUP (context_mem_livesets (concretize_memloc_fuel caller)
      observed.cu_context caller
      (bp_analyze_fuel (concretize_memloc_fuel caller) (cfg_analyze caller) caller)
      (cfg_analyze caller)) (Allocation aidA) = SOME addrsA /\
    FLOOKUP (context_mem_livesets (concretize_memloc_fuel caller)
      observed.cu_context caller
      (bp_analyze_fuel (concretize_memloc_fuel caller) (cfg_analyze caller) caller)
      (cfg_analyze caller)) (Allocation aidB) = SOME addrsB /\
    MEM (s0.vs_current_bb,s0.vs_inst_idx) addrsA /\
    MEM (s0.vs_current_bb,s0.vs_inst_idx) addrsB
Proof
  strip_tac >>
  `n <= LENGTH es` by decide_tac >>
  Cases_on `EL n (q0::qs)` >>
  rename1 `EL n (q0::qs) = JointConfig stkN PGN GN tnN current instN sN omsN omN hsN hN` >>
  `active_inst caller invoke s0` by
    (qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_call_iff] >> metis_tac[]) >>
  `(EL (LENGTH stkN - SUC (LENGTH stk0)) stkN).cf_fn = caller /\
   (EL (LENGTH stkN - SUC (LENGTH stk0)) stkN).cf_inst = invoke /\
   (EL (LENGTH stkN - SUC (LENGTH stk0)) stkN).cf_state = s0 /\
   invoke.inst_opcode = INVOKE` by
    (irule joint_open_call_saved_at >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_transition _ _ _ _`)) >>
     goal_assum (drule_at (Pat `EL n (_::_) = _`)) >>
     simp[] >> metis_tac[]) >>
  `LENGTH stk0 < LENGTH stkN` by
    (qpat_x_assum `!k. c < k /\ k <= n ==> _` (qspec_then `n` mp_tac) >>
     simp[activation_depth_def]) >>
  `activation_location (EL n (q0::qs)) (LENGTH stk0) caller
     (s0.vs_current_bb,s0.vs_inst_idx)` by simp[activation_location_def] >>
  `?addrsA. FLOOKUP (context_mem_livesets (concretize_memloc_fuel caller)
      observed.cu_context caller
      (bp_analyze_fuel (concretize_memloc_fuel caller) (cfg_analyze caller) caller)
      (cfg_analyze caller)) (Allocation aidA) = SOME addrsA /\
      MEM (s0.vs_current_bb,s0.vs_inst_idx) addrsA` by
    (irule concretize_untainted_owner_read_liveset >>
     conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `activation_location _ _ _ _`)) >>
     goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `EL j (_::_) = _`)) >>
     goal_assum (drule_at (Pat `o1_walk_view _ _ _ _ _`)) >>
     qexists_tac `byteA` >> simp[] >> metis_tac[]) >>
  `activation_cache (EL n (q0::qs)) dB ownerB aidB (bB,szB)` by metis_tac[] >>
  `?addrsB. FLOOKUP (context_mem_livesets (concretize_memloc_fuel caller)
      observed.cu_context caller
      (bp_analyze_fuel (concretize_memloc_fuel caller) (cfg_analyze caller) caller)
      (cfg_analyze caller)) (Allocation aidB) = SOME addrsB /\
      MEM (s0.vs_current_bb,s0.vs_inst_idx) addrsB` by
    (irule concretize_open_call_activation_liveset_context >>
     goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_transition _ _ _ _`)) >>
     goal_assum (drule_at (Pat `activation_cache _ _ ownerB _ _`)) >>
     goal_assum (drule_at (Pat `o1_walk_view _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `EL c (_::_) = _`)) >>
     qexists_tac `byteB` >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem concretize_common_call_livesets:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs q /\ c < n /\ n <= j /\ j <= LENGTH es /\
  EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 caller invoke s0 oms0 om0 hs0 h0 /\
  joint_transition C (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
  (!k. c < k /\ k <= n ==> LENGTH stk0 < activation_depth (EL k (q0::qs))) /\
  EL n (q0::qs) = JointConfig stkN PGN GN tnN current instN sN omsN omN hsN hN /\
  FLOOKUP sN.vs_allocas aidB = SOME (bB,szB) /\ bB <= byteB /\ byteB < bB + szB /\
  EL j (q0::qs) = JointConfig stkJ PGJ GJ tnJ reader instJ sJ omsJ omJ hsJ hJ /\
  byteA IN joint_reads (EL j (q0::qs)) /\ lo <= byteA /\
  byteA NOTIN joint_mem_taint (EL j (q0::qs)) /\ ~in_revert_forward reader sJ /\
  (!k. n <= k /\ k < j ==> byteA NOTIN joint_writes (EL k (q0::qs)) (EL k es)) /\
  activation_cache (EL j (q0::qs)) (LENGTH stk0) caller aidA (bA,szA) /\
  bA <= byteA /\ byteA < bA + szA /\ o1_walk_view rpolicy 2 C' caller observed ==>
  ?addrsA addrsB.
    FLOOKUP (context_mem_livesets (concretize_memloc_fuel caller)
      observed.cu_context caller
      (bp_analyze_fuel (concretize_memloc_fuel caller) (cfg_analyze caller) caller)
      (cfg_analyze caller)) (Allocation aidA) = SOME addrsA /\
    FLOOKUP (context_mem_livesets (concretize_memloc_fuel caller)
      observed.cu_context caller
      (bp_analyze_fuel (concretize_memloc_fuel caller) (cfg_analyze caller) caller)
      (cfg_analyze caller)) (Allocation aidB) = SOME addrsB /\
    MEM (s0.vs_current_bb,s0.vs_inst_idx) addrsA /\
    MEM (s0.vs_current_bb,s0.vs_inst_idx) addrsB
Proof
  strip_tac >>
  `activation_cache (EL n (q0::qs)) (LENGTH stkN) current aidB (bB,szB)` by
    simp[activation_cache_current] >>
  `LENGTH stk0 < LENGTH stkN` by
    (qpat_x_assum `!k. c < k /\ k <= n ==> _` (qspec_then `n` mp_tac) >>
     simp[activation_depth_def]) >>
  drule_all concretize_common_call_activation_livesets >> simp[]
QED
