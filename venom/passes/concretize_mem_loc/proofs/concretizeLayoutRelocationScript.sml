Theory concretizeLayoutRelocation
Ancestors
  concretizeLayoutOwnerPairs concretizeLayoutPositions frameRelocationBinding frameDemandTaint
  frameActivationCache frameJointTrace frameJointDemand frameJointTaint
  frameJointTransition ptrDiscipline o1PassContract o1ScheduleDecomp
  unitTransformDefs venomInst venomWf cfgWf finite_map list pred_set arithmetic

(* This is numerical noncollision only. The cache-to-metadata bridge is
 * explicit, and is not a premise added to either frozen stage theorem.
 * Semantic coverage of transformed writes remains a separate obligation. *)
Theorem concretize_relocation_write_demand_noncollision:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs q /\ activation_depth q0 = 0 /\
  n < LENGTH es /\
  (!k d owner aid base size. k <= LENGTH es /\
     activation_cache (EL k (q0::qs)) d owner aid (base,size) ==>
     canonical_metadata C C' (Allocation aid) (positions owner aid) size /\
     (0 < size ==> lo <= positions owner aid)) /\
  joint_relocation_demand lo positions q0 es qs n a z /\
  byte IN joint_writes (EL n (q0::qs)) (EL n es) /\
  relocation_pair lo positions (EL n (q0::qs)) byte w /\ a <> byte ==>
  z <> w
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~joint_read_exempt (EL n (q0::qs))` by
    (irule joint_relocation_demand_nonrevert >> metis_tac[]) >>
  qpat_x_assum `joint_relocation_demand _ _ _ _ _ _ _ _` mp_tac >>
  simp[joint_relocation_demand_def] >> strip_tac >>
  qpat_x_assum `relocation_pair _ _ (EL j _) _ _` mp_tac >>
  qpat_x_assum `relocation_pair _ _ _ byte w` mp_tac >>
  simp[relocation_pair_def] >>
  disch_then strip_assume_tac >> disch_then strip_assume_tac
  >- metis_tac[]
  >- (qpat_x_assum `!k d owner aid base size. _`
        (qspec_then `j` mp_tac) >> simp[] >> disch_then drule >>
      strip_tac >> decide_tac)
  >- (qpat_x_assum `!k d owner aid base size. _`
        (qspec_then `n` mp_tac) >> simp[] >> disch_then drule >>
      strip_tac >> decide_tac) >>
  `vs0.vs_allocas = FEMPTY` by gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `activation_cache (EL n (q0::qs)) d' owner' aid' (b',sz')` by
    (irule (cj 2 joint_untainted_demand_cache) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `activation_cache (EL j _) _ _ _ _`)) >>
     qexists_tac `a` >> simp[] >> qexists_tac `n` >>
     gvs[joint_observed_read_def]) >>
  Cases_on `d' = d /\ aid' = aid`
  >- (gvs[] >> Cases_on `EL n (q0::qs)` >>
      gvs[activation_cache_def] >> decide_tac) >>
  suspend "distinct"

QED

Resume concretize_relocation_write_demand_noncollision[distinct]:
  qpat_assum `!k d owner aid base size. _` (qspec_then `j` mp_tac) >>
  simp[] >> disch_then drule >> strip_tac >>
  qpat_assum `!k d owner aid base size. _` (qspec_then `n` mp_tac) >>
  simp[] >> disch_then (qspecl_then [`d`, `owner`, `aid`, `b`, `sz`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `EL n (q0::qs)` >> pop_assum (mk_asm "writer") >>
  Cases_on `EL j (q0::qs)` >> pop_assum (mk_asm "reader") >>
  fs[joint_read_exempt_def, joint_observed_read_def] >>
  `positions owner' aid' + sz' <= positions owner aid \/
   positions owner aid + sz <= positions owner' aid'` by
    (irule concretize_write_demand_activation_disjoint >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     asm "reader" (irule_at Any) >>
     asm "writer" (irule_at Any) >>
     goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `ptr_discipline _ _ _`)) >>
     goal_assum (drule_at (Pat `callee_first _ _`)) >>
     goal_assum (drule_at (Pat `canonical_metadata _ _ (Allocation aid') _ _`)) >>
     goal_assum (drule_at (Pat `canonical_metadata _ _ (Allocation aid) _ _`)) >>
     asm "writer" (fn th => simp[th]) >>
     asm "reader" (fn th => simp[th]) >>
     goal_assum (drule_at (Pat `activation_cache _ _ _ _ (_,sz')`)) >>
     goal_assum (drule_at (Pat `activation_cache _ _ _ _ (_,sz)`)) >>
     qexistsl_tac [`byte`, `a`] >> simp[] >> metis_tac[]) >> decide_tac
QED

Finalise concretize_relocation_write_demand_noncollision

(* Coverage concerns actual target writes; numerical layout alone does not
 * supply it. Retained demand and noncollision then protect the complement. *)
Theorem concretize_relocation_demand_write_complement:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs q /\ activation_depth q0 = 0 /\
  n < LENGTH es /\
  (!k d owner aid base size. k <= LENGTH es /\
     activation_cache (EL k (q0::qs)) d owner aid (base,size) ==>
     canonical_metadata C C' (Allocation aid) (positions owner aid) size /\
     (0 < size ==> lo <= positions owner aid)) /\
  (!w. w IN target_writes ==> ?byte.
     byte IN joint_writes (EL n (q0::qs)) (EL n es) /\
     relocation_pair lo positions (EL n (q0::qs)) byte w) /\
  joint_relocation_demand lo positions q0 es qs (SUC n) a z /\
  a NOTIN joint_writes (EL n (q0::qs)) (EL n es) ==>
  joint_relocation_demand lo positions q0 es qs n a z /\
  z NOTIN target_writes
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `vs0.vs_allocas = FEMPTY` by
    gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `joint_relocation_demand lo positions q0 es qs n a z` by
    (irule joint_relocation_demand_retained >> metis_tac[]) >>
  conj_tac >- simp[] >>
  strip_tac >>
  qpat_x_assum `!w. w IN target_writes ==> _` drule >> strip_tac >>
  `a <> byte` by metis_tac[] >>
  drule_all concretize_relocation_write_demand_noncollision >> simp[]
QED

Theorem concretize_positions_write_demand_noncollision:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  fixed_region_reserved lo C /\
  joint_trace vs0 C q0 es qs q /\ activation_depth q0 = 0 /\ n < LENGTH es /\
  joint_relocation_demand lo (concretize_positions C') q0 es qs n a z /\
  byte IN joint_writes (EL n (q0::qs)) (EL n es) /\
  relocation_pair lo (concretize_positions C') (EL n (q0::qs)) byte w /\ a <> byte ==>
  z <> w
Proof
  strip_tac >> irule concretize_relocation_write_demand_noncollision >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `joint_relocation_demand _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `relocation_pair _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `callee_first _ _`)) >> simp[] >>
  metis_tac[concretize_positions_trace_cache]
QED

Theorem concretize_positions_demand_write_complement:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  fixed_region_reserved lo C /\
  joint_trace vs0 C q0 es qs q /\ activation_depth q0 = 0 /\ n < LENGTH es /\
  (!w. w IN target_writes ==> ?byte.
    byte IN joint_writes (EL n (q0::qs)) (EL n es) /\
    relocation_pair lo (concretize_positions C') (EL n (q0::qs)) byte w) /\
  joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC n) a z /\
  a NOTIN joint_writes (EL n (q0::qs)) (EL n es) ==>
  joint_relocation_demand lo (concretize_positions C') q0 es qs n a z /\
  z NOTIN target_writes
Proof
  strip_tac >> irule concretize_relocation_demand_write_complement >> simp[] >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `callee_first _ _`)) >> simp[] >>
  metis_tac[concretize_positions_trace_cache]
QED
