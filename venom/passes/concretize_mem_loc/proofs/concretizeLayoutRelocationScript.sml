Theory concretizeLayoutRelocation
Ancestors
  concretizeLayoutOwnerPairs concretizeLayoutPositions frameRelocationBinding frameDemandTaint
  frameActivationCache frameJointTrace frameJointDemand frameJointTaint
  frameJointTransition ptrDiscipline o1PassContract o1ScheduleDecomp
  unitTransformDefs venomInst venomWf cfgWf frameWriteOwnership frameDemandOwnership
  frameOriginHistory frameOriginReachable finite_map list pred_set arithmetic

(* This is numerical noncollision only. The cache-to-metadata bridge is
 * explicit, and is not a premise added to either frozen stage theorem.
 * Semantic coverage of transformed writes remains a separate obligation. *)
(* Without DALLOCA every written byte at or above lo lies in a live cache. *)
Theorem joint_write_cached[local]:
  joint_trace vs0 C q0 es qs q /\ ptr_discipline lo C vs0 /\
  ~ctx_has_dalloca C /\ n < LENGTH es /\
  ~joint_read_exempt (EL n (q0::qs)) /\
  byte IN joint_writes (EL n (q0::qs)) (EL n es) /\ lo <= byte ==>
  ?d owner aid b sz. activation_cache (EL n (q0::qs)) d owner aid (b,sz) /\
    b <= byte /\ byte < b + sz
Proof
  strip_tac >> drule_all joint_trace_edge_at >> strip_tac >>
  `?stk PG G tn fn inst s oms om hs h.
     EL n (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h` by
    (Cases_on `EL n (q0::qs)` >> simp[]) >>
  gvs[joint_read_exempt_def] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (gvs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `access_ok lo G fn inst s` by metis_tac[ptr_discipline_def] >>
  `byte IN range_bytes (source_memory_write_ranges inst s)` by
    (drule joint_writes_source_subset >> metis_tac[SUBSET_DEF]) >>
  drule_all access_ok_write_site >> strip_tac >>
  `ctx_has_dalloca C ==> ptr_discipline lo C vs0` by simp[] >>
  `ctx_has_dalloca C ==> FST (b,sz) < w2n vs0.vs_initial_fmp` by simp[] >>
  drule_all joint_provenance_activation_owner >> strip_tac >>
  metis_tac[]
QED

(* A live cache at j holding a demanded byte and a live cache at n holding a
   written byte relocate the two bytes to distinct positions. *)
Theorem relocation_cached_pair_noncollision[local]:
  joint_trace vs0 C q0 es qs q /\
  joint_observed_read (EL j (q0::qs)) a /\
  byte IN joint_writes (EL n (q0::qs)) (EL n es) /\
  activation_cache (EL j (q0::qs)) d' owner' aid' (b',sz') /\
  activation_cache (EL n (q0::qs)) d owner aid (b,sz) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\
  activation_depth q0 = 0 /\ n < LENGTH es /\ n <= j /\ j <= LENGTH es /\
  (!k d owner aid base size. k <= LENGTH es /\
     activation_cache (EL k (q0::qs)) d owner aid (base,size) ==>
     canonical_metadata C C' (Allocation aid) (positions owner aid) size) /\
  ~joint_read_exempt (EL n (q0::qs)) /\
  (!k. n <= k /\ k < j ==> a NOTIN joint_writes (EL k (q0::qs)) (EL k es)) /\
  lo <= a /\ lo <= byte /\ a <> byte /\
  b' <= a /\ a < b' + sz' /\ b <= byte /\ byte < b + sz ==>
  positions owner' aid' + (a - b') <> positions owner aid + (byte - b)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `vs0.vs_allocas = FEMPTY` by gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `activation_cache (EL n (q0::qs)) d' owner' aid' (b',sz')` by
    (irule (cj 2 joint_untainted_demand_cache) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `activation_cache (EL j _) _ _ _ _`)) >>
     qexists_tac `a` >> simp[] >> qexists_tac `n` >>
     gvs[joint_observed_read_def]) >>
  Cases_on `d' = d /\ aid' = aid`
  >- (gvs[] >>
      `!c. activation_cache c d owner aid (b,sz) /\
           activation_cache c d owner' aid (b',sz') ==>
           owner' = owner /\ b' = b /\ sz' = sz` by
        (rpt (pop_assum kall_tac) >> Cases >>
         simp[activation_cache_def] >> rpt strip_tac >> gvs[]) >>
      first_x_assum (qspec_then `EL n (q0::qs)` mp_tac) >>
      impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac >> gvs[] >> decide_tac) >>
  suspend "distinct"
QED

Resume relocation_cached_pair_noncollision[distinct]:
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

Finalise relocation_cached_pair_noncollision

(* Static bytes stay below lo, cached bytes land in [lo, initial fmp) under
   DALLOCA, and dynamic bytes stay at or above the initial fmp. Without
   DALLOCA every demanded or written byte at or above lo is cached, so the
   dynamic case cannot meet a cached one. *)
Theorem concretize_relocation_write_demand_noncollision:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ activation_depth q0 = 0 /\
  n < LENGTH es /\
  (!k d owner aid base size. k <= LENGTH es /\
     activation_cache (EL k (q0::qs)) d owner aid (base,size) ==>
     canonical_metadata C C' (Allocation aid) (positions owner aid) size /\
     (0 < size ==> lo <= positions owner aid) /\
     (ctx_has_dalloca C ==>
        positions owner aid + size <= w2n vs0.vs_initial_fmp)) /\
  joint_relocation_demand lo positions q0 es qs n a z /\
  byte IN joint_writes (EL n (q0::qs)) (EL n es) /\
  relocation_pair lo positions (EL n (q0::qs)) byte w /\ a <> byte ==>
  z <> w
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~joint_read_exempt (EL n (q0::qs))` by
    (irule joint_relocation_demand_nonrevert >> metis_tac[]) >>
  `vs0.vs_allocas = FEMPTY` by gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `EVERY wf_function C.ctx_functions` by
    (gvs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  qpat_x_assum `joint_relocation_demand _ _ _ _ _ _ _ _` mp_tac >>
  simp[joint_relocation_demand_def] >>
  disch_then (qx_choose_then `j` (map_every assume_tac o CONJUNCTS)) >>
  `n <= LENGTH es` by decide_tac >>
  `joint_initial_fmp (EL n (q0::qs)) = w2n vs0.vs_initial_fmp /\
   joint_initial_fmp (EL j (q0::qs)) = w2n vs0.vs_initial_fmp` by
    (conj_tac >> irule joint_initial_fmp_trace >> metis_tac[]) >>
  `!k d owner aid b sz x. k <= LENGTH es /\
     activation_cache (EL k (q0::qs)) d owner aid (b,sz) /\
     b <= x /\ x < b + sz ==>
     lo <= positions owner aid /\
     (ctx_has_dalloca C ==> positions owner aid + sz <= w2n vs0.vs_initial_fmp)` by
    (rpt gen_tac >> strip_tac >> `0 < sz` by decide_tac >>
     qpat_assum `!k d owner aid base size. _`
       (qspecl_then [`k`, `d`, `owner`, `aid`, `b`, `sz`] mp_tac) >>
     simp[]) >>
  `!k d owner aid base size. k <= LENGTH es /\
     activation_cache (EL k (q0::qs)) d owner aid (base,size) ==>
     canonical_metadata C C' (Allocation aid) (positions owner aid) size` by
    metis_tac[] >>
  qpat_x_assum `relocation_pair _ _ (EL j _) _ _`
    (strip_assume_tac o REWRITE_RULE [relocation_pair_def]) >>
  qpat_x_assum `relocation_pair _ _ (EL n _) _ _`
    (strip_assume_tac o REWRITE_RULE [relocation_pair_def]) >|
  [decide_tac,
   `lo <= positions owner aid` by metis_tac[] >> decide_tac,
   decide_tac,
   `lo <= positions owner aid` by metis_tac[] >> decide_tac,
   drule_all relocation_cached_pair_noncollision >> gvs[],
   suspend "cached_dynamic",
   decide_tac,
   suspend "dynamic_cached",
   decide_tac]
QED

Resume concretize_relocation_write_demand_noncollision[cached_dynamic]:
  Cases_on `ctx_has_dalloca C`
  >- (`positions owner aid + sz <= w2n vs0.vs_initial_fmp` by metis_tac[] >>
      decide_tac) >>
  `?d' owner' aid' b' sz'. activation_cache (EL n (q0::qs)) d' owner' aid' (b',sz') /\
     b' <= byte /\ byte < b' + sz'` by
    (irule joint_write_cached >> metis_tac[]) >>
  `b' + sz' <= joint_initial_fmp (EL n (q0::qs))` by metis_tac[] >>
  decide_tac
QED

Resume concretize_relocation_write_demand_noncollision[dynamic_cached]:
  Cases_on `ctx_has_dalloca C`
  >- (`positions owner aid + sz <= w2n vs0.vs_initial_fmp` by metis_tac[] >>
      decide_tac) >>
  `?d' owner' aid' b' sz'. activation_cache (EL j (q0::qs)) d' owner' aid' (b',sz') /\
     b' <= a /\ a < b' + sz'` by
    (irule joint_observed_read_cached >> metis_tac[]) >>
  `b' + sz' <= joint_initial_fmp (EL j (q0::qs))` by metis_tac[] >>
  decide_tac
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
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ activation_depth q0 = 0 /\
  n < LENGTH es /\
  (!k d owner aid base size. k <= LENGTH es /\
     activation_cache (EL k (q0::qs)) d owner aid (base,size) ==>
     canonical_metadata C C' (Allocation aid) (positions owner aid) size /\
     (0 < size ==> lo <= positions owner aid) /\
     (ctx_has_dalloca C ==>
        positions owner aid + size <= w2n vs0.vs_initial_fmp)) /\
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
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\
  (ctx_has_dalloca C ==>
     ?eom. max_live_eom C' = SOME eom /\ eom <= w2n vs0.vs_initial_fmp) /\
  fixed_region_reserved lo C /\
  joint_trace vs0 C q0 es qs q /\ activation_depth q0 = 0 /\ n < LENGTH es /\
  joint_relocation_demand lo (concretize_positions C') q0 es qs n a z /\
  byte IN joint_writes (EL n (q0::qs)) (EL n es) /\
  relocation_pair lo (concretize_positions C') (EL n (q0::qs)) byte w /\ a <> byte ==>
  z <> w
Proof
  strip_tac >>
  `!k d owner aid base size. k <= LENGTH es /\
     activation_cache (EL k (q0::qs)) d owner aid (base,size) ==>
     canonical_metadata C C' (Allocation aid) (concretize_positions C' owner aid) size /\
     (0 < size ==> lo <= concretize_positions C' owner aid) /\
     (ctx_has_dalloca C ==>
        concretize_positions C' owner aid + size <= w2n vs0.vs_initial_fmp)` by
    (rpt gen_tac >> strip_tac >>
     drule_all concretize_positions_trace_cache >> strip_tac >> simp[] >>
     strip_tac >> qpat_x_assum `ctx_has_dalloca C ==> ?eom. _` drule >>
     strip_tac >> drule_all concretize_positions_cache_room >> decide_tac) >>
  irule concretize_relocation_write_demand_noncollision >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `joint_relocation_demand _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `relocation_pair _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `callee_first _ _`)) >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem concretize_positions_demand_write_complement:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\
  (ctx_has_dalloca C ==>
     ?eom. max_live_eom C' = SOME eom /\ eom <= w2n vs0.vs_initial_fmp) /\
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
  strip_tac >>
  `!k d owner aid base size. k <= LENGTH es /\
     activation_cache (EL k (q0::qs)) d owner aid (base,size) ==>
     canonical_metadata C C' (Allocation aid) (concretize_positions C' owner aid) size /\
     (0 < size ==> lo <= concretize_positions C' owner aid) /\
     (ctx_has_dalloca C ==>
        concretize_positions C' owner aid + size <= w2n vs0.vs_initial_fmp)` by
    (rpt gen_tac >> strip_tac >>
     drule_all concretize_positions_trace_cache >> strip_tac >> simp[] >>
     strip_tac >> qpat_x_assum `ctx_has_dalloca C ==> ?eom. _` drule >>
     strip_tac >> drule_all concretize_positions_cache_room >> decide_tac) >>
  irule concretize_relocation_demand_write_complement >> asm_rewrite_tac[] >>
  qexistsl_tac [`C`, `C'`, `names`, `q`, `rpolicy`, `vs0`] >> asm_rewrite_tac[]
QED
