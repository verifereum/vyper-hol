Theory concretizePtrOwnerFloor
Ancestors concretizePtrOwnerPath concretizePtrHistoryObservation
  concretizePtrChronologicalHistory concretizePtrAllocationOwnership
  frameExecutionHistory frameRawEndpoints frameResolvedTrace unitMemInv ptrDiscipline
  list rich_list arithmetic

Theorem ptr_reachable_owner_allocas_from:
  ptr_observation_reachable vs C obs /\ ptr_discipline lo C vs /\
  d <= LENGTH obs.po_stack ==>
  allocas_from lo (ptr_owner_view d obs).cf_state
Proof
  strip_tac >> fs[ptr_observation_reachable_def] >>
  Cases_on `d = LENGTH obs.po_stack`
  >- (simp[ptr_owner_view_def] >> fs[ptr_discipline_def] >> metis_tac[]) >>
  qabbrev_tac `n = LENGTH obs.po_stack - SUC d` >>
  `n < LENGTH obs.po_stack` by (simp[Abbr `n`] >> decide_tac) >>
  drule frame_reachable_has_history >> strip_tac >>
  drule_all frame_history_saved_endpoint >> strip_tac >>
  `MEM ((EL n obs.po_stack).cf_inst,(EL n obs.po_stack).cf_state) (EL n hs)` by
    metis_tac[MEM_LAST_NOT_NIL] >>
  drule_all ptr_history_saved_observation >> strip_tac >>
  `allocas_from lo (EL n obs.po_stack).cf_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  simp[ptr_owner_view_def, GSYM ADD1, Abbr `n`]
QED

(* Each owner view of a reachable observation is the state of a reachable
   frame: the current frame, or a saved caller at its suspension point. *)
Theorem ptr_reachable_owner_frame:
  ptr_observation_reachable vs C obs /\ d <= LENGTH obs.po_stack ==>
  ?stk PG G tn fn inst.
    frame_reachable vs C stk PG G tn fn inst (ptr_owner_view d obs).cf_state
Proof
  strip_tac >> fs[ptr_observation_reachable_def] >>
  Cases_on `d = LENGTH obs.po_stack`
  >- (simp[ptr_owner_view_def] >> metis_tac[]) >>
  qabbrev_tac `n = LENGTH obs.po_stack - SUC d` >>
  `n < LENGTH obs.po_stack` by (simp[Abbr `n`] >> decide_tac) >>
  drule frame_reachable_has_history >> strip_tac >>
  drule_all frame_history_saved_endpoint >> strip_tac >>
  `MEM ((EL n obs.po_stack).cf_inst,(EL n obs.po_stack).cf_state) (EL n hs)` by
    metis_tac[MEM_LAST_NOT_NIL] >>
  drule_all ptr_history_saved_observation >> strip_tac >>
  `(ptr_owner_view d obs).cf_state = (EL n obs.po_stack).cf_state` by
    simp[ptr_owner_view_def, GSYM ADD1, Abbr `n`] >>
  metis_tac[]
QED

Theorem ptr_reachable_owner_below_initial_fmp:
  ptr_observation_reachable vs C obs /\ ptr_discipline lo C vs /\
  ctx_has_dalloca C /\ d <= LENGTH obs.po_stack /\
  FLOOKUP (ptr_owner_view d obs).cf_state.vs_allocas aid = SOME (b,sz) ==>
  b + sz <= w2n vs.vs_initial_fmp
Proof
  strip_tac >> drule_all ptr_reachable_owner_frame >> strip_tac >>
  `(ptr_owner_view d obs).cf_state.vs_initial_fmp = vs.vs_initial_fmp` by
    metis_tac[frame_reachable_initial_fmp] >>
  drule frame_reachable_caches_below >> rpt (disch_then drule) >>
  disch_then (qspecl_then [`0`,`aid`,`b`,`sz`] mp_tac) >> simp[]
QED

(* A reachable frame's static allocations end at or below the dynamic floor:
   below the initial free memory pointer under DALLOCA, below
   alloca_next < 2^256 otherwise (raw_mem_ok). *)
Theorem ptr_reachable_alloca_below_dyn_floor:
  frame_reachable vs C stk PG G tn fn inst s /\ ptr_discipline lo C vs /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  vs.vs_allocas = FEMPTY /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
  b + sz <= dyn_floor C vs
Proof
  strip_tac >> simp[dyn_floor_def] >> IF_CASES_TAC
  >- (`s.vs_initial_fmp = vs.vs_initial_fmp` by
        metis_tac[frame_reachable_initial_fmp] >>
      drule frame_reachable_caches_below >> rpt (disch_then drule) >>
      disch_then (qspecl_then [`0`,`aid`,`b`,`sz`] mp_tac) >> simp[]) >>
  `ptr_alloc_table_ok s` by
    (drule_all ptr_frame_alloc_geometry >> simp[ptr_active_alloc_geometry_def]) >>
  `b + sz <= s.vs_alloca_next` by (fs[ptr_alloc_table_ok_def] >> metis_tac[]) >>
  `raw_mem_ok C fn inst s` by (drule_all frame_reachable_mem_inv >> simp[]) >>
  fs[raw_mem_ok_def] >> decide_tac
QED

Theorem ptr_reachable_owner_below_dyn_floor:
  ptr_observation_reachable vs C obs /\ ptr_discipline lo C vs /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  vs.vs_allocas = FEMPTY /\ d <= LENGTH obs.po_stack /\
  FLOOKUP (ptr_owner_view d obs).cf_state.vs_allocas aid = SOME (b,sz) ==>
  b + sz <= dyn_floor C vs
Proof
  strip_tac >> drule_all ptr_reachable_owner_frame >> strip_tac >>
  drule_all ptr_reachable_alloca_below_dyn_floor >> simp[]
QED
