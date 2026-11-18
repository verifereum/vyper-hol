Theory gasFocusConcretizeHistoricalCut
Ancestors
  gasFocusChronologicalCut concretizeLayoutCutSafe
  concretizePtrHistoricalPlacement concretizePtrExecutedCoverage
  concretizePtrSourceOwnership concretizePtrActivationBirths
  concretizePtrActivationChronology concretizePtrChronologicalHistory
  concretizePtrPrefixLedger concretizePtrStructuralTrace
  concretizePtrStructuralTranscript concretizePtrStagePlacements
  concretizePtrOwnerPath o1PassContract o1SafeUpto o1ScheduleDecompHelpers
  venomWf venomInst ptrDiscipline finite_map list arithmetic

Theorem ptr_source_ownership_erases_upto:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_discipline_upto lo n C vs /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  gas_cut n vs a.po_state ==>
  ptr_params_erases (dyn_floor C vs) births PT a.po_params /\
  ptr_ledger_erases (dyn_floor C vs) births TG a.po_prov /\
  ptr_saved_erases (dyn_floor C vs) births saved a.po_stack
Proof
  strip_tac >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule ptr_source_birth_caches_activations >> strip_tac >>
  drule ptr_source_activations_sound >> strip_tac >>
  `EVERY (\obs. ctx_has_dalloca C ==> allocas_below_fmp obs.po_state) h` by
    (drule_all ptr_chrono_history_cut >> simp[EVERY_MEM] >> strip_tac >>
     drule ptr_chrono_history_reachable >>
     simp[EVERY_MEM, ptr_observation_reachable_def] >> strip_tac >>
     rpt strip_tac >>
     qpat_assum `!obs. MEM obs h ==> gas_cut _ _ _` (drule_then assume_tac) >>
     qpat_assum `!obs. MEM obs h ==> frame_reachable _ _ _ _ _ _ _ _ _`
       (drule_then assume_tac) >>
     drule_all ptr_discipline_upto_at >> simp[]) >>
  fs[ptr_discipline_upto_def] >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_source_ownership_history_erases >> simp[]
QED

Theorem ptr_live_birth_owner_cache[local]:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  FLOOKUP TG v = SOME (token,aid) /\
  FLOOKUP births (token,aid) = SOME (b,sz) ==>
  ?d. d <= LENGTH a.po_stack /\
    EL (LENGTH a.po_stack - d) tokens = token /\
    FLOOKUP registry token = SOME (ptr_owner_view d a).cf_fn /\
    FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (b,sz)
Proof
  strip_tac >>
  drule_all ptr_source_ownership_live_prov >> strip_tac >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule ptr_source_birth_caches_activations >> strip_tac >>
  drule ptr_source_activations_length >> strip_tac >>
  drule ptr_source_birth_caches_slices >> strip_tac >>
  gs[MEM_EL] >> rename1 `k < SUC (LENGTH a.po_stack)` >>
  qexists_tac `LENGTH a.po_stack - k` >>
  `LENGTH a.po_stack - (LENGTH a.po_stack - k) = k` by decide_tac >>
  simp[] >>
  conj_tac
  >- (drule ptr_source_activations_owner_lookup >>
      disch_then (qspec_then `LENGTH a.po_stack - k` mp_tac) >> simp[]) >>
  qpat_assum `ptr_birth_slices _ _ _` (mp_tac o REWRITE_RULE [ptr_birth_slices_def]) >>
  disch_then (qspecl_then [`LENGTH a.po_stack - k`,`aid`] mp_tac) >> simp[]
QED

Theorem ptr_transcript_historical_placement_upto:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  (o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs) /\
  ptr_discipline_upto lo n C vs /\ gas_cut n vs a.po_state /\
  ptr_stage_placements C' positions /\
  ptr_structural_transcript R vs C Ct h a ht at done tokens registry births PT TG saved entries H /\
  i <= j /\ j < LENGTH h /\
  EL i H = (tsi,ri,bi,PTi,TGi,si,ei) /\
  EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
  FLOOKUP TGi v = SOME (token,aid) /\
  FLOOKUP (EL i h).po_prov v = SOME (b,sz) ==>
  ?d owner output p.
    d <= LENGTH (EL i h).po_stack /\
    EL (LENGTH (EL i h).po_stack-d) tsi = token /\
    FLOOKUP ri token = SOME owner /\
    owner = (ptr_owner_view d (EL i h)).cf_fn /\
    FLOOKUP (ptr_owner_view d (EL i h)).cf_state.vs_allocas aid = SOME (b,sz) /\
    lookup_function owner.fn_name C'.ctx_functions = SOME output /\
    MEM (Allocation aid,p,sz) output.fn_mems_used /\
    FLOOKUP positions (Allocation aid) = SOME (p,sz) /\
    FLOOKUP bi (token,aid) = SOME (b,sz) /\
    FLOOKUP bj (token,aid) = SOME (b,sz) /\
    FLOOKUP rj token = SOME owner
Proof
  strip_tac >> `i < LENGTH h` by decide_tac >>
  drule ptr_structural_transcript_ownership >> disch_then (qspec_then `i` mp_tac) >>
  simp[ptr_snapshot_ownership_def] >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  `gas_cut n vs (EL i h).po_state` by
    (drule_all ptr_chrono_history_cut >> simp[EVERY_EL]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def] >>
     metis_tac[venomFnInstsProofsTheory.fn_insts_mem_block]) >>
  `FLOOKUP bi (token,aid) = SOME (b,sz)` by
    (drule_all ptr_source_ownership_erases_upto >> simp[ptr_ledger_erases_def] >>
     strip_tac >>
     qpat_x_assum `!v. ptr_owner_erases _ _ _ _` (qspec_then `v` mp_tac) >>
     simp[ptr_owner_erases_def]) >>
  `FLOOKUP bj (token,aid) = SOME (b,sz)` by
    (drule_all (Q.SPEC `j` ptr_transcript_birth_retained) >> simp[]) >>
  drule_all ptr_live_birth_owner_cache >> disch_then (qx_choose_then `d` strip_assume_tac) >>
  `ptr_observation_reachable vs C (EL i h)` by
    (drule ptr_chrono_history_reachable >> simp[EVERY_EL]) >>
  fs[ptr_observation_reachable_def] >>
  `?output p.
    lookup_function (ptr_owner_view d (EL i h)).cf_fn.fn_name C'.ctx_functions = SOME output /\
    MEM (Allocation aid,p,sz) output.fn_mems_used` by
    (Cases_on `d = LENGTH (EL i h).po_stack`
     >- (gvs[ptr_owner_view_def] >> drule_all ptr_frame_current_mems_static >> simp[]) >>
     `MEM (ptr_owner_view d (EL i h)) (EL i h).po_stack` by
       (simp[ptr_owner_view_def] >> irule EL_MEM >> decide_tac) >>
     drule_all ptr_frame_saved_mems_static >> simp[]) >>
  `FLOOKUP rj token = SOME (ptr_owner_view d (EL i h)).cf_fn` by
    (drule_all (Q.SPEC `j` ptr_transcript_registry_retained) >> simp[]) >>
  qexistsl [`d`,`output`,`p`] >>
  fs[ptr_stage_placements_def] >> metis_tac[lookup_function_MEM]
QED
