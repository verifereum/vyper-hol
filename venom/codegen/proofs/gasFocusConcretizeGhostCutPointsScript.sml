Theory gasFocusConcretizeGhostCutPoints
Ancestors
  gasFocusConcretizeEndpointCut gasFocusConcretizeHistoricalCut
  gasFocusChronologicalCut concretizePtrStructuralTrace
  concretizePtrStructuralTranscript concretizePtrChronologicalHistory
  concretizePtrPairedPrefix concretizePtrParamShape concretizeLayoutCutSafe
  lowerDloadPtrRawReachable o1SafeUpto unitMemInv list

(* For a fixed paired prefix the stage and initialization witnesses have
   already done their work: only source shape and bounded safety are needed
   to recover the point facts.  Source and target indices range independently. *)
Theorem focus_concretize_ghost_cut_points_ptr_safe:
  o1_ctx_shape C /\ o1_ptr_safe_upto D lo n C vs /\
  ptr_paired_prefix R lp positions lo vs C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  gas_cut n vs at.po_state ==>
  gas_cut n vs a.po_state /\
  (!i. i < LENGTH h ==>
    gas_cut n vs (EL i h).po_state /\
    EVERY (\f. gas_cut n vs f.cf_state) (EL i h).po_stack /\
    ptr_observation_reachable vs C (EL i h) /\
    raw_reachable vs C (EL i h).po_fn (EL i h).po_inst (EL i h).po_state /\
    access_ok lo (EL i h).po_prov (EL i h).po_fn (EL i h).po_inst (EL i h).po_state /\
    taint_ok (EL i h).po_fn (EL i h).po_taint (EL i h).po_inst (EL i h).po_state /\
    allocas_from lo (EL i h).po_state /\
    (ctx_has_dalloca C ==> allocas_below_fmp (EL i h).po_state) /\
    (!tsi ri bi PTi TGi si ei. EL i H = (tsi,ri,bi,PTi,TGi,si,ei) ==>
      ptr_params_erases (dyn_floor C vs) bi PTi (EL i h).po_params /\
      ptr_ledger_erases (dyn_floor C vs) bi TGi (EL i h).po_prov /\
      ptr_saved_erases (dyn_floor C vs) bi si (EL i h).po_stack)) /\
  (!q. q < LENGTH ht ==>
    gas_cut n vs (EL q ht).po_state /\
    EVERY (\f. gas_cut n vs f.cf_state) (EL q ht).po_stack)
Proof
  strip_tac >>
  `ptr_discipline_upto lo n C vs` by fs[o1_ptr_safe_upto_def] >>
  `gas_cut n vs a.po_state` by (drule_all ptr_paired_endpoint_cut_safety >> simp[]) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  `EVERY (\b. gas_cut n vs b.po_state) h` by metis_tac[ptr_chrono_history_cut] >>
  `EVERY (\b. gas_cut n vs b.po_state) ht` by metis_tac[ptr_chrono_history_cut] >>
  asm_rewrite_tac[] >> reverse conj_tac
  >- (gen_tac >> strip_tac >>
      `gas_cut n vs (EL q ht).po_state` by fs[EVERY_EL] >>
      `ptr_chrono_history vs Ct (TAKE (SUC q) ht) (EL q ht)` by
        (drule ptr_chrono_history_prefix >> simp[]) >>
      drule_all ptr_chrono_saved_callers_cut >> simp[]) >>
  gen_tac >> strip_tac >>
  `gas_cut n vs (EL i h).po_state` by fs[EVERY_EL] >>
  `ptr_chrono_history vs C (TAKE (SUC i) h) (EL i h)` by
    (qpat_assum `ptr_chrono_history vs C h a` (mp_tac o MATCH_MP ptr_chrono_history_prefix) >> simp[]) >>
  `EVERY (\f. gas_cut n vs f.cf_state) (EL i h).po_stack` by
    (drule_all ptr_chrono_saved_callers_cut >> simp[]) >>
  `ptr_observation_reachable vs C (EL i h)` by
    (irule (cj 1 ptr_chrono_history_reachable) >> metis_tac[]) >>
  `frame_reachable vs C (EL i h).po_stack (EL i h).po_params (EL i h).po_prov
     (EL i h).po_taint (EL i h).po_fn (EL i h).po_inst (EL i h).po_state` by
    fs[ptr_observation_reachable_def] >>
  `raw_reachable vs C (EL i h).po_fn (EL i h).po_inst (EL i h).po_state` by
    (drule_all lowerDloadPtrRawReachableTheory.frame_reachable_raw >> simp[]) >>
  drule_all ptr_discipline_upto_at >> strip_tac >>
  simp[] >> rpt gen_tac >> strip_tac >>
  drule ptr_structural_transcript_ownership >>
  disch_then (qspec_then `i` mp_tac) >> simp[ptr_snapshot_ownership_def] >> strip_tac >>
  drule o1_ctx_shape_instructions_wf >> strip_tac >>
  drule_all ptr_source_ownership_erases_upto >> simp[]
QED

Theorem focus_concretize_ghost_cut_points_cut_headroom:
  o1_ctx_shape C /\ o1_ptr_safe_upto D lo n C vs /\
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> dload_headroom_ok ctx fn inst s) C vs /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
    raw_mem_ok C fn inst s /\ dload_offset_ok C fn inst s) /\
  ptr_paired_prefix R lp positions lo vs C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  gas_cut n vs at.po_state ==>
  gas_cut n vs a.po_state /\
  (!i. i < LENGTH h ==>
    gas_cut n vs (EL i h).po_state /\
    EVERY (\f. gas_cut n vs f.cf_state) (EL i h).po_stack /\
    ptr_observation_reachable vs C (EL i h) /\
    raw_reachable vs C (EL i h).po_fn (EL i h).po_inst (EL i h).po_state /\
    access_ok lo (EL i h).po_prov (EL i h).po_fn (EL i h).po_inst (EL i h).po_state /\
    taint_ok (EL i h).po_fn (EL i h).po_taint (EL i h).po_inst (EL i h).po_state /\
    allocas_from lo (EL i h).po_state /\
    (ctx_has_dalloca C ==> allocas_below_fmp (EL i h).po_state) /\
    raw_mem_ok C (EL i h).po_fn (EL i h).po_inst (EL i h).po_state /\
    dload_offset_ok C (EL i h).po_fn (EL i h).po_inst (EL i h).po_state /\
    dload_headroom_ok C (EL i h).po_fn (EL i h).po_inst (EL i h).po_state /\
    (!tsi ri bi PTi TGi si ei. EL i H = (tsi,ri,bi,PTi,TGi,si,ei) ==>
      ptr_params_erases (dyn_floor C vs) bi PTi (EL i h).po_params /\
      ptr_ledger_erases (dyn_floor C vs) bi TGi (EL i h).po_prov /\
      ptr_saved_erases (dyn_floor C vs) bi si (EL i h).po_stack)) /\
  (!q. q < LENGTH ht ==>
    gas_cut n vs (EL q ht).po_state /\
    EVERY (\f. gas_cut n vs f.cf_state) (EL q ht).po_stack)
Proof
  strip_tac >>
  drule_all focus_concretize_ghost_cut_points_ptr_safe >> strip_tac >>
  asm_rewrite_tac[] >> gen_tac >> strip_tac >>
  qpat_assum `!i. i < LENGTH h ==> _` (drule_then strip_assume_tac) >>
  fs[mem_inv_raw_reachable] >> metis_tac[]
QED

Theorem focus_concretize_ghost_cut_points:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ptr_paired_prefix R lp positions lo vs C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  gas_cut n vs at.po_state ==>
  gas_cut n vs a.po_state /\
  (!i. i < LENGTH h ==>
    gas_cut n vs (EL i h).po_state /\
    EVERY (\f. gas_cut n vs f.cf_state) (EL i h).po_stack /\
    ptr_observation_reachable vs C (EL i h) /\
    raw_reachable vs C (EL i h).po_fn (EL i h).po_inst (EL i h).po_state /\
    access_ok lo (EL i h).po_prov (EL i h).po_fn (EL i h).po_inst (EL i h).po_state /\
    taint_ok (EL i h).po_fn (EL i h).po_taint (EL i h).po_inst (EL i h).po_state /\
    allocas_from lo (EL i h).po_state /\
    (ctx_has_dalloca C ==> allocas_below_fmp (EL i h).po_state) /\
    raw_mem_ok C (EL i h).po_fn (EL i h).po_inst (EL i h).po_state /\
    dload_offset_ok C (EL i h).po_fn (EL i h).po_inst (EL i h).po_state /\
    dload_headroom_ok C (EL i h).po_fn (EL i h).po_inst (EL i h).po_state /\
    (!tsi ri bi PTi TGi si ei. EL i H = (tsi,ri,bi,PTi,TGi,si,ei) ==>
      ptr_params_erases (dyn_floor C vs) bi PTi (EL i h).po_params /\
      ptr_ledger_erases (dyn_floor C vs) bi TGi (EL i h).po_prov /\
      ptr_saved_erases (dyn_floor C vs) bi si (EL i h).po_stack)) /\
  (!q. q < LENGTH ht ==>
    gas_cut n vs (EL q ht).po_state /\
    EVERY (\f. gas_cut n vs f.cf_state) (EL q ht).po_stack)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  fs[o1_safe_upto_def] >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==> dload_headroom_ok ctx fn inst s) C vs` by fs[mem_inv_raw_reachable] >>
  drule_all focus_concretize_ghost_cut_points_cut_headroom >> simp[]
QED
