Theory gasFocusConcretizeWriterSeed
Ancestors
  gasFocusConcretizeHistoricalCut gasFocusConcretizeOwnedSeed
  concretizePtrHistoricalWriteExclusion concretizePtrWriteClassification
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrChronologicalDemand
  concretizePtrAllocationOwnership concretizePtrOwnerSeeds
  gasFocusChronologicalCut concretizeLayoutCutSafe concretizePtrOperationalOpcodes
  o1LowerDloadPtrDiscipline o1PassContract o1SafeUpto unitShapeDefs unitTransformDefs dretDesugarDefs
  ptrDiscipline venomWf venomInst list arithmetic finite_map words

(* A protected actual write identifies its owner at the writer snapshot,
   even if the writing instruction executes in a descendant frame. *)
Theorem ptr_cut_actual_writer_seed:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  EVERY all_reachable C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  ptr_discipline_upto lo n C vs /\ gas_cut n vs a.po_state /\
  ptr_stage_placements C' positions /\
  ptr_structural_transcript R vs C Ct h a ht at done tokens registry births PT TG saved entries H /\
  w < LENGTH h /\ EL w H = (tsw,rw,bw,PTw,TGw,sw,ew) /\
  ~in_revert_forward (EL w h).po_fn (EL w h).po_state /\
  d <= LENGTH (EL w h).po_stack /\
  FLOOKUP (ptr_owner_view d (EL w h)).cf_state.vs_allocas aid = SOME (b,sz) /\
  b <= x /\ x < b+sz /\ lo <= x /\ x < dyn_floor C vs /\
  x IN range_bytes (step_writes (EL w h).po_inst (EL w h).po_state post) ==>
  ml_used_gen (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel (ptr_owner_view d (EL w h)).cf_fn)
      (cfg_analyze (ptr_owner_view d (EL w h)).cf_fn) (ptr_owner_view d (EL w h)).cf_fn)
    mems (ptr_owner_view d (EL w h)).cf_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  `gas_cut n vs (EL w h).po_state` by
    (drule_all ptr_chrono_history_cut >> simp[EVERY_EL]) >>
  `ptr_observation_reachable vs C (EL w h)` by
    (drule ptr_chrono_history_reachable >> simp[EVERY_EL]) >>
  fs[ptr_observation_reachable_def] >>
  drule_all ptr_discipline_upto_at >> strip_tac >>
  drule ptr_frame_context_membership >> strip_tac >>
  drule ptr_frame_operand_instructions >> strip_tac >>
  `(EL w h).po_inst.inst_opcode <> DRET /\ label_positions_ok (EL w h).po_inst` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def,
        no_dret_def, inst_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  qabbrev_tac `aw = EL w h` >>
  `!op. IS_SOME (eval_operand op aw.po_state) = IS_SOME (eval_operand op aw.po_state)` by simp[] >>
  drule_all ptr_ordinary_write_descriptor >>
  disch_then (qx_choose_then `ops` (qx_choose_then `sizeop`
    (qx_choose_then `off` (qx_choose_then `len` (map_every assume_tac o CONJUNCTS))))) >>
  `w2n off <= x /\ x < w2n off + w2n len` by
    (drule_all ptr_step_write_max_containment >> simp[]) >>
  `w2n len <> 0` by decide_tac >>
  unabbrev_all_tac >>
  drule_all ptr_historical_write_classification_upto >>
  disch_then (DISJ_CASES_THEN2 (map_every assume_tac o CONJUNCTS) strip_assume_tac)
  >- (`F` by decide_tac) >>
  `w <= w` by simp[] >>
  drule_all ptr_transcript_historical_placement_upto >>
  disch_then (qx_choose_then `e` strip_assume_tac) >>
  `vs.vs_allocas = FEMPTY` by fs[o1_initial_state_ok_def] >>
  drule_all ptr_frame_alloc_geometry >> strip_tac >>
  `db <= x /\ x < db+sb` by decide_tac >>
  `d = e /\ aid = bid` by
    (irule ptr_owner_overlap_unique >>
     qexistsl [`b`,`db`,`EL w h`,`sz`,`sb`,`x`] >> simp[]) >>
  gvs[] >>
  drule ptr_structural_transcript_ownership >>
  disch_then (qspec_then `w` mp_tac) >> simp[ptr_snapshot_ownership_def] >> strip_tac >>
  drule ptr_discipline_upto_fn_ptr_ok >> strip_tac >>
  `EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions` by
    (qpat_assum `o1_ctx_shape C` mp_tac >>
     simp[NoAsms, o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
     disch_then (mp_tac o cj 3) >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (qpat_assum `EVERY fn_inst_wf C.ctx_functions` mp_tac >>
     simp[NoAsms, EVERY_MEM, ptr_fn_inst_wf_flat]) >>
  irule ptr_source_owned_use_seed >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED
