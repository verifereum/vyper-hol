Theory concretizePtrDallocaStageCoverage
Ancestors
  concretizePtrStagePairedBridge concretizePtrHistoryCoverage
  concretizePtrUniversalExtension concretizePtrPairedPrefix
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrPairedFields
  o1PassContract unitTransformDefs list

(* Coverage keeps the forwarding window as a separate alternative: its
   instructions need not have a continuing paired source execution. *)
Theorem ptr_dalloca_stage_history_coverage:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  (!eom. max_live_eom C' = SOME eom ==> eom <= w2n vs.vs_initial_fmp) /\
  max_live_eom C' = SOME eom ==>
  ?R lp positions.
    ptr_stage_placements C' positions /\
    !ht at. ptr_chrono_history vs C' ht at ==>
      (?h a done tokens registry births PT TG saved entries H calls ws.
        ptr_paired_prefix R lp positions lo vs C C'
          h a ht at done tokens registry births PT TG saved entries H calls ws /\
        a.po_inst.inst_opcode <> NOP /\
        at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst) \/
      (?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
        revert_forward_pair bb i j /\
        i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j)
Proof
  strip_tac >>
  `(ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp)` by simp[] >>
  drule ptr_stage_paired_bridge >>
  disch_then (qspecl_then [`vs`, `lo`, `eom`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qexistsl_tac [`R`, `lp`, `positions`] >> simp[] >>
  rpt gen_tac >> disch_tac >>
  irule ptr_paired_history_coverage >>
  `C.ctx_entry = C'.ctx_entry` by fs[ctx_pass_stage_def] >>
  `vs.vs_vars = FEMPTY` by
    fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all ptr_paired_universal_extension >> simp[]) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem ptr_dalloca_stage_frame_coverage:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  (!eom. max_live_eom C' = SOME eom ==> eom <= w2n vs.vs_initial_fmp) /\
  max_live_eom C' = SOME eom ==>
  ?R lp positions.
    ptr_stage_placements C' positions /\
    !stk PG G tn fn inst s.
      frame_reachable vs C' stk PG G tn fn inst s ==>
      (?h a ht done tokens registry births PT TG saved entries H calls ws.
        ptr_paired_prefix R lp positions lo vs C C'
          h a ht (ptr_observe stk PG G tn fn inst s)
          done tokens registry births PT TG saved entries H calls ws /\
        ptr_observation_reachable vs C a /\
        ptr_paired_code R lp positions a.po_fn fn /\
        ptr_paired_cursor lp a (ptr_observe stk PG G tn fn inst s) /\
        a.po_inst.inst_opcode <> NOP /\
        inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst) \/
      (?bb i j. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        revert_forward_pair bb i j /\ i < s.vs_inst_idx /\ s.vs_inst_idx <= j)
Proof
  strip_tac >> drule ptr_dalloca_stage_history_coverage >>
  disch_then (qspecl_then [`vs`, `lo`, `eom`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qexistsl_tac [`R`, `lp`, `positions`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule ptr_reachable_has_chrono_history >> strip_tac >>
  qpat_x_assum `!ht at. ptr_chrono_history _ _ _ _ ==> _`
    (drule_then strip_assume_tac)
  >- (disj1_tac >>
      drule ptr_paired_prefix_endpoint >> strip_tac >>
      drule ptr_paired_prefix_transcript >> strip_tac >>
      drule ptr_structural_transcript_erasure >> strip_tac >>
      drule ptr_structural_trace_source >> strip_tac >>
      drule ptr_chrono_history_reachable >> strip_tac >>
      gvs[ptr_observe_def] >>
      rpt (goal_assum (drule_at Any)) >> simp[]) >>
  disj2_tac >> fs[ptr_observe_def] >> metis_tac[]
QED
