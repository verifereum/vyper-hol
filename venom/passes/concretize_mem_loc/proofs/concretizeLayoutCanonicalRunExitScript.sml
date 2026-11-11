Theory concretizeLayoutCanonicalRunExit
Ancestors concretizeLayoutCanonicalBlock concretizeLayoutCanonicalDriver
  concretizeLayoutCanonicalDeferred frameSelectedSimulation
  concretizeLayoutStagePairing concretizeLayoutScopedPhase
  concretizeLayoutPhaseOrigin concretizeLayoutPairedEntry

Theorem layout_run_exit_phi_entry[local]:
  EVERY wf_function C.ctx_functions /\
  layout_canonical_run D lo vs0 C C' q0 es qs ass qend q n fn s fn' t /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK phi /\
  decoration_entry fn (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) q ==>
  ?bb' phi'. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    eval_phis t bb'.bb_instructions = OK phi' /\
    layout_canonical_EB D lo vs0 C C' q0 es qs ass qend q n bb
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) bb'
      (phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
Proof
  strip_tac >> drule layout_canonical_run_phi >>
  disch_then (qspec_then `ARB` strip_assume_tac) >> gvs[] >>
  rename1 `eval_phis t bb'.bb_instructions = OK phi'` >>
  qpat_x_assum `layout_canonical_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_canonical_run_def] >> strip_tac >>
  `wf_function fn` by metis_tac[listTheory.EVERY_MEM] >>
  `MEM bb fn.fn_blocks` by metis_tac[phiTransformTheory.lookup_block_MEM] >>
  `bb_well_formed bb` by fs[venomWfTheory.wf_function_def] >>
  `phi.vs_current_bb = s.vs_current_bb /\
   phi'.vs_current_bb = t.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  `s.vs_current_bb = t.vs_current_bb` by
    fs[layout_canonical_entry_def,
       concretizeLayoutAlignedControlTheory.layout_aligned_entry_def,
       frameControlAgreementTheory.control_agree_def] >>
  `bb' = clear_nops_block (block_map_transform
    (concretize_inst_with_positions positions) bb)` by
    (fs[layout_driver_row_def, layout_stage_row_def,
        concretizeMemLocDefsTheory.apply_context_concretize_layout_def,
        concretizeMemLocDefsTheory.apply_concretize_layout_def] >>
     qpat_x_assum `lookup_block t.vs_current_bb _ = SOME bb'` mp_tac >>
     asm_rewrite_tac[] >>
     simp[concretizeStepStructureTheory.concretize_positions_blocks,
          passSimulationProofsTheory.lookup_block_map_proof,
          concretizeStepStructureTheory.concretize_positions_block_label]) >>
  fs[layout_canonical_entry_def, layout_canonical_ready_def,
     layout_scoped_phi_link_def, layout_phase_begins_def, layout_phase_origin_def] >>
  simp[layout_canonical_EB_def] >> qexists `INL b` >>
  simp[layout_canonical_block_witness_def] >>
  qexistsl [`fn`, `fn'`, `positions`] >> simp[] >>
  irule layout_paired_ordinary_initialize >> simp[] >> metis_tac[]
QED

(* Leaf of the canonical simulation contract, run-exit: a block whose
   result is not OK. *)
Theorem layout_canonical_run_exit_certificate:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  dead_wf D /\ taint_within D C vs0 /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  joint_trace vs0 C q0 es qs qend ==>
  selected_run_exit_certificate C C' q0 path
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend)
Proof
  strip_tac >> rewrite_tac[selected_run_exit_certificate_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all layout_run_exit_phi_entry >> strip_tac >>
  qexistsl [`bb'`, `phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions`] >>
  simp[] >> rpt strip_tac >>
  `layout_canonical_result D lo vs0 C C' q0 es qs ass qend qe
    (n + LENGTH w) r rb'` by
    (Cases_on `r` >> Cases_on `rb'` >> gvs[layout_canonical_OB_def]) >>
  `!p. rb' <> OK p` by
    (Cases_on `r` >> Cases_on `rb'` >> gvs[layout_canonical_result_def]) >>
  simp[selected_run_match_def, layout_canonical_OutR_def] >>
  qexists `rb'` >> simp[] >>
  gvs[frameFiniteExecutionTheory.finite_step_run_exit]
QED

val _ = export_theory();
