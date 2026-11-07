Theory concretizeLayoutCanonicalRunNext
Ancestors concretizeLayoutCanonicalBlock concretizeLayoutCanonicalDriver
  concretizeLayoutCanonicalDeferred frameSelectedSimulation
  concretizeLayoutScopedPhase concretizeLayoutPhaseOrigin concretizeLayoutPairedEntry
  concretizeLayoutStagePairing concretizeLayoutBlockPairing concretizeMemLocDefs
  concretizeStepStructure passSimulationProofs
  passSharedDefs venomExecSemantics venomExecProofs venomWf venomInst list

Theorem layout_canonical_run_block_entry[local]:
  layout_canonical_run D lo vs0 C C' q0 es qs ass qend q n fn s fn' t /\
  EVERY wf_function C.ctx_functions /\
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
  rename1 `lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb'` >>
  fs[layout_canonical_run_def] >>
  rename1 `layout_driver_row C' fn fn' positions` >>
  `bb_well_formed bb` by
    (fs[EVERY_MEM, venomWfTheory.wf_function_def] >>
     fs[lookup_block_def] >> metis_tac[FIND_MEM]) >>
  fs[layout_driver_row_def] >>
  `s.vs_current_bb = t.vs_current_bb` by
    (fs[contextCodegenRelTheory.enters_block_def, frameControlAgreementTheory.control_agree_def] >>
     gvs[] >> imp_res_tac eval_phis_preserves_current_bb >> gvs[]) >>
  `layout_block_pair layout.cl_positions bb bb'
     (phi_prefix_length bb.bb_instructions)
     (phi_prefix_length bb'.bb_instructions)` by
    (irule layout_block_pair_phi_entry >> simp[] >>
     qpat_x_assum `lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb'` mp_tac >>
     fs[layout_stage_row_def, apply_context_concretize_layout_def,
        apply_concretize_layout_def] >>
     simp[concretize_positions_blocks, lookup_block_map_proof,
          concretize_positions_block_label] >>
     gvs[]) >>
  simp[layout_canonical_EB_def] >> qexists `INL b` >>
  simp[layout_canonical_block_witness_def] >>
  (conj_tac >- fs[layout_canonical_entry_def, layout_canonical_ready_def]) >>
  qexistsl [`fn`, `fn'`, `layout.cl_positions`] >>
  gvs[layout_canonical_entry_def, layout_canonical_ready_def,
      layout_scoped_phi_link_def, layout_phase_begins_def,
      layout_phase_origin_def, layout_paired_ordinary_def,
      layout_driver_row_def] >>
  imp_res_tac eval_phis_preserves_current_bb >> gvs[] >> metis_tac[]
QED

(* Leaf of the canonical simulation contract, run-next: a non-halted OK block ending in a terminator, followed by
   the OriginBlock edge and the rest of the run. *)
Theorem layout_canonical_run_next_certificate:
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
  selected_run_next_certificate C C' q0 path
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend)
Proof
  cheat
QED

val _ = export_theory();
