Theory concretizeLayoutCanonicalRunHalt
Ancestors concretizeLayoutCanonicalBlock concretizeLayoutCanonicalDriver
  concretizeLayoutCanonicalDeferred frameSelectedSimulation
  concretizeLayoutPhaseOrigin concretizeLayoutCanonicalIndex
  concretizeLayoutAlignedControl frameControlAgreement
  concretizeLayoutStagePairing concretizeLayoutPairedEntry
  concretizeLayoutScopedPhase concretizeLayoutBlockPairing
  frameJointTrace frameAllocationOwnership frameOriginReachable
  frameOriginHistory o1PassContract venomWf venomExecProofs
  o1ScheduleDecompHelpers frameFiniteJointDecoration frameJointTransition
  list arithmetic venomInst concretizeLayoutCompletedJump

Theorem canonical_entry_retarget[local]:
  layout_canonical_entry D lo vs0 C C' q0 es qs ass qend q n (INL b) p u ==>
  layout_canonical_entry D lo vs0 C C' q0 es qs ass qend q n
    (INL (b with lop_origin := (b.lop_origin with lbo_target := target)))
    p (u with vs_inst_idx := k)
Proof
  simp[layout_canonical_entry_def, layout_canonical_ready_def,
    layout_driver_indexed_def, layout_phase_canonical_def,
    layout_aligned_entry_def, layout_ordinary_entry_def,
    layout_ordinary_trace_def] >>
  strip_tac >>
  drule layout_ordinary_state_target_index >>
  disch_then (qspec_then `k` assume_tac) >>
  gvs[layout_ordinary_state_def, control_agree_def]
QED

Theorem canonical_entry_function_member[local]:
  layout_canonical_entry D lo vs0 C C' q0 es qs ass qend q n (INL b) p u /\
  decoration_entry fn p q /\ ~ctx_has_dalloca C ==>
  MEM fn C.ctx_functions
Proof
  simp[layout_canonical_entry_def, layout_canonical_ready_def,
    layout_ordinary_trace_def] >> strip_tac >>
  `joint_config_reachable vs0 C q` by
    (drule joint_trace_prefix_reachable >>
     pure_rewrite_tac[EVERY_EL] >>
     disch_then (qspec_then `b.lop_cursor` mp_tac) >> fs[]) >>
  Cases_on `q` >> gvs[decoration_entry_def, decoration_at_def] >>
  rename1 `joint_config_reachable vs0 C
    (JointConfig stk PG G tn fn inst p oms om hs hist)` >>
  `frame_reachable vs0 C stk PG G tn fn inst p` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  metis_tac[frame_allocation_ownership]
QED

(* Leaf of the canonical simulation contract, run-halt: a block that ends
   OK with the state halted. *)
Theorem layout_canonical_run_halt_certificate:
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
  selected_run_halt_certificate C C' q0 path
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend)
Proof
  strip_tac >> simp[selected_run_halt_certificate_def] >> rpt strip_tac >>
  drule layout_canonical_run_phi >>
  disch_then (qspec_then `ARB` strip_assume_tac) >> gvs[] >>
  drule_all canonical_entry_function_member >> strip_tac >>
  `lookup_function fn.fn_name C.ctx_functions = SOME fn /\
   fn.fn_eom = NONE /\ wf_function fn` by
    (fs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def, EVERY_MEM] >>
     metis_tac[lookup_function_member_iff]) >>
  drule_all layout_stage_row_produce >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb_well_formed bb` by
    (fs[wf_function_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
  drule_all layout_stage_row_block_pair >> strip_tac >>
  rename1 `layout_block_pair layout.cl_positions bb actual _ _` >>
  drule canonical_entry_retarget >>
  disch_then (qspecl_then [`actual`, `phi_prefix_length actual.bb_instructions`]
    assume_tac) >>
  `layout_driver_row C' fn out layout.cl_positions` by
    (simp[layout_driver_row_def] >> metis_tac[]) >>
  `lookup_block phi.vs_current_bb fn.fn_blocks = SOME bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  qmatch_asmsub_abbrev_tac `INL phase` >>
  `layout_canonical_block_witness D lo vs0 C C' q0 (MAP FST path)
    (MAP SND path) ass qend q n bb
    (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    actual (phi'' with vs_inst_idx := phi_prefix_length actual.bb_instructions)
    (INL phase)` by
    (simp[layout_canonical_block_witness_def] >>
     fs[layout_canonical_entry_def, layout_canonical_ready_def] >>
     qexistsl [`fn`, `out`, `layout.cl_positions`] >>
     simp[layout_paired_ordinary_def] >>
     fs[Abbr `phase`, layout_scoped_phi_link_def, layout_phase_begins_def,
        layout_phase_origin_def]) >>
  qexistsl [`actual`, `phi'' with vs_inst_idx := phi_prefix_length actual.bb_instructions`] >>
  conj_tac >- (simp[layout_canonical_EB_def] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `rb'` >>
  gvs[layout_canonical_OB_def, layout_canonical_result_def] >>
  first_x_assum drule >> strip_tac >>
  fs[layout_completed_jump_def]
QED

val _ = export_theory();
