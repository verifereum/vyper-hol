Theory concretizeLayoutCanonicalRunNext
Ancestors concretizeLayoutCanonicalBlock concretizeLayoutCanonicalDriver
  concretizeLayoutCanonicalDeferred frameSelectedSimulation
  concretizeLayoutScopedPhase concretizeLayoutPhaseOrigin concretizeLayoutPairedEntry
  concretizeLayoutStagePairing concretizeLayoutBlockPairing concretizeMemLocDefs
  concretizeStepStructure passSimulationProofs concretizeLayoutCompletedJump
  concretizeLayoutRunState frameControlAgreement frameJointTransition
  frameResolvedCoherent concretizeLayoutCanonicalIndex frameSelectedDecoration
  arithmetic frameFiniteExecution unitShapeDefs
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

Theorem layout_canonical_jump_continue[local]:
  layout_completed_jump D lo vs0 C C' q0 es qs qend a inst j s t post tpost /\
  layout_driver_indexed es ass a /\ vs0.vs_allocas = FEMPTY /\
  MEM fn C.ctx_functions /\ layout_driver_row C' fn fn' positions /\
  a.lop_config = JointConfig stk PG G tn fn ci s oms om hs h /\
  a.lop_ids = birth::ids /\ a.lop_anns = (rp,rv)::saved /\
  a.lop_cursor < LENGTH es /\
  EL a.lop_cursor es = SOME (OriginBlock fuel post) /\
  EL (SUC a.lop_cursor) (q0::qs) =
    JointConfig stk PG G' tn' fn inst' sentry oms om' hs h' /\
  joint_transition C (JointConfig stk PG G tn fn ci s oms om hs h)
    (SOME (OriginBlock fuel post))
    (JointConfig stk PG G' tn' fn inst' sentry oms om' hs h') /\
  resolved_annotation_edge C a.lop_cursor a.lop_config (EL a.lop_cursor es)
    (EL (SUC a.lop_cursor) (q0::qs)) a.lop_ids a.lop_anns
    (EL (SUC a.lop_cursor) (lifetime_annotations 0 [0] es))
    (EL (SUC a.lop_cursor) ass) /\
  EVERY bb_well_formed fn.fn_blocks /\
  (!bb. MEM bb fn.fn_blocks ==>
    EVERY (\i. MEM i (fn_insts fn)) bb.bb_instructions) /\
  control_agree post tpost ==>
  layout_canonical_run D lo vs0 C C' q0 es qs ass qend
    (JointConfig stk PG G' tn' fn inst' sentry oms om' hs h')
    (SUC a.lop_cursor) fn post fn' tpost
Proof
  strip_tac >> drule layout_completed_jump_local >> strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs qend a s` by
    fs[layout_completed_jump_def, layout_ordinary_entry_def] >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_jump_view_def, layout_ordinary_state_def] >> strip_tac >>
  fs[control_agree_def] >>
  drule_all (SRULE[] layout_run_block_state) >>
  disch_then (qspec_then `positions` strip_assume_tac) >>
  `enters_block fn post sentry` by
    (fs[joint_transition_block_iff] >> metis_tac[]) >>
  `enters_block fn' tpost tentry` by
    (fs[layout_driver_row_def, layout_stage_row_def,
        apply_context_concretize_layout_def, apply_concretize_layout_def,
        contextCodegenRelTheory.enters_block_def] >> gvs[] >> metis_tac[]) >>
  `layout_driver_indexed es ass b` by
    (fs[layout_driver_indexed_def, resolved_annotation_edge_def,
        layout_phase_canonical_def, frameActivationLifetimeTheory.lifetime_step_def] >>
     qpat_x_assum `resolved_annotation_update _ _ _ _ _` mp_tac >>
     simp[Once resolved_annotation_update_cases] >> strip_tac >> gvs[]) >>
  `control_agree sentry tentry` by
    (fs[contextCodegenRelTheory.enters_block_def, control_agree_def] >>
     gvs[] >> imp_res_tac eval_phis_preserves_current_bb >>
     imp_res_tac eval_phis_only_updates_vs_vars >>
     fs[venomStateTheory.venom_state_component_equality]) >>
  irule layout_canonical_run_intro >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
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
  strip_tac >> simp[selected_run_next_certificate_def] >> rpt gen_tac >> strip_tac >>
  drule_all layout_canonical_run_block_entry >> strip_tac >>
  qexistsl [`bb'`, `phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions`] >>
  simp[] >> gen_tac >> strip_tac >>
  Cases_on `rb'` >> gvs[layout_canonical_OB_def, layout_canonical_result_def] >>
  qpat_x_assum `layout_canonical_EB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_canonical_EB_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE[APPEND_ASSOC, ADD_ASSOC]) >>
  drule_all (PURE_REWRITE_RULE[APPEND_ASSOC, ADD_ASSOC]
    selected_run_next_children) >> strip_tac >>
  `?birth ids rp rv saved. b.lop_ids = birth::ids /\ b.lop_anns = (rp,rv)::saved` by
    (fs[layout_completed_jump_def, layout_ordinary_entry_def, layout_ordinary_state_def] >>
     gvs[]) >>
  `u = si` by
    (fs[layout_completed_jump_def, layout_ordinary_entry_def, layout_ordinary_state_def,
        layout_phase_normalize_def] >> gvs[]) >> gvs[] >>
  `MEM fn C.ctx_functions /\ ?positions. layout_driver_row C' fn fn' positions` by
    (fs[layout_canonical_run_def] >> metis_tac[]) >>
  `EVERY bb_well_formed fn.fn_blocks /\
   (!bb. MEM bb fn.fn_blocks ==> EVERY (\i. MEM i (fn_insts fn)) bb.bb_instructions)` by
    (fs[EVERY_MEM, venomWfTheory.wf_function_def, fn_insts_def] >>
     conj_tac >- metis_tac[] >>
     metis_tac[MEM_fn_insts_blocks]) >>
  qpat_x_assum `!k. k < LENGTH path ==> _`
    (qspec_then `n + LENGTH wb` mp_tac) >> simp[] >> strip_tac >>
  fs[joint_transition_block_iff] >> gvs[] >>
  qexists `v` >> conj_tac >- (
    `n + (LENGTH wb + 1) = SUC b.lop_cursor` by simp[] >>
    pop_assum (fn th => once_rewrite_tac[th]) >>
    irule layout_canonical_jump_continue >>
    goal_assum (drule_at Any) >> simp[] >>
    fs[layout_driver_indexed_def, layout_phase_canonical_def] >>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE[GSYM ADD_ASSOC, GSYM ADD1]) >>
    pure_rewrite_tac[GSYM ADD_ASSOC, GSYM ADD1] >>
    fs[ADD_CLAUSES, joint_transition_block_iff] >>
    `FST (EL (n + LENGTH wb) path) = SOME (OriginBlock fuel post)` by
      metis_tac[EL_MAP] >> metis_tac[]) >>
  gen_tac >> strip_tac >>
  simp[selected_run_match_def, layout_canonical_OutR_def] >>
  qexists `rr'` >> conj_tac
  >- (irule finite_step_run_next >> goal_assum (drule_at Any) >>
      metis_tac[frameFiniteControlTheory.finite_execution_block_endpoint]) >>
  qpat_x_assum `layout_canonical_OutR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[layout_canonical_OutR_def, LENGTH_APPEND, LENGTH, ADD_ASSOC] >>
  simp[]
QED

val _ = export_theory();
