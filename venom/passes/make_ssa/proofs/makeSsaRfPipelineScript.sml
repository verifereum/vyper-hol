Theory makeSsaRfPipeline
Ancestors makeSsaRfFinalBlock makeSsaRfLocalBridge makeSsaRfDomDistinct
  makeSsaRfTreeTrace makeSsaRfWitness makeSsaCurrentDefs makeSsaRfEdgeShape
  makeSsaRfShape makeSsaRfTransport makeSsaRfAnnotations makeSsaRfAllocation
  makeSsaHelper makeSsaCurrentProps makeSsaRfAssign makeSsaRfRenameTrace list pair

Theorem current_event_rf_trace:
  current_event_valid A V ev /\ current_event_trace A finalH ev /\
  EVERY (\i. EVERY (rf_operand_in V) i.inst_operands)
    (current_event_input_block ev).bb_instructions ==>
  ?f g. rf_back_trace V f g
    (REVERSE (current_event_input_block ev).bb_instructions)
    (REVERSE (current_event_renamed_block ev).bb_instructions)
Proof
  PairCases_on `ev` >>
  simp[current_event_valid_def, current_event_trace_def,
    current_event_input_block_def, current_event_renamed_block_def] >>
  strip_tac >>
  qexistsl_tac [`latest_current_name (ev3,ev4)`,
    `latest_current_name (ev9,ev10)`] >>
  irule current_local_trace_rf_back_trace >> metis_tac[]
QED


Theorem rf_init_counter:
  !vars v. current_counter
    (MAP (\w. (w,0n)) vars, MAP (\w. (w,[w])) vars) v = 0
Proof
  Induct >> simp[current_counter_def, alistTheory.ALOOKUP_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[current_counter_def]
QED

Theorem rf_init_latest:
  !vars v. latest_current_name
    (MAP (\w. (w,0n)) vars, MAP (\w. (w,[w])) vars) v = v
Proof
  Induct >> simp[latest_current_name_def, alistTheory.ALOOKUP_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[latest_current_name_def]
QED

Theorem rf_init_allocation:
  ssa_vars_covered s V /\ ssa_vars_covered s (MAP FST defs) ==>
  current_allocation_consistent V [] s (init_current_rename_state defs) /\
  current_env_realizes [] CurrentDefault (init_current_rename_state defs) V
Proof
  simp[current_allocation_consistent_def, current_history_valid_def,
    current_owner_count_def, init_current_rename_state_def, rf_init_counter,
    current_env_realizes_def, current_token_name_def, rf_init_latest,
    ssa_stacks_covered_def, EVERY_MAP, ssa_vars_covered_def, EVERY_MEM,
    MEM_MAP] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem rf_initial_tree_events_valid:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  (!v. MEM v (FLAT (MAP block_ir_vars bbs)) ==> MEM v V) /\
  ssa_vars_covered s V /\ ssa_vars_covered s (MAP FST defs) /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  current_tree_trace (current_annotation_map bbs (rf_block_annotations bbs))
    sm tree s (init_current_rename_state defs) bbs [] CurrentDefault []
    ctrs' s' bbs' H' visited' events ==>
  EVERY (current_event_valid
    (current_annotation_map bbs (rf_block_annotations bbs)) V) events
Proof
  strip_tac >>
  `current_pending_annotations V
    (current_annotation_map bbs (rf_block_annotations bbs)) [] []` by
    metis_tac[rf_block_annotation_map_pending] >>
  `current_annotation_separation
    (current_annotation_map bbs (rf_block_annotations bbs))` by
    metis_tac[rf_block_annotation_map_separation] >>
  drule (cj 1 current_tree_trace_events_valid) >> simp[] >>
  disch_then (qspec_then `V` mp_tac) >>
  simp[current_env_owned_initial] >> metis_tac[rf_init_allocation]
QED

Theorem rf_local_step_source_shape:
  rf_copy_shape old input /\ rf_local_step V f g input output ==>
  rf_local_step V f g old output
Proof
  simp[rf_copy_shape_def, rf_local_step_def] >> metis_tac[]
QED

Theorem current_local_trace_source_rf:
  !annss inputs s rs H E outputs s' rs' H' E' originals.
  current_local_trace annss inputs s rs H E outputs s' rs' H' E' /\
  LIST_REL rf_copy_shape originals inputs /\
  current_annotations_ok V H (FLAT annss) /\
  current_allocation_consistent V H s rs /\ current_env_realizes H E rs V /\
  current_env_owned V H E /\
  EVERY (\i. EVERY (rf_operand_in V) i.inst_operands) originals ==>
  rf_back_trace V (latest_current_name rs) (latest_current_name rs')
    (REVERSE originals) (REVERSE outputs)
Proof
  Induct >> simp[current_local_trace_def, rf_back_trace_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `rf_copy_shape orig inst` >>
  rename1 `LIST_REL rf_copy_shape origs rest` >>
  `current_annotations_ok V H h` by
    metis_tac[current_annotations_split, FLAT] >>
  `current_allocation_consistent V H1 s1 rs1 /\ current_env_realizes H1 E1 rs1 V` by
    (irule current_inst_trace_preserves >> metis_tac[]) >>
  `current_env_owned V H1 E1` by metis_tac[current_inst_trace_owned] >>
  `current_annotations_ok V H1 (FLAT annss)` by
    (fs[current_inst_trace_def] >>
     irule current_outputs_trace_remaining >> metis_tac[FLAT]) >>
  `rf_back_trace V (latest_current_name rs1) (latest_current_name rs')
     (REVERSE origs) (REVERSE rest1)` by
    (first_x_assum irule >> metis_tac[]) >>
  `rf_local_step V (latest_current_name rs) (latest_current_name rs1) inst inst1` by
    (irule current_inst_trace_rf_step >> metis_tac[]) >>
  `rf_local_step V (latest_current_name rs) (latest_current_name rs1) orig inst1` by
    metis_tac[rf_local_step_source_shape] >>
  simp[REVERSE_DEF] >> irule rf_back_trace_append >>
  qexists_tac `latest_current_name rs1` >>
  simp[rf_back_trace_def] >> metis_tac[]
QED

Theorem current_event_source_rf_trace:
  current_event_valid A V ev /\ current_event_trace A finalH ev /\
  current_edge_shape old (current_event_input_block ev) /\
  EVERY (\i. EVERY (rf_operand_in V) i.inst_operands) old.bb_instructions ==>
  ?f g. rf_back_trace V f g (REVERSE old.bb_instructions)
    (REVERSE (current_event_renamed_block ev).bb_instructions)
Proof
  strip_tac >> drule current_edge_shape_copy_shape >> strip_tac >>
  PairCases_on `ev` >>
  gvs[current_event_valid_def, current_event_trace_def,
    current_event_input_block_def, current_event_renamed_block_def] >>
  qexistsl_tac [`latest_current_name (ev3,ev4)`,
    `latest_current_name (ev9,ev10)`] >>
  irule current_local_trace_source_rf >> metis_tac[]
QED

Theorem rf_map_operand_identity[simp]:
  rf_map_operand I op = op
Proof
  Cases_on `op` >> simp[rf_map_operand_def]
QED

Theorem rf_local_step_identity:
  rf_local_step V I I inst inst
Proof
  `rf_map_operand I = I` by simp[FUN_EQ_THM] >>
  simp[rf_local_step_def, MAP_ID]
QED

Theorem rf_back_trace_identity:
  !insts. EVERY (\i. EVERY (rf_operand_in V) i.inst_operands) insts ==>
  rf_back_trace V I I (REVERSE insts) (REVERSE insts)
Proof
  Induct >> simp[rf_back_trace_def] >> rpt strip_tac >>
  irule rf_back_trace_append >> qexists_tac `I` >>
  simp[rf_back_trace_def, rf_local_step_identity]
QED

Theorem rf_trace_final_block_boundary:
  current_tree_trace A sm tree s rs bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  EVERY (current_event_valid A V) events /\
  EVERY (current_event_names H' V) events /\
  lookup_block q bbs = SOME old /\ lookup_block q bbs' = SOME final /\
  EVERY (\i. EVERY (rf_operand_in V) i.inst_operands) old.bb_instructions ==>
  ?renamed f g.
    rf_back_trace V f g (REVERSE old.bb_instructions)
      (REVERSE renamed.bb_instructions) /\
    LIST_REL rf_copy_shape renamed.bb_instructions final.bb_instructions
Proof
  strip_tac >> drule_all current_trace_final_block >> strip_tac
  >- (qexistsl_tac [`old`, `I`, `I`] >> conj_tac
      >- (irule rf_back_trace_identity >> fs[EVERY_MEM] >> metis_tac[]) >>
      metis_tac[current_edge_shape_copy_shape]) >>
  `current_event_valid A V ev` by fs[EVERY_MEM] >>
  `?f g. rf_back_trace V f g (REVERSE old.bb_instructions)
     (REVERSE (current_event_renamed_block ev).bb_instructions)` by
    (irule current_event_source_rf_trace >> metis_tac[]) >>
  qexistsl_tac [`current_event_renamed_block ev`, `f`, `g`] >>
  metis_tac[current_edge_shape_copy_shape]
QED

Theorem rf_rename_run_block_boundary:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  (!v. MEM v (FLAT (MAP block_ir_vars bbs)) ==> MEM v V) /\
  ssa_vars_covered s V /\ ssa_vars_covered s (MAP FST defs) /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  rename_current_blocks s (init_current_rename_state defs) bbs sm tree =
    (ctrs',s',bbs') /\
  lookup_block q bbs = SOME old /\ lookup_block q bbs' = SOME final /\
  EVERY (\i. EVERY (rf_operand_in V) i.inst_operands) old.bb_instructions ==>
  ?renamed f g.
    rf_back_trace V f g (REVERSE old.bb_instructions)
      (REVERSE renamed.bb_instructions) /\
    LIST_REL rf_copy_shape renamed.bb_instructions final.bb_instructions
Proof
  strip_tac >>
  `current_unvisited_annotations
    (current_annotation_map bbs (rf_block_annotations bbs)) [] bbs` by
    simp[rf_block_annotation_map_initial] >>
  `?ctrs1 s1 bbs1 H' visited' events.
    current_tree_trace (current_annotation_map bbs (rf_block_annotations bbs))
      sm tree s (init_current_rename_state defs) bbs [] CurrentDefault []
      ctrs1 s1 bbs1 H' visited' events` by
    (irule (cj 1 current_tree_trace_exists) >> simp[]) >>
  drule (cj 1 current_tree_trace_projection) >> strip_tac >> gvs[] >>
  `EVERY (current_event_valid
      (current_annotation_map bbs (rf_block_annotations bbs)) V) events` by
    (irule rf_initial_tree_events_valid >> metis_tac[]) >>
  `current_allocation_consistent V [] s (init_current_rename_state defs) /\
   current_env_realizes ([] : (current_token # string # string) list)
     CurrentDefault (init_current_rename_state defs) V` by
    metis_tac[rf_init_allocation] >>
  `current_annotations_ok V ([] : (current_token # string # string) list)
     (FLAT (FLAT (rf_block_annotations bbs)))` by
    metis_tac[rf_block_annotations_ok] >>
  `EVERY (current_event_names H' V) events` by
    (drule_at (Pat `current_tree_trace _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       current_annotated_tree_names >>
     simp[current_env_owned_initial] >>
     disch_then (qspec_then `V` mp_tac) >>
     fs[rf_block_annotations_def]) >>
  irule rf_trace_final_block_boundary >> metis_tac[]
QED

Theorem rf_rename_cleanup_phase_certificate:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  (!v. MEM v (FLAT (MAP block_ir_vars bbs)) ==> MEM v V) /\
  ssa_vars_covered s V /\ ssa_vars_covered s (MAP FST defs) /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  rename_current_blocks s (init_current_rename_state defs) bbs sm tree =
    (ctrs',s',bbs') /\
  lookup_block q bbs = SOME inserted /\
  inserted.bb_instructions = pre ++ bb.bb_instructions /\
  EVERY inst_wf inserted.bb_instructions /\
  EVERY (\i. EVERY (rf_operand_in V) i.inst_operands) inserted.bb_instructions /\
  lookup_block q (simplify_current_phis_if enabled bbs') = SOME final ==>
  rf_phase_certificate V bb final (LENGTH pre)
Proof
  strip_tac >>
  Cases_on `lookup_block q bbs'` >> gvs[current_cleanup_if_lookup] >>
  rename1 `lookup_block q bbs' = SOME edged` >>
  `?renamed f g.
    rf_back_trace V f g (REVERSE inserted.bb_instructions)
      (REVERSE renamed.bb_instructions) /\
    LIST_REL rf_copy_shape renamed.bb_instructions edged.bb_instructions` by
    (irule rf_rename_run_block_boundary >> simp[] >> metis_tac[]) >>
  simp[rf_phase_certificate_def] >>
  qexistsl_tac [`pre`, `renamed`, `edged`, `f`, `g`, `enabled`] >> gvs[]
QED

Theorem rf_build_phi_inst_supply_wf:
  inst_wf (build_phi_inst_supply id v ps)
Proof
  simp[build_phi_inst_supply_def, venomWfTheory.inst_wf_def] >>
  Induct_on `ps` >> simp[venomWfTheory.phi_well_formed_def]
QED

Theorem rf_process_frontiers_supply_wf:
  !fs s v pm li bbs rest hp bbs' rest' hp' s'.
  process_frontiers_supply s v pm li bbs rest hp fs = (bbs',rest',hp',s') /\
  EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs'
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  pop_assum $ mk_asm "ih" >>
  simp[process_frontiers_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[]
  >- (rpt strip_tac >> asm "ih" drule_all >> simp[]) >>
  IF_CASES_TAC >> gvs[]
  >- (rpt strip_tac >> asm "ih" drule_all >> simp[]) >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `process_frontiers_supply _ _ _ _ next _ _ _` >>
  `EVERY (\bb. EVERY inst_wf bb.bb_instructions) next` by
    (simp[Abbr `next`, EVERY_MAP, makeSsaDefsTheory.insert_phi_at_block_def,
      EVERY_MEM] >> rpt strip_tac >> Cases_on `bb.bb_label = h` >>
     gvs[rf_build_phi_inst_supply_wf, EVERY_MEM] >> metis_tac[]) >>
  asm "ih" drule_all >> simp[]
QED

Theorem rf_insert_phis_for_var_supply_wf:
  !s v df pm li bbs work hp bbs' s'.
  insert_phis_for_var_supply s v df pm li bbs work hp = (bbs',s') /\
  EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs'
Proof
  recInduct insert_phis_for_var_supply_ind >>
  rw[insert_phis_for_var_supply_def] >> gvs[] >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >>
  first_x_assum irule >> simp[] >>
  irule rf_process_frontiers_supply_wf >> metis_tac[]
QED

Theorem rf_add_phi_nodes_supply_wf:
  !defs s df pm li bbs bbs' s'.
  add_phi_nodes_supply s df pm li bbs defs = (bbs',s') /\
  EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs'
Proof
  Induct >- simp[add_phi_nodes_supply_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[add_phi_nodes_supply_def] >> pairarg_tac >> gvs[] >> strip_tac >>
  `EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs''` by
    (irule rf_insert_phis_for_var_supply_wf >> metis_tac[]) >>
  first_x_assum drule_all >> simp[]
QED
