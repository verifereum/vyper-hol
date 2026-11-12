Theory o1LabelFlowMiddleSsa
Ancestors
  o1LabelFlowMiddleInsertion o1LabelFlowMiddleOwnership
  o1LabelFlowMiddleTraversal o1LabelFlowMiddleCleanup
  o1MakeSsaCallAssembly o1MakeSsaCalls o1MakeSsaRootedTree
  o1MakeSsaActualMaps makeSsaCurrentProps o1PassContract
  o1MakeSsaOwnership o1MakeSsaEventOwnership irSupply venomInst
  venomFnScheduleRunner venomWf list pred_set

Theorem prepared_rename_owner_init:
  ir_supply_covers_fn s f /\
  add_phi_nodes_supply s df pm li f.fn_blocks
    (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl f.fn_blocks) labels)))) = (bbs,s1) ==>
  current_rename_owner (set (fn_ir_vars f))
    {(v,v) | MEM v (fn_ir_vars f)} s1
    (init_current_rename_state (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl f.fn_blocks) labels)))))
Proof
  strip_tac >> irule current_rename_owner_init_function >>
  drule add_phi_nodes_supply_extends >> strip_tac >>
  irule ssa_vars_covered_mono >> goal_assum $ drule_at Any >>
  fs[ssa_vars_covered_def, ir_supply_covers_fn_def,
     list_subset_def, EVERY_MEM]
QED

Theorem prepared_visit_common_owner:
  add_phi_nodes_supply s df pm li f.fn_blocks
    (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl f.fn_blocks) labels)))) = (bbs,s1) /\
  ir_supply_covers_fn s f /\
  visit_blocks path s1
    (init_current_rename_state (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl f.fn_blocks) labels)))))
    bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\
  (!q. MEM q (dom_tree_postorder tree) ==> IS_SOME (lookup_block q bbs)) ==>
  ?H. current_name_owner (set (fn_ir_vars f)) H t /\
    (!e. MEM e events ==>
      current_stack_owner (set (fn_ir_vars f)) H (SND e.sve_in) /\
      current_stack_owner (set (fn_ir_vars f)) H (SND e.sve_out) /\
      LIST_REL (\i j. LIST_REL (\v n. (n,v) IN H)
        i.inst_outputs j.inst_outputs) e.sve_before e.sve_after)
Proof
  strip_tac >>
  `EVERY (\bb. EVERY (\i. set i.inst_outputs SUBSET set (fn_ir_vars f))
    bb.bb_instructions) bbs` by metis_tac[prepared_original_output_domain] >>
  `!e. MEM e events ==> IS_SOME (lookup_block e.sve_label bbs)` by
    (drule (cj 1 o1MakeSsaVisitRetentionTheory.retention_event_labels) >>
     strip_tac >> metis_tac[]) >>
  drule_all visit_events_output_domain >> strip_tac >>
  drule_all prepared_rename_owner_init >> strip_tac >>
  drule_all (cj 1 visit_common_rename_owner) >> strip_tac >>
  qexists `Hf` >> fs[current_rename_owner_def]
QED

Theorem inserted_function_wf:
  wf_function f /\ ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  set (MAP FST defs) SUBSET set (fn_ir_vars f) /\
  add_phi_nodes_supply s df pm li f.fn_blocks defs = (bbs,t) ==>
  wf_function (f with fn_blocks := bbs)
Proof
  strip_tac >>
  `ssa_vars_covered s (fn_ir_vars f) /\
   ssa_vars_covered s (MAP FST defs)` by
    (gvs[ssa_vars_covered_def, ir_supply_covers_fn_def,
         list_subset_def, EVERY_MEM, SUBSET_DEF] >> metis_tac[]) >>
  drule add_phi_nodes_supply_ok >>
  disch_then (qspecl_then [`defs`,`df`,`pm`,`li`,`f.fn_blocks`,`bbs`,`t`] mp_tac) >>
  (impl_tac >- (gvs[wf_function_def, fn_labels_def, fn_ir_vars_def,
    fn_inst_ids_distinct_def, fn_ir_inst_ids_def, block_ir_inst_ids_def,
    ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >>
    fs[lambdify block_ir_inst_ids_def])) >> strip_tac >>
  `EVERY bb_well_formed bbs` by
    (irule o1MakeSsaFrontierTheory.add_phi_nodes_supply_well_formed >>
     goal_assum $ drule_at Any >> fs[wf_function_def, EVERY_MEM]) >>
  `MAP (\b. (b.bb_label,bb_succs b)) bbs =
   MAP (\b. (b.bb_label,bb_succs b)) f.fn_blocks` by
    metis_tac[o1MakeSsaCfgTheory.add_phi_nodes_supply_cfg] >>
  gvs[wf_function_def, fn_labels_def, fn_has_entry_def,
      fn_inst_ids_distinct_def, ssa_ids_supply_ok_def,
      lambdify block_ir_inst_ids_def, EVERY_MEM] >>
  conj_tac >- (Cases_on `bbs` >> gvs[]) >>
  simp[fn_succs_closed_def] >> rpt strip_tac >>
  `MEM (bb.bb_label,bb_succs bb)
     (MAP (\b. (b.bb_label,bb_succs b)) f.fn_blocks)` by
    (qpat_x_assum `block_succs_map bbs = _` (SUBST1_TAC o SYM) >>
     simp[MEM_MAP] >> qexists `bb` >> simp[]) >>
  fs[MEM_MAP, fn_succs_closed_def, fn_labels_def] >> metis_tac[]
QED
