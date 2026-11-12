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
