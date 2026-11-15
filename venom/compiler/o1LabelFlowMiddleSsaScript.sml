Theory o1LabelFlowMiddleSsa
Ancestors
  o1LabelFlowMiddleInsertion o1LabelFlowMiddleOwnership
  o1LabelFlowMiddleTraversal o1LabelFlowMiddleCleanup
  o1MakeSsaCallAssembly o1MakeSsaRootedTree
  o1MakeSsaActualMaps makeSsaCurrentProps o1PassContract
  o1MakeSsaOwnership o1MakeSsaEventOwnership irSupply venomInst
  venomFnScheduleRunner venomWf makeSsaDefs makeSsaCurrentAnalysis
  venomExecProofs makeSsaRfPipeline makeSsaCurrentNonDegCleanup
  makeSsaCurrentTraceCertificate list pred_set

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

Theorem prepared_actual_tree:
  wf_function f /\ make_ssa_input_ok f /\ fn_entry_label f = SOME entry /\
  add_phi_nodes_supply s df pm li f.fn_blocks defs = (bbs,t) ==>
  ALL_DISTINCT (dom_tree_postorder (current_dom_tree f)) /\
  (!q. MEM q (dom_tree_postorder (current_dom_tree f)) ==>
    IS_SOME (lookup_block q bbs))
Proof
  strip_tac >> conj_tac
  >- metis_tac[actual_rooted_tree_distinct] >>
  drule add_phi_nodes_supply_labels >> strip_tac >>
  `?eb. entry_block f = SOME eb` by fs[fn_entry_label_def, AllCaseEqs()] >>
  `PERM (dom_tree_postorder (current_dom_tree f)) (fn_labels f)` by
    (rewrite_tac[GSYM current_dom_postorder_def] >>
     irule current_dom_postorder_perm >> fs[make_ssa_input_ok_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `MEM q (MAP (\bb. bb.bb_label) bbs)` by
    metis_tac[sortingTheory.PERM_MEM_EQ, fn_labels_def] >>
  `?b. MEM b bbs /\ b.bb_label = q` by (fs[MEM_MAP] >> metis_tac[]) >>
  `lookup_block q bbs = SOME b` by
    (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >> simp[]
QED

Theorem insert_phis_operand_domain:
  insert_phis_for_var_supply s var df pm li bbs wl hp = (bbs',s') /\
  var IN V /\ EVERY (\bb. EVERY (\i. !v. MEM (Var v) i.inst_operands ==>
    v IN V) bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY (\i. !v. MEM (Var v) i.inst_operands ==>
    v IN V) bb.bb_instructions) bbs'
Proof
  strip_tac >> drule o1MakeSsaFrontierTheory.insert_phis_for_var_supply_invariant >>
  disch_then irule >> simp[] >> rpt strip_tac >> IF_CASES_TAC >>
  gvs[insert_phi_at_block_def, build_phi_inst_supply_def, EVERY_MEM,
      MEM_FLAT, MEM_MAP] >> rpt strip_tac >> gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem add_phi_nodes_operand_domain:
  !defs s df pm li bbs bbs' s' V.
  add_phi_nodes_supply s df pm li bbs defs = (bbs',s') /\
  set (MAP FST defs) SUBSET V /\
  EVERY (\bb. EVERY (\i. !v. MEM (Var v) i.inst_operands ==>
    v IN V) bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY (\i. !v. MEM (Var v) i.inst_operands ==>
    v IN V) bb.bb_instructions) bbs'
Proof
  Induct >- simp[add_phi_nodes_supply_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> simp[add_phi_nodes_supply_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  drule_all insert_phis_operand_domain >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem function_original_operand_domain:
  EVERY (\bb. EVERY (\i. !v. MEM (Var v) i.inst_operands ==>
    v IN set (fn_ir_vars f)) bb.bb_instructions) f.fn_blocks
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  simp[fn_ir_vars_def, MEM_FLAT, MEM_MAP] >>
  qexists `block_ir_vars bb` >> conj_tac >- metis_tac[] >>
  simp[block_ir_vars_def, MEM_FLAT, MEM_MAP] >>
  qexists `inst_ir_vars i` >> simp[inst_ir_vars_def, inst_uses_def,
    MEM_operand_vars_eq_Var] >> metis_tac[]
QED

Theorem prepared_original_variable_domain:
  add_phi_nodes_supply s df pm li f.fn_blocks
    (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl f.fn_blocks) labels)))) = (bbs,t) ==>
  !bb i v. MEM bb bbs /\ MEM i bb.bb_instructions ==>
    (MEM (Var v) i.inst_operands \/ MEM v i.inst_outputs ==>
      v IN set (fn_ir_vars f))
Proof
  strip_tac >>
  `EVERY (\bb. EVERY (\i. !v. MEM (Var v) i.inst_operands ==>
    v IN set (fn_ir_vars f)) bb.bb_instructions) bbs` by
    (drule add_phi_nodes_operand_domain >> disch_then irule >>
     simp[compute_defs_original_key_domain, function_original_operand_domain]) >>
  drule prepared_original_output_domain >>
  gvs[EVERY_MEM, SUBSET_DEF] >> metis_tac[]
QED

Theorem prepared_renaming_label_flow:
  wf_function f /\ fn_inst_wf f /\ make_ssa_input_ok f /\
  fn_entry_label f = SOME entry /\ ir_supply_covers_fn s f /\
  ir_supply_inst_ok s /\ label_flow_ok (ctx with ctx_functions := [f]) /\
  (!x. code_end_var f x ==> ?d op. MEM d (fn_insts f) /\
    d.inst_opcode = ADD /\ d.inst_operands = [op; Label "code_end"] /\
    d.inst_outputs = [x] /\
    (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
    (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
      MEM (Var x) j.inst_operands ==>
      j.inst_opcode = CODECOPY /\
      (?dst sz. j.inst_operands = [dst; Var x; sz] /\
        dst <> Var x /\ sz <> Var x) /\
      ?a b. bb.bb_instructions = a ++ [d;j] ++ b)) /\
  add_phi_nodes_supply s df pm
    (select_current_live_in had_phis (liveness_analyze f) f) f.fn_blocks
    (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl f.fn_blocks) labels)))) = (bbs,s1) /\
  rename_current_blocks s1
    (init_current_rename_state (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl f.fn_blocks) labels)))))
    bbs (current_succ_map f) (current_dom_tree f) = (ct,t,final) ==>
  label_flow_ok (ctx with ctx_functions := [f with fn_blocks := final])
Proof
  strip_tac >>
  `wf_function (f with fn_blocks := bbs)` by
    metis_tac[inserted_function_wf, compute_defs_original_key_domain] >>
  `EVERY current_nondeg_block_shape bbs` by
    (irule makeSsaCurrentNonDegShapeTheory.current_nondeg_add_placement_shape >>
     goal_assum $ drule_at Any >> metis_tac[current_nondeg_input_shape]) >>
  `label_flow_ok (ctx with ctx_functions := [f with fn_blocks := bbs])` by
    (irule local_adjacent_insertion_label_flow >> goal_assum $ drule_at Any >>
     simp[] >> metis_tac[]) >>
  drule_all prepared_actual_tree >> strip_tac >>
  qabbrev_tac `trace = visit_blocks [] s1
    (init_current_rename_state (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl f.fn_blocks) labels)))))
    bbs (current_succ_map f) (current_dom_tree f)` >>
  `FST trace = (ct,t,final)` by
    simp[Abbr `trace`, o1MakeSsaVisitTraceTheory.visit_erasure] >>
  `trace = ((ct,t,final),SND trace)` by metis_tac[pairTheory.PAIR] >>
  qunabbrev_tac `trace` >>
  drule_all prepared_visit_common_owner >> strip_tac >>
  drule (SRULE [] (Q.INST [`f` |-> `f with fn_blocks := bbs`]
    visit_blocks_label_flow)) >> disch_then irule >>
  goal_assum $ drule_at Any >> simp[] >>
  conj_tac >- metis_tac[current_actual_succs_distinct] >>
  conj_tac >- (drule_at (Pat `add_phi_nodes_supply _ _ _ _ _ _ = _`)
    local_adjacent_insertion_lifetime >> simp[]) >>
  drule prepared_original_variable_domain >> strip_tac >>
  conj_tac >- fs[wf_function_def, fn_labels_def] >>
  qexistsl [`H`,`set (fn_ir_vars f)`,`t`] >> simp[] >> metis_tac[]
QED
