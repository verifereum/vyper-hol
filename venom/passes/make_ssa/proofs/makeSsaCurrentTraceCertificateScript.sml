Theory makeSsaCurrentTraceCertificate
Ancestors
  makeSsaCurrentFinalSlots makeSsaCurrentTreePaths makeSsaCurrentTreeTrace
  makeSsaCurrentEdgeTrace
  makeSsaCurrentCertificate makeSsaCurrentAllocation makeSsaCurrentTokens
  makeSsaCurrentProps makeSsaCurrentDefs makeSsaHelper cfgTransformProps
  makeSsaCurrentAnalysis cfgAnalysisProps cfgHelpers venomExecProps
  venomFnScheduleRunner irSupply venomWf venomInst list rich_list pair sorting cfgCorrectnessProof

Theorem current_event_names_accessors:
  current_event_names H V ev /\ MEM v V ==>
  current_token_name H (current_event_entry_env ev v) =
    SOME (latest_current_name (current_event_entry_rs ev) v) /\
  current_token_name H (current_event_exit_env ev v) =
    SOME (latest_current_name (current_event_exit_rs ev) v)
Proof
  PairCases_on `ev` >>
  simp[current_event_names_def, current_event_entry_env_def,
    current_event_exit_env_def, current_event_entry_rs_def, current_event_exit_rs_def]
QED

Theorem current_provenance_tree_static_names:
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\
  (!old. MEM old olds ==> lookup_block old.bb_label fn.fn_blocks = SOME old) /\
  (!l. MEM l (dom_tree_labels tree) ==> IS_SOME (lookup_block l bbs)) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s rs bbs H CurrentDefault visited ctrs' s' bbs' H' visited' events /\
  EVERY (current_event_names H' V) events /\ MEM ev events ==>
  ?path. current_tree_ancestor_path tree (current_event_label ev) path /\
    (!v. MEM v V ==>
      current_token_name H'
        (current_inherited_token fn (current_actual_inserted fn) v path) =
        SOME (latest_current_name (current_event_entry_rs ev) v)) /\
    (!v. MEM v V ==>
      current_token_name H'
        (current_block_token fn (current_actual_inserted fn) v (current_event_label ev)
          (current_inherited_token fn (current_actual_inserted fn) v path)) =
        SOME (latest_current_name (current_event_exit_rs ev) v))
Proof
  strip_tac >> drule_all current_provenance_tree_static_env >> strip_tac >>
  qexists_tac `path` >> simp[] >> fs[EVERY_MEM] >>
  metis_tac[current_event_names_accessors]
QED

Theorem current_provenance_tree_static_slot:
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\
  (!old. MEM old olds ==> lookup_block old.bb_label fn.fn_blocks = SOME old) /\
  (!l. MEM l (dom_tree_labels tree) ==> IS_SOME (lookup_block l bbs)) /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s rs bbs H CurrentDefault visited ctrs' s' bbs' H' visited' events /\
  EVERY (current_event_names H' V) events /\
  (!p ss. ALOOKUP sm p = SOME ss ==> ALL_DISTINCT ss) /\
  lookup_block h bbs = SOME old /\ MEM p (dom_tree_labels tree) /\
  MEM h (case ALOOKUP sm p of NONE => [] | SOME ss => ss) /\
  k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_opcode = PHI /\
  (EL k old.bb_instructions).inst_operands = current_phi_slots slots /\
  i < LENGTH slots /\ EL i slots = (p,v) /\ MEM v V ==>
  ?new path n. lookup_block h bbs' = SOME new /\
    current_tree_ancestor_path tree p path /\
    current_token_name H'
      (current_block_token fn (current_actual_inserted fn) v p
        (current_inherited_token fn (current_actual_inserted fn) v path)) = SOME n /\
    LENGTH new.bb_instructions = LENGTH old.bb_instructions /\
    k < LENGTH new.bb_instructions /\ (EL k new.bb_instructions).inst_opcode = PHI /\
    EL (2 * i) (EL k new.bb_instructions).inst_operands = Label p /\
    EL (2 * i + 1) (EL k new.bb_instructions).inst_operands = Var n
Proof
  strip_tac >> drule_all current_tree_trace_event_coverage >> strip_tac >>
  drule_all current_tree_trace_event_labels_distinct >> strip_tac >>
  drule_all current_provenance_tree_static_names >> strip_tac >>
  `FST (EL i slots) = current_event_label ev` by simp[] >>
  `MEM h (case ALOOKUP sm (current_event_label ev) of NONE => [] | SOME ss => ss)` by simp[] >>
  drule_all current_tree_trace_phi_slot >> simp[] >> strip_tac >>
  qexistsl_tac [`new`, `path`, `latest_current_name (current_event_exit_rs ev) v`] >>
  fs[] >> metis_tac[]
QED

Theorem current_actual_tree_label_member:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME bb ==>
  (MEM l (dom_tree_labels (current_dom_tree fn)) <=> MEM l (fn_labels fn))
Proof
  strip_tac >> drule_all current_dom_postorder_perm >>
  simp[current_dom_postorder_def] >> strip_tac >>
  `MEM l (dom_tree_postorder (current_dom_tree fn)) <=> MEM l (fn_labels fn)` by
    metis_tac[PERM_MEM_EQ] >>
  metis_tac[cj 1 current_tree_labels_postorder]
QED

Theorem current_actual_tree_lookup_coverage:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME bb /\
  MAP (\b. b.bb_label) bbs = MAP (\b. b.bb_label) fn.fn_blocks ==>
  !l. MEM l (dom_tree_labels (current_dom_tree fn)) ==> IS_SOME (lookup_block l bbs)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `MEM l (fn_labels fn)` by metis_tac[current_actual_tree_label_member] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) bbs)` by fs[wf_function_def, fn_labels_def] >>
  `MEM l (MAP (\b. b.bb_label) bbs)` by fs[fn_labels_def] >>
  `?b. MEM b bbs /\ b.bb_label = l` by metis_tac[MEM_MAP] >>
  drule_all MEM_lookup_block >> simp[]
QED

Theorem current_query_map_lookup_domain:
  !labels query p ss.
  ALOOKUP (current_query_map labels query) p = SOME ss ==> MEM p labels
Proof
  Induct >> simp[current_query_map_def] >> rpt gen_tac >>
  Cases_on `h = p` >> fs[current_query_map_def] >> metis_tac[]
QED

Theorem current_actual_succs_distinct:
  wf_function fn /\ ALOOKUP (current_succ_map fn) p = SOME ss ==>
  ALL_DISTINCT ss
Proof
  strip_tac >>
  `MEM p (fn_labels fn)` by
    (fs[current_succ_map_def] >> metis_tac[current_query_map_lookup_domain]) >>
  `?b. MEM b fn.fn_blocks /\ b.bb_label = p` by
    (fs[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `ss = bb_succs b` by
    metis_tac[ALOOKUP_current_succ_map, cfg_analyze_preserves_bb_succs, optionTheory.SOME_11] >>
  simp[bb_succs_def] >> CASE_TAC >> simp[all_distinct_nub]
QED

Theorem current_insertion_initial_supply:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  defs = compute_defs (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl fn.fn_blocks) labels))) /\
  add_phi_nodes_supply s df pm li fn.fn_blocks defs = (bbs,s1) ==>
  MAP (\b. b.bb_label) bbs = MAP (\b. b.bb_label) fn.fn_blocks /\
  ssa_vars_covered s1 (FLAT (MAP block_ir_vars bbs)) /\
  ssa_vars_covered s1 (MAP FST defs)
Proof
  strip_tac >>
  `ssa_vars_covered s (FLAT (MAP block_ir_vars fn.fn_blocks))` by
    fs[ir_supply_covers_fn_def, list_subset_def, fn_ir_vars_def, ssa_vars_covered_def] >>
  `ssa_vars_covered s (MAP FST defs)` by
    (simp[] >> irule compute_defs_lookup_blocks_vars_covered >> simp[]) >>
  `ALL_DISTINCT (FLAT (MAP block_ir_inst_ids fn.fn_blocks))` by
    (fs[wf_function_def, fn_inst_ids_distinct_def] >>
     qpat_x_assum `ALL_DISTINCT (FLAT _)` mp_tac >>
     simp[GSYM block_ir_inst_ids_def, ETA_THM]) >>
  `EVERY (\id. MEM id s.irs_used_inst_ids) (FLAT (MAP block_ir_inst_ids fn.fn_blocks))` by
    fs[ir_supply_covers_fn_def, list_subset_def, fn_ir_inst_ids_def] >>
  `ALL_DISTINCT (MAP basic_block_bb_label fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  drule_all add_phi_nodes_supply_ok >> strip_tac >>
  drule ssa_ids_supply_ok_extends >> strip_tac >>
  drule_all ssa_vars_covered_mono >>
  pure_rewrite_tac[bb_label_eta] >> metis_tac[]
QED

Theorem current_actual_initial_trace_names:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME bb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  defs = compute_defs (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))) /\
  add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
    (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) fn.fn_blocks defs = (bbs1,s1) /\
  rename_current_blocks s1 (init_current_rename_state defs) bbs1
    (current_succ_map fn) (current_dom_tree fn) = (ctrs',s',bbs') ==>
  ?annsss H' visited' events.
    LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
      (ZIP (fn.fn_blocks,bbs1)) annsss /\
    LENGTH fn.fn_blocks = LENGTH bbs1 /\
    (!old. MEM old fn.fn_blocks ==> lookup_block old.bb_label fn.fn_blocks = SOME old) /\
    (!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==> IS_SOME (lookup_block l bbs1)) /\
    ALL_DISTINCT (dom_tree_labels (current_dom_tree fn)) /\
    current_tree_trace (current_annotation_map bbs1 annsss) (current_succ_map fn)
      (current_dom_tree fn) s1 (init_current_rename_state defs) bbs1
      [] CurrentDefault [] ctrs' s' bbs' H' visited' events /\
    EVERY (current_event_names H' (FLAT (MAP block_ir_vars bbs1))) events
Proof
  strip_tac >>
  `MAP (\b. b.bb_label) bbs1 = MAP (\b. b.bb_label) fn.fn_blocks /\
   ssa_vars_covered s1 (FLAT (MAP block_ir_vars bbs1)) /\
   ssa_vars_covered s1 (MAP FST defs)` by
    (irule current_insertion_initial_supply >> metis_tac[]) >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  `!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==> IS_SOME (lookup_block l bbs1)` by
    (metis_tac[current_actual_tree_lookup_coverage]) >>
  `!old. MEM old fn.fn_blocks ==> lookup_block old.bb_label fn.fn_blocks = SOME old` by
    (rpt strip_tac >> irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
  `?annsss H' visited' events.
    LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
      (ZIP (fn.fn_blocks,bbs1)) annsss /\
    ALL_DISTINCT (MAP FST (FLAT (FLAT annsss))) /\
    current_tree_trace (current_annotation_map bbs1 annsss) (current_succ_map fn)
      (current_dom_tree fn) s1 (init_current_rename_state defs) bbs1
      [] CurrentDefault [] ctrs' s' bbs' H' visited' events` by
    (irule current_actual_tree_trace >> metis_tac[]) >>
  `LENGTH fn.fn_blocks = LENGTH bbs1` by metis_tac[LENGTH_MAP] >>
  drule_all current_provenance_initial_tree_names >> strip_tac >>
  qexistsl_tac [`annsss`, `H'`, `visited'`, `events`] >> simp[]
QED

Theorem current_phi_slots_vars:
  !slots. venomInst$operand_vars (current_phi_slots slots) = MAP SND slots
Proof
  Induct >> simp[current_phi_slots_def, venomInstTheory.operand_vars_def] >> gen_tac >> PairCases_on `h` >>
  fs[current_phi_slots_def, venomInstTheory.operand_vars_def, operand_var_def]
QED

Theorem current_initial_slot_var_covered:
  lookup_block h bbs = SOME old /\ k < LENGTH old.bb_instructions /\
  (EL k old.bb_instructions).inst_operands = current_phi_slots slots /\
  i < LENGTH slots /\ EL i slots = (p,v) ==>
  MEM v (FLAT (MAP block_ir_vars bbs))
Proof
  strip_tac >>
  `MEM old bbs` by metis_tac[lookup_block_MEM] >>
  `MEM (EL k old.bb_instructions) old.bb_instructions` by simp[EL_MEM] >>
  `MEM v (MAP SND slots)` by
    (simp[MEM_MAP] >> qexists_tac `(p,v)` >> simp[] >> metis_tac[EL_MEM]) >>
  `MEM v (inst_ir_vars (EL k old.bb_instructions))` by
    simp[inst_ir_vars_def, inst_uses_def, current_phi_slots_vars] >>
  simp[MEM_FLAT, MEM_MAP] >> qexists_tac `block_ir_vars old` >>
  conj_tac >- metis_tac[] >>
  simp[block_ir_vars_def, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem current_actual_static_certificate:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME bb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  defs = compute_defs (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))) /\
  add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
    (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) fn.fn_blocks defs = (bbs1,s1) /\
  rename_current_blocks s1 (init_current_rename_state defs) bbs1
    (current_succ_map fn) (current_dom_tree fn) = (ctrs',s',bbs') ==>
  ?H events.
    (?annsss visited'. current_tree_trace (current_annotation_map bbs1 annsss)
      (current_succ_map fn) (current_dom_tree fn) s1 (init_current_rename_state defs)
      bbs1 [] CurrentDefault [] ctrs' s' bbs' H visited' events) /\
    (!p. MEM p (fn_labels fn) ==> ?ev. MEM ev events /\ current_event_label ev = p) /\
    (!ev. MEM ev events ==>
      ?path. current_tree_ancestor_path (current_dom_tree fn) (current_event_label ev) path /\
        (!v. MEM v (FLAT (MAP block_ir_vars bbs1)) ==>
          current_token_name H
            (current_inherited_token fn (current_actual_inserted fn) v path) =
          SOME (latest_current_name (current_event_entry_rs ev) v)) /\
        (!v. MEM v (FLAT (MAP block_ir_vars bbs1)) ==>
          current_token_name H
            (current_block_token fn (current_actual_inserted fn) v (current_event_label ev)
              (current_inherited_token fn (current_actual_inserted fn) v path)) =
          SOME (latest_current_name (current_event_exit_rs ev) v))) /\
    (!h old p v k slots i.
      lookup_block h bbs1 = SOME old /\ fn_cfg_edge fn p h /\
      k < LENGTH old.bb_instructions /\
      (EL k old.bb_instructions).inst_opcode = PHI /\
      (EL k old.bb_instructions).inst_operands = current_phi_slots slots /\
      i < LENGTH slots /\ EL i slots = (p,v) ==>
      ?new path n. lookup_block h bbs' = SOME new /\
        current_tree_ancestor_path (current_dom_tree fn) p path /\
        current_token_name H
          (current_block_token fn (current_actual_inserted fn) v p
            (current_inherited_token fn (current_actual_inserted fn) v path)) = SOME n /\
        LENGTH new.bb_instructions = LENGTH old.bb_instructions /\
        k < LENGTH new.bb_instructions /\ (EL k new.bb_instructions).inst_opcode = PHI /\
        EL (2 * i) (EL k new.bb_instructions).inst_operands = Label p /\
        EL (2 * i + 1) (EL k new.bb_instructions).inst_operands = Var n)
Proof
  strip_tac >> drule_all current_actual_initial_trace_names >> strip_tac >>
  qexistsl_tac [`H'`, `events`] >> conj_tac >- metis_tac[] >> conj_tac
  >- (rpt strip_tac >>
      `MEM p (dom_tree_labels (current_dom_tree fn))` by
        metis_tac[current_actual_tree_label_member] >>
      drule_all current_tree_trace_event_coverage >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule current_provenance_tree_static_names >> metis_tac[]) >>
  rpt strip_tac >>
  `MEM p (fn_labels fn)` by (fs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `MEM p (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_label_member] >>
  `MEM h (case ALOOKUP (current_succ_map fn) p of NONE => [] | SOME ss => ss)` by
    simp[ALOOKUP_current_succ_map, GSYM current_cfg_edge_succs] >>
  `MEM v (FLAT (MAP block_ir_vars bbs1))` by
    metis_tac[current_initial_slot_var_covered] >>
  irule current_provenance_tree_static_slot >>
  metis_tac[current_actual_succs_distinct]
QED
