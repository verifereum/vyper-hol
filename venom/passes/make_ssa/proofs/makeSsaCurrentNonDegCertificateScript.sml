Theory makeSsaCurrentNonDegCertificate
Ancestors
  makeSsaCurrentTraceCertificate makeSsaCurrentTreeTrace makeSsaCurrentNonDegOutputs
  makeSsaCurrentTreePaths
  makeSsaCurrentAllocation makeSsaCurrentCertificate makeSsaCurrentAnalysis
  makeSsaCurrentDefs makeSsaCurrentProps venomWf venomInst list

Theorem current_nondeg_provenance_initial_events_valid:
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\
  ALL_DISTINCT (MAP FST (FLAT (FLAT annsss))) /\
  ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) /\
  ssa_vars_covered s (MAP FST defs) /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s (init_current_rename_state defs) bbs [] CurrentDefault []
    ctrs' s' bbs' H' visited' events ==>
  EVERY (current_event_valid (current_annotation_map bbs annsss)
    (FLAT (MAP block_ir_vars bbs))) events
Proof
  strip_tac >>
  `LENGTH bbs = LENGTH annsss` by
    (drule LIST_REL_LENGTH >> simp[]) >>
  `LIST_REL (\bb anns.
      LIST_REL (\a inst. MAP SND a = inst.inst_outputs) anns bb.bb_instructions)
      bbs annsss` by
    (irule current_provenance_map_owners >> metis_tac[]) >>
  `current_annotations_ok (FLAT (MAP block_ir_vars bbs))
    ([] : (current_token # string # string) list) (FLAT (FLAT annsss))` by
    (irule current_provenance_annotations_ok >> simp[] >> conj_tac
     >- (drule current_annotation_owners_in_vars >> simp[]) >>
     qexistsl_tac [`fn`, `ZIP (olds,bbs)`] >> simp[]) >>
  `current_allocation_consistent (FLAT (MAP block_ir_vars bbs))
      ([] : (current_token # string # string) list) s
      (init_current_rename_state defs) /\
   current_env_realizes ([] : (current_token # string # string) list) CurrentDefault (init_current_rename_state defs)
      (FLAT (MAP block_ir_vars bbs))` by
    (irule current_initial_state_valid >> simp[]) >>
  `current_pending_annotations (FLAT (MAP block_ir_vars bbs))
     (current_annotation_map bbs annsss) [] []` by
    metis_tac[current_annotation_map_pending] >>
  `current_annotation_separation (current_annotation_map bbs annsss)` by
    metis_tac[current_annotation_map_separation] >>
  drule (cj 1 current_tree_trace_events_valid) >> simp[]
QED

Theorem current_nondeg_actual_initial_certificate:
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
    EVERY (current_event_names H' (FLAT (MAP block_ir_vars bbs1))) events /\
    current_history_valid (FLAT (MAP block_ir_vars bbs1)) H' /\
    EVERY (current_event_valid (current_annotation_map bbs1 annsss)
      (FLAT (MAP block_ir_vars bbs1))) events /\
    (!ev. MEM ev events ==> ?new.
      lookup_block (current_event_label ev) bbs' = SOME new /\
      LIST_REL (\anns inst.
        LIST_REL (\(t,v) n. current_token_name H' t = SOME n) anns inst.inst_outputs)
        ((current_annotation_map bbs1 annsss) (current_event_label ev)) new.bb_instructions)
Proof
  strip_tac >>
  `MAP (\b. b.bb_label) bbs1 = MAP (\b. b.bb_label) fn.fn_blocks /\
   ssa_vars_covered s1 (FLAT (MAP block_ir_vars bbs1)) /\
   ssa_vars_covered s1 (MAP FST defs)` by
    (irule current_insertion_initial_supply >> metis_tac[]) >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  `!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==> IS_SOME (lookup_block l bbs1)` by
    metis_tac[current_actual_tree_lookup_coverage] >>
  `!old. MEM old fn.fn_blocks ==> lookup_block old.bb_label fn.fn_blocks = SOME old` by
    (rpt strip_tac >> irule venomExecPropsTheory.MEM_lookup_block >>
     fs[wf_function_def, fn_labels_def]) >>
  `?annsss H' visited' events.
    LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
      (ZIP (fn.fn_blocks,bbs1)) annsss /\
    ALL_DISTINCT (MAP FST (FLAT (FLAT annsss))) /\
    current_tree_trace (current_annotation_map bbs1 annsss) (current_succ_map fn)
      (current_dom_tree fn) s1 (init_current_rename_state defs) bbs1
      [] CurrentDefault [] ctrs' s' bbs' H' visited' events` by
    (irule current_actual_tree_trace >> metis_tac[]) >>
  `LENGTH fn.fn_blocks = LENGTH bbs1` by metis_tac[LENGTH_MAP] >>
  drule_all current_nondeg_provenance_initial_events_valid >> strip_tac >>
  drule_all current_provenance_initial_tree_names >> strip_tac >>
  qexistsl_tac [`annsss`, `H'`, `visited'`, `events`] >>
  fs[current_allocation_consistent_def] >> rpt strip_tac >>
  irule current_nondeg_trace_final_outputs >> metis_tac[]
QED

Theorem current_nondeg_actual_initial_trace_names:
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
    EVERY (current_event_names H' (FLAT (MAP block_ir_vars bbs1))) events /\
    current_history_valid (FLAT (MAP block_ir_vars bbs1)) H'
Proof
  strip_tac >> drule_all current_nondeg_actual_initial_certificate >> strip_tac >>
  qexistsl_tac [`annsss`, `H'`, `visited'`, `events`] >> simp[]
QED

Theorem current_nondeg_actual_static_slots:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME bb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  defs = compute_defs (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))) /\
  add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
    (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) fn.fn_blocks defs = (bbs1,s1) /\
  rename_current_blocks s1 (init_current_rename_state defs) bbs1
    (current_succ_map fn) (current_dom_tree fn) = (ctrs',s',bbs') ==>
  ?H. current_history_valid (FLAT (MAP block_ir_vars bbs1)) H /\
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
        k < LENGTH new.bb_instructions /\
        (EL k new.bb_instructions).inst_opcode = PHI /\
        EL (2 * i) (EL k new.bb_instructions).inst_operands = Label p /\
        EL (2 * i + 1) (EL k new.bb_instructions).inst_operands = Var n)
Proof
  strip_tac >> drule_all current_nondeg_actual_initial_trace_names >> strip_tac >>
  qexists `H'` >> conj_tac >- simp[] >> rpt strip_tac >>
  `MEM p (fn_labels fn)` by
    (fs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `MEM p (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_label_member] >>
  `MEM h (case ALOOKUP (current_succ_map fn) p of NONE => [] | SOME ss => ss)` by
    simp[ALOOKUP_current_succ_map, GSYM current_cfg_edge_succs] >>
  `MEM v (FLAT (MAP block_ir_vars bbs1))` by
    metis_tac[current_initial_slot_var_covered] >>
  irule current_provenance_tree_static_slot >>
  metis_tac[current_actual_succs_distinct]
QED

Theorem current_nondeg_inserted_output_name:
  k < LENGTH pre /\ (EL k pre).inst_outputs = [v] /\
  LIST_REL (\anns inst.
    LIST_REL (\(t,w) n. current_token_name H t = SOME n) anns inst.inst_outputs)
    (current_block_annotations old pre) insts ==>
  ?n. k < LENGTH insts /\ (EL k insts).inst_outputs = [n] /\
      current_token_name H (CurrentInserted v old.bb_label) = SOME n
Proof
  strip_tac >>
  `k < LENGTH (current_block_annotations old pre)` by
    simp[current_block_annotations_def, current_inserted_annotations_def] >>
  fs[LIST_REL_EL_EQN] >>
  qpat_x_assum `!n. n < LENGTH (current_block_annotations old pre) ==> _` (qspec_then `k` mp_tac) >>
  simp[current_block_annotations_def, current_inserted_annotations_def,
       EL_APPEND_EQN, EL_MAP] >>
  Cases_on `(EL k insts).inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[]
QED

Theorem current_nondeg_provenance_map_lookup:
  !olds bbs annsss.
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\ lookup_block h bbs = SOME placed ==>
  ?old pre. MEM old olds /\ old.bb_label = h /\
    placed = old with bb_instructions := pre ++ old.bb_instructions /\
    current_annotation_map bbs annsss h = current_block_annotations old pre
Proof
  Induct >- (Cases_on `bbs` >> simp[lookup_block_def, FIND_thm]) >>
  qx_gen_tac `old0` >>
  Cases_on `bbs` >> Cases_on `annsss` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `current_block_provenance _ _ _ _` mp_tac >>
  simp[current_block_provenance_def] >> strip_tac >> gvs[] >>
  Cases_on `old0.bb_label = h` >>
  gvs[lookup_block_def, FIND_thm, current_annotation_map_def] >>
  metis_tac[]
QED

Theorem current_nondeg_provenance_final_inserted_outputs:
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\ lookup_block h bbs = SOME placed /\
  LIST_REL (\anns inst.
    LIST_REL (\(t,w) n. current_token_name H t = SOME n) anns inst.inst_outputs)
    (current_annotation_map bbs annsss h) new.bb_instructions ==>
  ?old pre. MEM old olds /\ old.bb_label = h /\
    placed = old with bb_instructions := pre ++ old.bb_instructions /\
    current_annotation_map bbs annsss h = current_block_annotations old pre /\
    (!k v. k < LENGTH pre /\ (EL k pre).inst_outputs = [v] ==>
      ?n. k < LENGTH new.bb_instructions /\ (EL k new.bb_instructions).inst_outputs = [n] /\
          current_token_name H (CurrentInserted v h) = SOME n)
Proof
  strip_tac >> drule_all current_nondeg_provenance_map_lookup >> strip_tac >>
  qexistsl_tac [`old`, `pre`] >> simp[] >> rpt strip_tac >>
  gvs[] >> drule_all current_nondeg_inserted_output_name >> simp[]
QED
