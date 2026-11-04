Theory makeSsaCurrentReinsertionSlots
Ancestors
  makeSsaCurrentEdgeTrace makeSsaCurrentPlacementCut makeSsaCurrentReinsertionNames makeSsaCurrentReinsertionTokens
  makeSsaCurrentFinalBlock makeSsaCurrentOutputNames makeSsaCurrentActualRetention makeSsaCurrentCleanupBoundary makeSsaCurrentFinalSlots makeSsaCurrentSourceCuts makeSsaCurrentTreePaths makeSsaCurrentTraceCertificate
  makeSsaCurrentCertificate makeSsaCurrentTreeTrace makeSsaCurrentTokens
  makeSsaCurrentPathBridge makeSsaCurrentTokenGraph makeSsaCurrentAnalysis
  makeSsaCurrentAllocation makeSsaCurrentRenameTrace makeSsaCurrentDefs
  o1PassContract venomWf venomExecProps venomInst cfgWf list pair

Theorem current_unique_prefix_labels:
  !olds news. LIST_REL (current_unique_prefix pm vars) olds news ==>
  MAP (\b. b.bb_label) news = MAP (\b. b.bb_label) olds
Proof
  Induct >> Cases_on `news` >> simp[] >> rpt strip_tac >>
  fs[current_unique_prefix_def]
QED

Theorem current_certificate_static_env:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\ MEM ev events ==>
  ?path. current_tree_ancestor_path (current_dom_tree fn) (current_event_label ev) path /\
    (!v. current_event_exit_env ev v =
      current_block_token fn (current_actual_inserted fn) v (current_event_label ev)
        (current_inherited_token fn (current_actual_inserted fn) v path))
Proof
  simp[current_structural_certificate_def] >> rpt strip_tac >> gvs[] >>
  drule current_add_phi_nodes_unique_prefix >> strip_tac >>
  `LENGTH fn.fn_blocks = LENGTH ins` by metis_tac[LIST_REL_LENGTH] >>
  `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks` by
    metis_tac[current_unique_prefix_labels] >>
  `!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==> IS_SOME (lookup_block l ins)` by
    metis_tac[current_actual_tree_lookup_coverage] >>
  `!old. MEM old fn.fn_blocks ==> lookup_block old.bb_label fn.fn_blocks = SOME old` by
    (rpt strip_tac >> irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
  drule_all current_provenance_tree_static_env >> metis_tac[]
QED

Theorem current_certificate_event_at:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\ MEM l (fn_labels fn) ==>
  ?ev. MEM ev events /\ current_event_label ev = l
Proof
  simp[current_structural_certificate_def] >> rpt strip_tac >> gvs[] >>
  drule current_add_phi_nodes_unique_prefix >> strip_tac >>
  `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks` by
    metis_tac[current_unique_prefix_labels] >>
  `!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==> IS_SOME (lookup_block l ins)` by
    metis_tac[current_actual_tree_lookup_coverage] >>
  `MEM l (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_label_member] >>
  drule_all current_tree_trace_event_coverage >> simp[]
QED

Theorem current_certificate_reinsertion_exit:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME eb /\
  fn_phi_outputs_single_def fn /\ blocks_have_leading_phi fn.fn_blocks /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [v] /\ MEM ev events ==>
  current_event_exit_env ev v = CurrentDefault v \/
  current_event_exit_env ev v = CurrentOriginal h i 0
Proof
  strip_tac >> drule_all current_certificate_static_env >> strip_tac >>
  drule_all current_actual_phi_reinsertion_chain >>
  disch_then (qspecl_then [`path ++ [current_event_label ev]`, `CurrentDefault v`] mp_tac) >>
  simp[GSYM current_inherited_token_def, GSYM current_inherited_token_step] >>
  Cases_on `MEM h (path ++ [current_event_label ev])` >> gvs[]
QED

Theorem current_certificate_reinsertion_exit_witness:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME eb /\
  fn_phi_outputs_single_def fn /\ blocks_have_leading_phi fn.fn_blocks /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [v] /\ current_actual_inserted fn v h ==>
  ?ev. MEM ev events /\ fn_cfg_edge fn (current_event_label ev) h /\
    current_event_exit_env ev v = CurrentOriginal h i 0
Proof
  strip_tac >> drule_all current_actual_phi_reinsertion_witness >> strip_tac >>
  `MEM p (fn_labels fn)` by
    (fs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  drule_all current_certificate_event_at >> strip_tac >>
  drule_all current_certificate_static_env >> strip_tac >>
  `current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label (REVERSE path) p` by
    metis_tac[current_actual_path_chain] >>
  `ps = REVERSE path` by
    (irule current_token_chain_unique >> metis_tac[current_token_root_idom]) >>
  qexists_tac `ev` >> gvs[]
QED

Theorem current_event_annotation_owner_covered:
  current_event_valid A V ev /\
  MEM (t,v) (FLAT (A (current_event_label ev))) ==> MEM v V
Proof
  PairCases_on `ev` >>
  simp[current_event_valid_def, current_event_label_def, current_annotations_ok_def] >>
  rpt strip_tac >> fs[EVERY_MEM] >> first_x_assum drule >> simp[]
QED

Theorem current_certificate_reinsertion_names:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME eb /\
  fn_phi_outputs_single_def fn /\ blocks_have_leading_phi fn.fn_blocks /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [v] /\ current_actual_inserted fn v h ==>
  ?src. src <> v /\ current_token_name H (CurrentOriginal h i 0) = SOME src /\
    (!ev. MEM ev events ==> latest_current_name (current_event_exit_rs ev) v = v \/
      latest_current_name (current_event_exit_rs ev) v = src) /\
    (?ev. MEM ev events /\ fn_cfg_edge fn (current_event_label ev) h /\
      latest_current_name (current_event_exit_rs ev) v = src)
Proof
  strip_tac >>
  drule_all current_certificate_events_valid >> strip_tac >>
  drule_all current_certificate_inserted_prefix >> strip_tac >>
  `MEM h (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  drule_all current_certificate_event_at >> strip_tac >>
  `MEM (CurrentInserted v h,v) (FLAT (A h))` by
    (simp[current_block_annotations_def, FLAT_APPEND] >>
     metis_tac[current_inserted_annotation_member, lookup_block_label]) >>
  `MEM v V` by
    (`current_event_valid A V ev` by metis_tac[EVERY_MEM] >>
     drule current_event_annotation_owner_covered >> simp[] >>
     disch_then (qspecl_then [`v`, `CurrentInserted v h`] mp_tac) >> gvs[]) >>
  `!ev. MEM ev events ==> current_token_name H (current_event_exit_env ev v) =
      SOME (latest_current_name (current_event_exit_rs ev) v)` by
    (rpt strip_tac >> irule (cj 2 current_event_names_accessors) >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all current_certificate_reinsertion_exit_witness >> strip_tac >>
  `current_token_name H (CurrentOriginal h i 0) =
    SOME (latest_current_name (current_event_exit_rs ev') v)` by metis_tac[] >>
  drule_all current_certificate_reinserted_first_name >> strip_tac >>
  `latest_current_name (current_event_exit_rs ev') v <> v` by
    (spose_not_then assume_tac >>
     `CurrentOriginal h i 0 = CurrentInserted v h` by
       (irule current_allocated_name_injective >> simp[] >> metis_tac[]) >> fs[]) >>
  qexists_tac `latest_current_name (current_event_exit_rs ev') v` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all current_certificate_reinsertion_exit >>
      strip_tac >>
      qpat_x_assum `!e. MEM e events ==> current_token_name H (current_event_exit_env e v) = _`
        (qspec_then `ev''` mp_tac) >> simp[current_token_name_default]) >>
  metis_tac[]
QED

Theorem current_certificate_event_labels_distinct:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb ==>
  ALL_DISTINCT (MAP current_event_label events)
Proof
  strip_tac >> fs[current_structural_certificate_def] >>
  drule current_add_phi_nodes_unique_prefix >> strip_tac >>
  `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks` by
    metis_tac[current_unique_prefix_labels] >>
  `!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==> IS_SOME (lookup_block l ins)` by
    metis_tac[current_actual_tree_lookup_coverage] >>
  irule current_tree_trace_event_labels_distinct >>
  metis_tac[current_actual_tree_labels_distinct]
QED

Theorem current_certificate_edge_pair:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  fn_cfg_edge fn p h ==>
  ?ev. MEM ev events /\ current_event_label ev = p /\
    FOLDL (\slot ev. current_event_pair_action (current_succ_map fn) h ev slot)
      (p,v) events = (p,latest_current_name (current_event_exit_rs ev) v)
Proof
  strip_tac >>
  `MEM p (fn_labels fn)` by
    (fs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  drule_all current_certificate_event_at >> strip_tac >>
  `ALL_DISTINCT (MAP current_event_label events)` by
    metis_tac[current_certificate_event_labels_distinct] >>
  qexists_tac `ev` >> simp[] >>
  `MEM h (case ALOOKUP (current_succ_map fn) (current_event_label ev) of
      NONE => [] | SOME ss => ss)` by
    simp[ALOOKUP_current_succ_map, GSYM current_cfg_edge_succs] >>
  metis_tac[current_event_fold_pair_unique, FST, SND]
QED

Theorem current_certificate_reinsertion_pairs:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME eb /\
  fn_phi_outputs_single_def fn /\ blocks_have_leading_phi fn.fn_blocks /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [v] /\ current_actual_inserted fn v h /\
  ps = (case ALOOKUP (current_pred_map fn) h of NONE => [] | SOME ps0 => ps0) ==>
  ?src slots. src <> v /\ current_token_name H (CurrentOriginal h i 0) = SOME src /\
    FOLDL (\ops ev. current_event_operand_action (current_succ_map fn) h ev ops)
      (current_phi_slots (MAP (\p. (p,v)) ps)) events = current_phi_slots slots /\
    (!p n. MEM (p,n) slots ==> n = v \/ n = src) /\
    (?p. MEM (p,src) slots)
Proof
  strip_tac >>
  `MEM h (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  drule_all current_certificate_reinsertion_names >> strip_tac >>
  qexistsl_tac [`src`, `MAP (\slot. FOLDL (\slot ev.
    current_event_pair_action (current_succ_map fn) h ev slot) slot events)
      (MAP (\p. (p,v)) ps)`] >>
  simp[current_event_fold_slots] >> conj_tac
  >- (rpt strip_tac >> fs[MEM_MAP] >> gvs[] >>
      rename1 `(p,n) = FOLDL _ (p0,v) events` >>
      `fn_cfg_edge fn p0 h` by
        gvs[ALOOKUP_current_pred_map, current_cfg_edge_preds] >>
      drule_all current_certificate_edge_pair >> disch_then (qspec_then `v` strip_assume_tac) >> gvs[] >> metis_tac[]) >>
  `MEM (current_event_label ev) ps` by
    gvs[ALOOKUP_current_pred_map, current_cfg_edge_preds] >>
  `ALL_DISTINCT (MAP current_event_label events)` by
    metis_tac[current_certificate_event_labels_distinct] >>
  `MEM (current_event_label ev) (fn_labels fn)` by
    (fs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `MEM h (case ALOOKUP (current_succ_map fn) (current_event_label ev) of
      NONE => [] | SOME ss => ss)` by
    simp[ALOOKUP_current_succ_map, GSYM current_cfg_edge_succs] >>
  `FOLDL (\slot ev. current_event_pair_action (current_succ_map fn) h ev slot)
      (current_event_label ev,v) events = (current_event_label ev,src)` by
    metis_tac[current_event_fold_pair_unique, FST, SND] >>
  simp[MEM_MAP] >> qexistsl_tac [`current_event_label ev`, `(current_event_label ev,v)`] >>
  simp[] >> metis_tac[]
QED

Theorem current_phi_two_names_copy:
  inst.inst_opcode = PHI /\ inst.inst_outputs = [dst] /\
  inst.inst_operands = current_phi_slots slots /\ src <> dst /\
  (!p n. MEM (p,n) slots ==> n = dst \/ n = src) /\
  (?p. MEM (p,src) slots) ==>
  simplify_current_phi inst = inst with <|inst_opcode := ASSIGN; inst_operands := [Var src]|>
Proof
  strip_tac >>
  `MEM src (MAP SND (FILTER (\slot. SND slot <> dst) slots))` by
    (simp[MEM_MAP, MEM_FILTER] >> metis_tac[SND]) >>
  `EVERY (\n. n = src) (MAP SND (FILTER (\slot. SND slot <> dst) slots))` by
    (simp[EVERY_MEM, MEM_MAP, MEM_FILTER] >> rpt strip_tac >>
     PairCases_on `y` >> gvs[] >> metis_tac[]) >>
  Cases_on `MAP SND (FILTER (\slot. SND slot <> dst) slots)` >> fs[] >>
  irule current_phi_slots_constant >> simp[] >> metis_tac[]
QED

Theorem current_local_inserted_output_name:
  current_local_trace (current_block_annotations old pre) insts s rs H E
    renamed s' rs' H' E' /\
  current_annotations_ok V H (FLAT (current_block_annotations old pre)) /\
  k < LENGTH pre /\ (EL k pre).inst_outputs = [v] ==>
  k < LENGTH renamed /\ ?n. (EL k renamed).inst_outputs = [n] /\
    current_token_name H' (CurrentInserted v old.bb_label) = SOME n
Proof
  strip_tac >> drule_all current_local_trace_output_names >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  `LENGTH (current_block_annotations old pre) = LENGTH pre + LENGTH old.bb_instructions` by
    simp[NoAsms, current_block_annotations_def, current_inserted_annotations_def] >>
  `k < LENGTH renamed` by decide_tac >> simp[] >>
  qpat_x_assum `!n. _` (qspec_then `k` mp_tac) >>
  simp[current_block_annotations_def, current_inserted_annotations_def, EL_APPEND_EQN,
    EL_MAP] >> strip_tac >>
  Cases_on `(EL k renamed).inst_outputs` >> gvs[] >>
  rename1 `LENGTH tail = 0` >> Cases_on `tail` >> gvs[]
QED

Theorem current_event_inserted_output_name:
  current_event_trace A finalH
    (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  current_event_valid A V
    (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  A l = current_block_annotations old pre /\
  k < LENGTH pre /\ (EL k pre).inst_outputs = [v] ==>
  k < LENGTH ren /\ ?n. (EL k ren).inst_outputs = [n] /\
    current_token_name finalH (CurrentInserted v old.bb_label) = SOME n
Proof
  simp[current_event_trace_def, current_event_valid_def] >> strip_tac >> gvs[] >>
  drule_all current_local_inserted_output_name >> strip_tac >> simp[] >>
  irule current_token_name_append_stable >> simp[]
QED

Theorem current_tree_inserted_output_name:
  ALL_DISTINCT (dom_tree_labels tree) /\
  current_tree_trace A sm tree s rs bbs [] E [] ctrs' s' bbs' H' visited' events /\
  EVERY (current_event_valid A V) events /\
  events = before ++ (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::after /\
  A l = current_block_annotations old pre /\
  k < LENGTH pre /\ (EL k pre).inst_outputs = [v] ==>
  ?final n. lookup_block l bbs' = SOME final /\ k < LENGTH final.bb_instructions /\
    (EL k final.bb_instructions).inst_outputs = [n] /\
    current_token_name H' (CurrentInserted v old.bb_label) = SOME n
Proof
  strip_tac >> drule (cj 1 current_tree_trace_events) >>
  simp[EVERY_APPEND] >> strip_tac >>
  `current_event_valid A V (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)` by
    fs[EVERY_APPEND] >>
  drule_all current_event_inserted_output_name >> strip_tac >>
  drule_all current_trace_final_event >>
  simp[current_event_label_def, current_event_renamed_block_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lookup_block l bbs' = SOME (current_replay_edges sm evs start)` >>
  `k < LENGTH start.bb_instructions` by simp[Abbr `start`] >>
  simp[current_replay_edges_output_index, Abbr `start`]
QED


Theorem current_wf_phi_slots:
  !ops. phi_well_formed ops ==> ops = current_phi_slots (phi_pairs ops)
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, phi_pairs_def, current_phi_slots_def] >>
  metis_tac[]
QED

Theorem current_certificate_block_replay:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old ==>
  ?pre renamed final.
    fn'.fn_blocks = simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
    lookup_block h renamed = SOME final /\
    A h = current_block_annotations old pre /\
    ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) pre)) /\
    EVERY (\inst. ?id v. inst = build_phi_inst_supply id v
      (case ALOOKUP (current_pred_map fn) h of NONE => [] | SOME ps => ps)) pre /\
    (!v. current_actual_inserted fn v h <=>
      ?inst. MEM inst pre /\ MEM v inst.inst_outputs) /\
    current_phi_view final.bb_instructions =
      FOLDL (\view ev. current_event_slot_action (current_succ_map fn) h ev view)
        (current_phi_view (pre ++ old.bb_instructions)) events /\
    (!k v. k < LENGTH pre /\ (EL k pre).inst_outputs = [v] ==>
      k < LENGTH final.bb_instructions /\ ?n.
      (EL k final.bb_instructions).inst_outputs = [n] /\
      current_token_name H (CurrentInserted v h) = SOME n) /\
    (!i v. i < LENGTH old.bb_instructions /\
      (EL i old.bb_instructions).inst_opcode = PHI /\
      (EL i old.bb_instructions).inst_outputs = [v] ==>
      LENGTH pre+i < LENGTH final.bb_instructions /\ ?src.
      (EL (LENGTH pre+i) final.bb_instructions).inst_outputs = [src] /\
      current_token_name H (CurrentOriginal h i 0) = SOME src /\
      (fn_phis_non_degenerate fn ==>
        simplify_current_phi (EL (LENGTH pre+i) final.bb_instructions) =
          EL (LENGTH pre+i) final.bb_instructions))
Proof
  strip_tac >> drule_all current_certificate_events_valid >> strip_tac >>
  qpat_x_assum `current_structural_certificate _ _ _ _ _ _ _` mp_tac >>
  simp[current_structural_certificate_def] >> rpt strip_tac >> gvs[] >>
  `LENGTH fn.fn_blocks = LENGTH ins` by
    (drule current_add_phi_nodes_unique_prefix >> metis_tac[LIST_REL_LENGTH]) >>
  drule_all current_provenance_annotation_lookup >> strip_tac >>
  drule current_add_phi_nodes_unique_prefix >> strip_tac >>
  drule current_prefix_relation_lookup >>
  disch_then (qspecl_then [`old`, `h`] mp_tac) >>
  simp[current_unique_prefix_def] >>
  (impl_tac >- (rpt strip_tac >> gvs[])) >> strip_tac >>
  `pre' = pre` by
    (gvs[basic_block_component_equality] >> metis_tac[APPEND_11]) >>
  `!p ss. ALOOKUP (current_succ_map fn) p = SOME ss ==> ALL_DISTINCT ss` by
    metis_tac[current_actual_succs_distinct] >>
  drule_all current_tree_trace_phi_lookup >> strip_tac >>
  qpat_x_assum `pre' = pre` SUBST_ALL_TAC >>
  `old.bb_label = h` by metis_tac[lookup_block_label] >>
  drule current_actual_insertion_prefix >> strip_tac >>
  drule current_prefix_relation_lookup >>
  disch_then (qspecl_then [`old`, `h`] mp_tac) >> simp[] >>
  (impl_tac >- (rpt strip_tac >> gvs[])) >> strip_tac >>
  `pre' = pre` by
    (gvs[basic_block_component_equality] >> metis_tac[APPEND_11]) >>
  qpat_x_assum `pre' = pre` SUBST_ALL_TAC >>
  `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks /\
    ssa_vars_covered si (FLAT (MAP block_ir_vars ins)) /\
    ssa_vars_covered si (MAP FST (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn))))))` by
    (irule current_insertion_initial_supply >> metis_tac[]) >>
  `!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==> IS_SOME (lookup_block l ins)` by
    metis_tac[current_actual_tree_lookup_coverage] >>
  `MEM h (dom_tree_labels (current_dom_tree fn))` by
    (drule_all current_actual_tree_label_member >>
     simp[fn_labels_def, MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  drule_all current_tree_trace_event_coverage >> strip_tac >>
  PairCases_on `ev` >> gvs[current_event_label_def] >>
  rename1 `lookup_block h fn.fn_blocks = SOME old` >>
  qpat_x_assum `MEM _ events` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  qexistsl_tac [`pre`, `renamed`, `new`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all current_tree_inserted_output_name >> strip_tac >>
      gvs[] >>
      `old.bb_label = h` by metis_tac[lookup_block_label] >>
      qpat_x_assum `old.bb_label = h` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  qpat_x_assum `add_phi_nodes_supply _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `LIST_REL (current_unique_prefix _ _) _ _` kall_tac >>
  qpat_x_assum `LIST_REL (\old new. ?pre. _) _ _` kall_tac >>
  qpat_x_assum `EVERY (\i. ?id v. MEM _ _ /\ _) pre` kall_tac >>
  qpat_x_assum `EVERY (\i. ?id v. _) pre` kall_tac >>
  qpat_x_assum `current_phi_view _ = _` kall_tac >>
  qpat_x_assum `!v. current_actual_inserted _ _ _ <=> _` kall_tac >>
  `LIST_REL (\old anns. ?new. current_block_provenance fn old new anns)
      fn.fn_blocks annsss` by
    (fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
     `n < LENGTH ins /\ n < LENGTH fn.fn_blocks` by decide_tac >>
     qpat_x_assum `!n. n < LENGTH ins ==> _` (qspec_then `n` mp_tac) >>
     simp[EL_ZIP] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP FST (FLAT (FLAT annsss)))` by
    (irule current_provenance_global_distinct >>
     qexistsl_tac [`fn`, `fn.fn_blocks`] >> fs[wf_function_def, fn_labels_def]) >>
  rpt strip_tac >> drule_all current_provenance_tree_original_phi_output >> strip_tac >>
  `pre' = pre` by
    (gvs[basic_block_component_equality] >> metis_tac[APPEND_11]) >>
  qpat_x_assum `pre' = pre` SUBST_ALL_TAC >>
  qpat_x_assum `events = _` (mk_asm "event_split") >>
  gvs[] >> conj_tac
  >- (`old.bb_label = h` by metis_tac[lookup_block_label] >>
      qpat_x_assum `old.bb_label = h` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  strip_tac >>
  `MEM (EL i old.bb_instructions) (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >>
     qexists_tac `old` >> conj_tac
     >- metis_tac[lookup_block_MEM] >>
     simp[MEM_EL] >> qexists_tac `i` >> simp[]) >>
  `inst_wf (EL i old.bb_instructions)` by
    (fs[fn_inst_wf_def] >> first_x_assum irule >>
     qexists_tac `old` >> conj_tac
     >- metis_tac[lookup_block_MEM] >>
     simp[MEM_EL] >> qexists_tac `i` >> simp[]) >>
  `phi_well_formed (EL i old.bb_instructions).inst_operands` by
    (qpat_x_assum `inst_wf _` (mp_tac o REWRITE_RULE [inst_wf_def]) >>
     qpat_x_assum `_.inst_opcode = PHI` (fn th => rewrite_tac[th]) >> simp[]) >>
  drule current_wf_phi_slots >> strip_tac >>
  asm_x "event_split" assume_tac >>
  drule_all current_provenance_tree_original_phi_retained >> strip_tac >>
  `pre' = pre` by
    (gvs[basic_block_component_equality] >> metis_tac[APPEND_11]) >>
  qpat_x_assum `pre' = pre` SUBST_ALL_TAC >> gvs[arithmeticTheory.ADD_COMM]
QED

Theorem current_certificate_reinsertion_copy:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME eb /\
  fn_phi_outputs_single_def fn /\ blocks_have_leading_phi fn.fn_blocks /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [v] /\ current_actual_inserted fn v h ==>
  ?pre renamed final k src.
    fn'.fn_blocks = simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
    lookup_block h renamed = SOME final /\ A h = current_block_annotations old pre /\
    k < LENGTH pre /\ (EL k pre).inst_outputs = [v] /\
    k < LENGTH final.bb_instructions /\ src <> v /\
    current_token_name H (CurrentOriginal h i 0) = SOME src /\
    (EL k final.bb_instructions).inst_outputs = [v] /\
    simplify_current_phi (EL k final.bb_instructions) =
      (EL k final.bb_instructions) with <|inst_opcode := ASSIGN; inst_operands := [Var src]|> /\
    LENGTH pre+i < LENGTH final.bb_instructions /\
    (EL (LENGTH pre+i) final.bb_instructions).inst_outputs = [src] /\
    (fn_phis_non_degenerate fn ==>
      simplify_current_phi (EL (LENGTH pre+i) final.bb_instructions) =
        EL (LENGTH pre+i) final.bb_instructions)
Proof
  strip_tac >> drule_all current_certificate_block_replay >> strip_tac >>
  drule_all current_certificate_reinserted_first_name >> strip_tac >>
  qabbrev_tac `ps = (case ALOOKUP (current_pred_map fn) h of
    NONE => [] | SOME ps => ps)` >>
  `ps = (case ALOOKUP (current_pred_map fn) h of NONE => [] | SOME ps => ps)` by
    simp[Abbr `ps`] >>
  drule_all current_certificate_reinsertion_pairs >> strip_tac >>
  `?inst. MEM inst pre /\ MEM v inst.inst_outputs` by metis_tac[] >>
  qpat_x_assum `EVERY _ pre` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then (drule_then strip_assume_tac) >>
  gvs[build_phi_inst_supply_def] >>
  qpat_x_assum `MEM <| inst_id := _; inst_opcode := _; inst_operands := _; inst_outputs := _ |> pre`
    (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `k < LENGTH pre` >>
  ` (EL k pre).inst_outputs = [v] /\ (EL k pre).inst_opcode = PHI /\
    (EL k pre).inst_operands = current_phi_slots (MAP (\p. (p,v)) ps)` by
    (qpat_x_assum `_ = EL k pre` (fn th => rewrite_tac[GSYM th]) >>
     simp[current_phi_slots_def, MAP_MAP_o, combinTheory.o_DEF]) >>
  qpat_x_assum `!k v. k < LENGTH pre /\ _ ==> _`
    (qspecl_then [`k`, `v`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!i v. i < LENGTH old.bb_instructions /\ _ ==> _`
    (qspecl_then [`i`, `v`] mp_tac) >> simp[] >> strip_tac >>
  `k < LENGTH (pre ++ old.bb_instructions) /\
    (EL k (pre ++ old.bb_instructions)).inst_opcode = PHI` by
    simp[EL_APPEND_EQN] >>
  drule_all current_phi_view_fold_instruction >> strip_tac >>
  gvs[EL_APPEND_EQN] >>
  qexistsl_tac [`pre`, `renamed`, `final`, `k`] >> simp[] >>
  irule current_phi_two_names_copy >> simp[] >> metis_tac[]
QED
