Theory makeSsaCurrentReinsertionSlots
Ancestors
  makeSsaCurrentReinsertionNames makeSsaCurrentReinsertionTokens
  makeSsaCurrentSourceCuts makeSsaCurrentTreePaths makeSsaCurrentTraceCertificate
  makeSsaCurrentCertificate makeSsaCurrentTreeTrace makeSsaCurrentTokens
  makeSsaCurrentPathBridge makeSsaCurrentTokenGraph makeSsaCurrentAnalysis
  makeSsaCurrentAllocation makeSsaCurrentRenameTrace makeSsaCurrentDefs
  venomWf venomExecProps venomInst cfgWf list pair

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
