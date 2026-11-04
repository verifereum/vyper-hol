Theory makeSsaCurrentReinsertionTokens
Ancestors
  makeSsaCurrentTokens makeSsaCurrentTokenOwnership makeSsaCurrentCutTokens makeSsaCurrentOccurrence
  makeSsaCurrentAvailability makeSsaCurrentPlacementCut makeSsaCurrentFrontier
  makeSsaCurrentTokenGraph makeSsaCurrentLastSite makeSsaCurrentPlacement
  makeSsaCurrentPhiLocality makeSsaCurrentDefSupport makeSsaCurrentAnalysis
  makeSsaCurrentTreePaths makeSsaCurrentGraphCut dominatorDefs venomWf cfgWf venomInst venomExecProps list

Theorem current_single_original_block_token:
  wf_function fn /\ lookup_block h fn.fn_blocks = SOME old /\
  i < LENGTH old.bb_instructions /\ (EL i old.bb_instructions).inst_outputs = [v] /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 ==>
  current_block_token fn ins v h t = CurrentOriginal h i 0
Proof
  strip_tac >>
  `MEM old fn.fn_blocks /\ MEM (EL i old.bb_instructions) old.bb_instructions` by
    metis_tac[lookup_block_MEM, EL_MEM] >>
  drule current_block_token_original >>
  disch_then (qspecl_then [`v`, `t`, `ins`] mp_tac) >>
  (impl_tac >- metis_tac[MEM]) >> strip_tac >>
  `MEM (EL i' old.bb_instructions) old.bb_instructions` by metis_tac[EL_MEM] >>
  `MEM v (EL i' old.bb_instructions).inst_outputs` by metis_tac[EL_MEM] >>
  `(EL i' old.bb_instructions) = (EL i old.bb_instructions)` by
    metis_tac[current_single_def_occurrence, MEM] >>
  `i' = i` by metis_tac[current_block_index_unique] >> gvs[]
QED

Theorem current_single_original_other_block:
  lookup_block h fn.fn_blocks = SOME old /\
  i < LENGTH old.bb_instructions /\ (EL i old.bb_instructions).inst_outputs = [v] /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 /\
  (!l. ins v l ==> l = h) /\ l <> h ==>
  current_block_token fn ins v l t = t
Proof
  strip_tac >> irule current_non_site_block_token >>
  spose_not_then assume_tac >>
  gvs[current_changing_site_def] >>
  `MEM old fn.fn_blocks /\ MEM (EL i old.bb_instructions) old.bb_instructions` by
    metis_tac[lookup_block_MEM, EL_MEM] >>
  `old = bb` by metis_tac[current_single_def_occurrence, MEM] >>
  metis_tac[lookup_block_label]
QED

Theorem current_single_original_chain:
  wf_function fn /\ lookup_block h fn.fn_blocks = SOME old /\
  i < LENGTH old.bb_instructions /\ (EL i old.bb_instructions).inst_outputs = [v] /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 /\
  (!l. ins v l ==> l = h) ==>
  !path t. current_chain_token fn ins v path t =
    if MEM h path then CurrentOriginal h i 0 else t
Proof
  strip_tac >>
  `!t. current_block_token fn ins v h t = CurrentOriginal h i 0` by
    metis_tac[current_single_original_block_token] >>
  `!l t. l <> h ==> current_block_token fn ins v l t = t` by
    metis_tac[current_single_original_other_block] >>
  Induct >> simp[current_chain_token_def] >> rpt gen_tac >>
  Cases_on `h' = h` >> simp[] >> Cases_on `MEM h path` >> simp[]
QED

Theorem current_actual_phi_reinsertion_chain:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME eb /\
  fn_phi_outputs_single_def fn /\ blocks_have_leading_phi fn.fn_blocks /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [v] ==>
  !path t. current_chain_token fn (current_actual_inserted fn) v path t =
    if MEM h path then CurrentOriginal h i 0 else t
Proof
  strip_tac >>
  `MEM old fn.fn_blocks /\ MEM (EL i old.bb_instructions) old.bb_instructions` by
    metis_tac[lookup_block_MEM, EL_MEM] >>
  `LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1` by
    (fs[fn_phi_outputs_single_def_def] >> metis_tac[MEM]) >>
  `!l. current_actual_inserted fn v l ==> l = h` by
    (rpt strip_tac >> `l = old.bb_label` by
      metis_tac[current_actual_inserted_single_local, MEM] >>
     metis_tac[lookup_block_label]) >>
  irule current_single_original_chain >> metis_tac[]
QED

Theorem current_actual_phi_reinsertion_exit:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME eb /\
  fn_phi_outputs_single_def fn /\ blocks_have_leading_phi fn.fn_blocks /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [v] ==>
  current_block_token fn (current_actual_inserted fn) v p
    (current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps)) =
    if MEM h (REVERSE ps ++ [p]) then CurrentOriginal h i 0 else CurrentDefault v
Proof
  strip_tac >>
  rewrite_tac[GSYM current_inherited_token_step, current_inherited_token_def] >>
  drule_all current_actual_phi_reinsertion_chain >> simp[]
QED

Theorem current_actual_single_reinsertion_frontier:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME eb /\
  blocks_have_leading_phi fn.fn_blocks /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 /\
  current_actual_inserted fn v db.bb_label ==>
  current_frontier_edge (current_frontier_map fn) db.bb_label db.bb_label
Proof
  simp[current_actual_inserted_def] >> strip_tac >>
  `!d. MEM d roots ==> d = db.bb_label` by
    metis_tac[current_compute_defs_single_support] >>
  qpat_x_assum `current_pruned_reach _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE[current_pruned_reach_cases])
  >- metis_tac[] >>
  qpat_assum `blocks_have_leading_phi _`
    (fn th => rule_assum_tac (REWRITE_RULE[th])) >>
  `d = db.bb_label` by metis_tac[current_compute_defs_pruned_reach_local] >> gvs[]
QED

Theorem current_actual_phi_reinsertion_witness:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME eb /\
  fn_phi_outputs_single_def fn /\ blocks_have_leading_phi fn.fn_blocks /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [v] /\ current_actual_inserted fn v h ==>
  ?p ps. fn_cfg_edge fn p h /\
    current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps p /\
    current_block_token fn (current_actual_inserted fn) v p
      (current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps)) =
      CurrentOriginal h i 0
Proof
  strip_tac >>
  `MEM old fn.fn_blocks /\ MEM (EL i old.bb_instructions) old.bb_instructions /\
   old.bb_label = h` by metis_tac[lookup_block_MEM, EL_MEM, lookup_block_label] >>
  `LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1` by
    (fs[fn_phi_outputs_single_def_def] >> metis_tac[MEM]) >>
  `current_frontier_edge (current_frontier_map fn) h h` by
    metis_tac[current_actual_single_reinsertion_frontier, MEM] >>
  `MEM h (fn_labels fn)` by metis_tac[current_actual_inserted_label] >>
  fs[current_frontier_edge_def] >>
  drule_all current_frontier_elim >> strip_tac >>
  `fn_cfg_edge fn p h` by metis_tac[current_cfg_edge_preds] >>
  `MEM p (fn_labels fn)` by
    (fs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  drule_all current_actual_token_chain >> strip_tac >>
  `MEM h (REVERSE ps ++ [p])` by
    (Cases_on `h = p` >> simp[] >>
     metis_tac[current_actual_chain_membership, strict_dominates_def, MEM_REVERSE]) >>
  qexistsl_tac [`p`, `ps`] >> simp[] >>
  drule_all current_actual_phi_reinsertion_exit >> fs[MEM_REVERSE]
QED
