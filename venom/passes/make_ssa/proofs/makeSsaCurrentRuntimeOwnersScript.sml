Theory makeSsaCurrentRuntimeOwners
Ancestors makeSsaCurrentPhaseShape makeSsaCurrentActualRetention
  makeSsaCurrentReinsertionNames makeSsaCurrentTraceCertificate
  makeSsaCurrentDefs makeSsaCurrentInduct makeSsaCurrentTreeTrace
  makeSsaCurrentRenameTrace makeSsaCurrentTreePaths makeSsaCurrentSourceCuts
  makeSsaCurrentFinalBlock makeSsaCurrentReinsertionSlots makeSsaCurrentOutputNames
  makeSsaCurrentAnalysis makeSsaCurrentCertificate makeSsaCurrentCleanupShape
  makeSsaCurrentProps
  venomExecProps venomWf cfgWf
  venomInst list pair alist

Theorem current_owned_output_excludes:
  current_history_valid U H /\ MEM v U /\ current_owner_name H v selected /\
  (!n. MEM n inst.inst_outputs ==> ?w.
    MEM w U /\ w <> v /\ current_owner_name H w n) ==>
  ~MEM selected inst.inst_outputs
Proof
  metis_tac[current_owner_name_separate]
QED

Theorem current_cleanup_output_subset:
  MEM n (simplify_current_phi inst).inst_outputs ==> MEM n inst.inst_outputs
Proof
  simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_opcode <> PHI` >> simp[simplify_current_phi_raw_def] >>
  Cases_on `current_phi_output inst.inst_outputs` >> simp[] >>
  Cases_on `current_phi_values (remove_current_phi_self x inst.inst_operands)` >> simp[] >>
  rename1 `current_phi_values _ = SOME values` >>
  Cases_on `values` >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem current_reassign_output_members:
  !ids insts. MEM n (FLAT (MAP (\i. i.inst_outputs)
    (reassign_current_inst_ids ids insts))) <=>
    MEM n (FLAT (MAP (\i. i.inst_outputs) insts))
Proof
  Induct >> Cases_on `insts` >> simp[reassign_current_inst_ids_def]
QED

Theorem current_cleanup_parts_output_subset:
  !insts phis ordinary. simplify_current_phi_prefix_parts insts = (phis,ordinary) ==>
  !n. MEM n (FLAT (MAP (\i. i.inst_outputs) (phis ++ ordinary))) ==>
    MEM n (FLAT (MAP (\i. i.inst_outputs) insts))
Proof
  Induct >- simp[simplify_current_phi_prefix_parts_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode <> PHI`
  >- (simp[simplify_current_phi_prefix_parts_def] >> rpt strip_tac >> gvs[]) >>
  simp[simplify_current_phi_prefix_parts_def] >> pairarg_tac >> gvs[] >>
  IF_CASES_TAC >> rpt strip_tac >> gvs[] >>
  metis_tac[current_cleanup_output_subset]
QED

Theorem current_cleanup_prefix_output_subset:
  MEM n (FLAT (MAP (\i. i.inst_outputs) (simplify_current_phi_prefix insts))) ==>
  MEM n (FLAT (MAP (\i. i.inst_outputs) insts))
Proof
  simp[simplify_current_phi_prefix_def, current_reassign_output_members] >>
  pairarg_tac >> gvs[current_reassign_output_members] >>
  drule current_cleanup_parts_output_subset >> simp[] >> metis_tac[]
QED

Theorem current_cleanup_block_output_subset:
  MEM n (FLAT (MAP (\i. i.inst_outputs) (simplify_current_phi_block bb).bb_instructions)) ==>
  MEM n (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  simp[simplify_current_phi_block_def] >> Cases_on `bb.bb_instructions` >> simp[] >>
  IF_CASES_TAC >> simp[] >> strip_tac >>
  drule current_cleanup_prefix_output_subset >> simp[]
QED

Theorem current_tree_trace_entry_owners:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events /\ current_env_history_owners H E ==>
    EVERY (\ev. current_env_history_owners H' (current_event_entry_env ev)) events) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events /\ current_env_history_owners H E ==>
    EVERY (\ev. current_env_history_owners H' (current_event_entry_env ev)) events)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      drule_all current_local_trace_history_owners >> strip_tac >>
      drule (cj 2 current_tree_trace_history) >> strip_tac >>
      drule current_local_trace_history >> strip_tac >>
      first_x_assum drule >> simp[] >> strip_tac >>
      simp[current_event_entry_env_def] >>
      metis_tac[current_env_history_owners_append])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  `?tail. H1 = H ++ tail` by metis_tac[cj 1 current_tree_trace_history] >>
  `?tail. H' = H1 ++ tail` by metis_tac[cj 2 current_tree_trace_history] >>
  `current_env_history_owners H1 E` by metis_tac[current_env_history_owners_append] >>
  last_x_assum drule_all >> strip_tac >>
  last_x_assum drule_all >> strip_tac >>
  gvs[EVERY_APPEND, EVERY_MEM] >>
  metis_tac[current_env_history_owners_append]
QED

Theorem current_certificate_entry_owners:
  current_structural_certificate s fn fn' s' A H events ==>
  EVERY (\ev. current_env_history_owners H (current_event_entry_env ev)) events
Proof
  simp[current_structural_certificate_def] >> rpt strip_tac >>
  drule (cj 1 current_tree_trace_entry_owners) >> simp[]
QED

Theorem current_event_entry_owner_name:
  current_history_valid U H /\ current_event_names H U ev /\ MEM v U /\
  current_env_history_owners H (current_event_entry_env ev) ==>
  current_owner_name H v (latest_current_name (current_event_entry_rs ev) v)
Proof
  strip_tac >> drule_all current_event_names_accessors >> strip_tac >>
  metis_tac[current_env_history_owner_name]
QED

Theorem current_certificate_owner_universe:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s ==>
  ?U. current_history_valid U H /\ EVERY (current_event_valid A U) events /\
    EVERY (current_event_names H U) events /\
    (!ev v. MEM ev events /\ MEM v U ==>
      current_owner_name H v (latest_current_name (current_event_entry_rs ev) v))
Proof
  strip_tac >> drule_all current_certificate_events_valid >> strip_tac >>
  drule current_certificate_entry_owners >> strip_tac >>
  qexists_tac `V` >> simp[] >> rpt strip_tac >>
  irule current_event_entry_owner_name >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem current_local_output_history:
  current_local_trace annss insts s rs H E renamed s' rs' H' E' /\
  MEM n (FLAT (MAP (\i. i.inst_outputs) renamed)) ==>
  ?t w. MEM (t,w,n) H'
Proof
  strip_tac >> drule current_local_trace_owned_names >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  gvs[MEM_FLAT, MEM_MAP, MEM_EL] >>
  first_x_assum (qspec_then `n'` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `n''` mp_tac) >> simp[] >>
  Cases_on `EL n'' (EL n' annss)` >> simp[] >> metis_tac[]
QED

Theorem current_tree_event_output_history:
  current_tree_trace A sm tree s rs bbs [] E [] ctrs' s' bbs' H' visited' events /\
  ALL_DISTINCT (dom_tree_labels tree) /\ MEM ev events /\
  lookup_block (current_event_label ev) bbs' = SOME final /\
  MEM n (FLAT (MAP (\i. i.inst_outputs) final.bb_instructions)) ==>
  ?t w. MEM (t,w,n) H'
Proof
  strip_tac >>
  `?before after. events = before ++ ev::after` by metis_tac[MEM_SPLIT] >>
  drule_all current_trace_final_event >> strip_tac >> gvs[] >>
  qpat_x_assum `MEM n _` mp_tac >> rewrite_tac[current_replay_edges_outputs] >>
  drule (cj 1 current_tree_trace_events) >> simp[EVERY_MEM] >> strip_tac >>
  `current_event_trace A H' ev` by metis_tac[] >>
  PairCases_on `ev` >>
  gvs[current_event_trace_def, current_event_renamed_block_def] >> strip_tac >>
  fs[ETA_THM, current_replay_edges_outputs] >>
  drule current_local_output_history >>
  disch_then (qspec_then `n` mp_tac) >> simp[ETA_THM, MEM_APPEND] >> metis_tac[]
QED

Theorem current_certificate_original_output_history:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  lookup_block l fn.fn_blocks = SOME old /\
  i < LENGTH old.bb_instructions /\ j < LENGTH (EL i old.bb_instructions).inst_outputs ==>
  ?pre renamed final.
    fn'.fn_blocks = simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
    lookup_block l renamed = SOME final /\
    A l = current_block_annotations old pre /\
    MEM (CurrentOriginal old.bb_label i j, EL j (EL i old.bb_instructions).inst_outputs,
      EL j (EL (LENGTH pre+i) final.bb_instructions).inst_outputs) H
Proof
  strip_tac >>
  `MEM l (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  drule_all current_certificate_event_at >> strip_tac >>
  qpat_x_assum `current_structural_certificate _ _ _ _ _ _ _` mp_tac >>
  simp[current_structural_certificate_def] >> rpt strip_tac >> gvs[] >>
  `LENGTH fn.fn_blocks = LENGTH ins` by
    (drule current_add_phi_nodes_unique_prefix >> metis_tac[LIST_REL_LENGTH]) >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  qpat_x_assum `MEM ev events` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  PairCases_on `ev` >>
  rule_assum_tac (PURE_REWRITE_RULE [current_event_label_def]) >>
  pure_rewrite_tac [current_event_label_def] >>
  drule_at (Pat `current_tree_trace _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    current_tree_original_output_owner >>
  disch_then drule_all >> strip_tac >>
  drule_all current_provenance_annotation_lookup >> strip_tac >>
  qexistsl_tac [`pre`, `renamed`, `final`] >> simp[] >>
  `pre' = pre` by
    (gvs[basic_block_component_equality] >> metis_tac[APPEND_11]) >> gvs[]
QED

Theorem current_certificate_event_output_history:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\ MEM ev events /\
  lookup_block (current_event_label ev) fn'.fn_blocks = SOME out /\
  MEM n (FLAT (MAP (\i. i.inst_outputs) out.bb_instructions)) ==>
  ?t w. MEM (t,w,n) H
Proof
  strip_tac >>
  qpat_x_assum `current_structural_certificate _ _ _ _ _ _ _` mp_tac >>
  simp[current_structural_certificate_def] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `lookup_block _ _ = SOME out` mp_tac >>
  rewrite_tac[current_cleanup_if_lookup] >>
  Cases_on `lookup_block (current_event_label ev) renamed` >> simp[] >> strip_tac >>
  `MEM n (FLAT (MAP (\i. i.inst_outputs) x.bb_instructions))` by
    (Cases_on `blocks_have_leading_phi fn.fn_blocks` >> gvs[] >>
     metis_tac[current_cleanup_block_output_subset]) >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  drule_all current_tree_event_output_history >> simp[]
QED

Theorem current_certificate_output_owners:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s ==>
  ?U. current_history_valid U H /\ EVERY (current_event_valid A U) events /\
    EVERY (current_event_names H U) events /\
    (!ev v. MEM ev events /\ MEM v U ==>
      current_owner_name H v (latest_current_name (current_event_entry_rs ev) v)) /\
    (!ev out n. MEM ev events /\
      lookup_block (current_event_label ev) fn'.fn_blocks = SOME out /\
      MEM n (FLAT (MAP (\i. i.inst_outputs) out.bb_instructions)) ==>
      ?w. MEM w U /\ current_owner_name H w n)
Proof
  strip_tac >> drule_all current_certificate_owner_universe >> strip_tac >>
  qexists_tac `U` >> simp[] >> rpt strip_tac >>
  drule_all current_certificate_event_output_history >> strip_tac >>
  metis_tac[current_history_owner_covered, current_owner_name_def]
QED

Theorem current_certificate_output_labels:
  current_structural_certificate s fn fn' s' A H events ==>
  fn_labels fn' = fn_labels fn
Proof
  simp[current_structural_certificate_def] >> rpt strip_tac >>
  drule (cj 1 current_tree_trace_labels) >> strip_tac >>
  drule add_phi_nodes_supply_labels >> strip_tac >>
  simp[fn_labels_def, simplify_current_phis_if_def, simplify_current_phis_def,
    simplify_current_phi_block_def, MAP_MAP_o, combinTheory.o_DEF] >>
  IF_CASES_TAC >> simp[] >> IF_CASES_TAC >>
  simp[MAP_MAP_o, combinTheory.o_DEF, simplify_current_phi_block_def]
QED

Theorem current_certificate_all_output_owners:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s ==>
  ?U. current_history_valid U H /\ EVERY (current_event_valid A U) events /\
    EVERY (current_event_names H U) events /\
    (!ev v. MEM ev events /\ MEM v U ==>
      current_owner_name H v (latest_current_name (current_event_entry_rs ev) v)) /\
    (!l out n. lookup_block l fn'.fn_blocks = SOME out /\
      MEM n (FLAT (MAP (\i. i.inst_outputs) out.bb_instructions)) ==>
      ?w. MEM w U /\ current_owner_name H w n)
Proof
  strip_tac >> drule_all current_certificate_output_owners >> strip_tac >>
  qexists_tac `U` >> simp[] >> rpt strip_tac >>
  `MEM l (fn_labels fn')` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `MEM l (fn_labels fn)` by metis_tac[current_certificate_output_labels] >>
  drule_all current_certificate_event_at >> strip_tac >>
  metis_tac[]
QED
