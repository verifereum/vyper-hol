Theory makeSsaCurrentRetainedNonclobber
Ancestors makeSsaCurrentCleanupOrigins makeSsaCurrentRetention
  makeSsaCurrentReinsertionOrder makeSsaCurrentOutputNames
  makeSsaCurrentReinsertionNames makeSsaCurrentCleanupShape
  makeSsaCurrentRenameTrace makeSsaCurrentAllocation makeSsaCurrentTreeTrace
  makeSsaCurrentFinalBlock makeSsaCurrentDefs makeSsaCurrentCleanupBoundary
  makeSsaCurrentRuntimeOwners makeSsaCurrentSourceCuts makeSsaCurrentReinsertionSlots
  makeSsaCurrentTreePaths makeSsaCurrentTraceCertificate makeSsaCurrentCertificate
  makeSsaHelper venomExecProps venomWf cfgWf cfgHelpers venomInst list alist

Theorem current_cleanup_origin_step_unchanged:
  ~MEM n inst.inst_outputs /\ current_cleanup_origin_step V inst M = SOME N ==>
  ALOOKUP N n = ALOOKUP M n
Proof
  Cases_on `inst.inst_opcode = NOP` >>
  gvs[current_cleanup_origin_step_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem current_cleanup_origins_unchanged:
  !copies M N.
  ~MEM n (FLAT (MAP (\i. i.inst_outputs) copies)) /\
  current_cleanup_origins V copies M = SOME N ==>
  ALOOKUP N n = ALOOKUP M n
Proof
  Induct >> simp[current_cleanup_origins_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all current_cleanup_origin_step_unchanged >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem current_outputs_trace_name_history:
  !anns s rs H E names s' rs' H' E'.
  current_outputs_trace anns s rs H E names s' rs' H' E' ==>
  MAP (SND o SND) H' = MAP (SND o SND) H ++ names
Proof
  Induct >> simp[current_outputs_trace_def] >> gen_tac >> PairCases_on `h` >>
  simp[current_outputs_trace_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[MAP_APPEND, APPEND_ASSOC]
QED

Theorem current_inst_trace_name_history:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' ==>
  MAP (SND o SND) H' = MAP (SND o SND) H ++ inst'.inst_outputs
Proof
  simp[current_inst_trace_def] >> rpt strip_tac >>
  drule current_outputs_trace_name_history >>
  Cases_on `inst.inst_opcode = PHI` >> simp[]
QED

Theorem current_local_trace_name_history:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  MAP (SND o SND) H' = MAP (SND o SND) H ++
    FLAT (MAP (\i. i.inst_outputs) insts')
Proof
  Induct >> simp[current_local_trace_def] >> rpt strip_tac >>
  drule current_inst_trace_name_history >> strip_tac >>
  first_x_assum drule >> simp[APPEND_ASSOC]
QED

Theorem current_event_outputs_distinct:
  current_event_trace A finalH
    (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  current_history_valid V finalH ==>
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) ren))
Proof
  simp[current_event_trace_def, current_history_valid_def] >> rpt strip_tac >>
  drule current_local_trace_name_history >> strip_tac >>
  gvs[MAP_APPEND, ALL_DISTINCT_APPEND]
QED

Theorem current_replay_edges_outputs:
  MAP (\i. i.inst_outputs) (current_replay_edges sm events bb).bb_instructions =
  MAP (\i. i.inst_outputs) bb.bb_instructions
Proof
  mp_tac (Q.SPECL [`events`, `bb`] current_replay_edges_shape) >>
  simp[current_edge_shape_def, LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP] >>
  metis_tac[]
QED

Theorem current_reassign_outputs:
  !ids insts. MAP (\i. i.inst_outputs) (reassign_current_inst_ids ids insts) =
    MAP (\i. i.inst_outputs) insts
Proof
  Induct >> Cases_on `insts` >> simp[reassign_current_inst_ids_def]
QED

Theorem current_simplify_phi_outputs:
  (simplify_current_phi inst).inst_outputs = inst.inst_outputs \/
  (simplify_current_phi inst).inst_outputs = []
Proof
  simp[simplify_current_phi_def, keep_current_phi_vars_def,
    simplify_current_phi_raw_def] >> rpt CASE_TAC >> simp[]
QED

Theorem current_cleanup_parts_outputs_distinct:
  !insts phis ordinary.
  simplify_current_phi_prefix_parts insts = (phis,ordinary) /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) ==>
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (phis ++ ordinary)))
Proof
  Induct >> simp[simplify_current_phi_prefix_parts_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  drule current_cleanup_parts_output_subset >> simp[] >> strip_tac >>
  fs[ALL_DISTINCT_APPEND] >>
  mp_tac (Q.INST [`inst` |-> `h`] current_simplify_phi_outputs) >>
  Cases_on `(simplify_current_phi h).inst_opcode = PHI` >>
  strip_tac >> gvs[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem current_cleanup_prefix_outputs_distinct:
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) ==>
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (simplify_current_phi_prefix insts)))
Proof
  simp[simplify_current_phi_prefix_def] >> pairarg_tac >>
  simp[current_reassign_outputs] >>
  strip_tac >> drule_all current_cleanup_parts_outputs_distinct >> simp[]
QED

Theorem current_cleanup_block_outputs_distinct:
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
    (simplify_current_phi_block bb).bb_instructions))
Proof
  Cases_on `bb.bb_instructions` >> simp[simplify_current_phi_block_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[current_cleanup_prefix_outputs_distinct]
QED

Theorem current_certificate_block_outputs_distinct:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn'.fn_blocks = SOME out ==>
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) out.bb_instructions))
Proof
  strip_tac >> drule_all current_certificate_events_valid >> strip_tac >>
  qpat_assum `current_structural_certificate _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [current_structural_certificate_def]) >>
  gvs[] >>
  drule current_add_phi_nodes_unique_prefix >> strip_tac >>
  `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks` by
    metis_tac[current_unique_prefix_labels] >>
  drule (cj 1 current_tree_trace_labels) >> strip_tac >>
  gvs[current_cleanup_if_lookup, AllCaseEqs()] >>
  `MEM h (fn_labels fn)` by
    (simp[fn_labels_def] >>
     metis_tac[lookup_block_MEM, lookup_block_label, MEM_MAP]) >>
  drule_all current_certificate_event_at >> strip_tac >>
  `?before after. events = before ++ ev::after` by metis_tac[MEM_SPLIT] >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  drule_all current_trace_final_event >> strip_tac >>
  drule (cj 1 current_tree_trace_events) >> simp[EVERY_MEM] >>
  disch_then (qspec_then `ev` mp_tac) >> simp[] >>
  PairCases_on `ev` >>
  gvs[current_event_label_def, current_event_renamed_block_def] >> strip_tac >>
  drule_all current_event_outputs_distinct >> strip_tac >>
  gvs[current_replay_edges_outputs] >>
  irule current_cleanup_block_outputs_distinct >>
  simp[current_replay_edges_outputs]
QED

Theorem current_outputs_split_nonclobber:
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (phis ++ copies ++ tail))) /\
  MEM n (FLAT (MAP (\i. i.inst_outputs) phis)) ==>
  ~MEM n (FLAT (MAP (\i. i.inst_outputs) copies))
Proof
  simp[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem current_outputs_take_subset:
  !copies k n. MEM n (FLAT (MAP (\i. i.inst_outputs) (TAKE k copies))) ==>
    MEM n (FLAT (MAP (\i. i.inst_outputs) copies))
Proof
  Induct >> Cases_on `k` >> simp[] >> metis_tac[]
QED

Theorem current_certificate_cleanup_nonclobber:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn'.fn_blocks = SOME out /\
  out.bb_instructions = phis ++ copies ++ tail /\
  MEM n (FLAT (MAP (\i. i.inst_outputs) phis)) ==>
  ~MEM n (FLAT (MAP (\i. i.inst_outputs) copies))
Proof
  strip_tac >> drule_all current_certificate_block_outputs_distinct >>
  gvs[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem current_certificate_cleanup_prefix_nonclobber:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn'.fn_blocks = SOME out /\
  out.bb_instructions = phis ++ copies ++ tail /\
  MEM n (FLAT (MAP (\i. i.inst_outputs) phis)) ==>
  ~MEM n (FLAT (MAP (\i. i.inst_outputs) (TAKE k copies)))
Proof
  strip_tac >> drule_all current_certificate_cleanup_nonclobber >>
  metis_tac[current_outputs_take_subset]
QED

Theorem current_certificate_cleanup_origins_preserved:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn'.fn_blocks = SOME out /\
  out.bb_instructions = phis ++ copies ++ tail /\
  MEM n (FLAT (MAP (\i. i.inst_outputs) phis)) /\
  current_cleanup_origins V copies M = SOME N ==>
  ALOOKUP N n = ALOOKUP M n
Proof
  strip_tac >> drule_all current_certificate_cleanup_nonclobber >>
  strip_tac >> irule current_cleanup_origins_unchanged >>
  qexistsl_tac [`V`, `copies`] >> simp[]
QED

Theorem current_certificate_cleanup_prefix_origins_preserved:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn'.fn_blocks = SOME out /\
  out.bb_instructions = phis ++ copies ++ tail /\
  MEM n (FLAT (MAP (\i. i.inst_outputs) phis)) /\
  current_cleanup_origins V (TAKE k copies) M = SOME N ==>
  ALOOKUP N n = ALOOKUP M n
Proof
  strip_tac >> drule_all current_certificate_cleanup_prefix_nonclobber >>
  disch_then (qspec_then `k` assume_tac) >>
  irule current_cleanup_origins_unchanged >>
  qexistsl_tac [`V`, `TAKE k copies`] >> simp[]
QED
