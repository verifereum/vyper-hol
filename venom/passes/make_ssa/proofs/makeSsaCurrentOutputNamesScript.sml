Theory makeSsaCurrentOutputNames
Ancestors
  makeSsaCurrentSourceCuts makeSsaCurrentFinalBlock makeSsaCurrentRenameTrace
  makeSsaCurrentAllocation makeSsaCurrentCertificate makeSsaCurrentTreeTrace makeSsaCurrentTreePaths cfgHelpers venomInst list pair arithmetic

Theorem current_local_trace_output_names:
  !annss insts s rs H E insts' s' rs' H' E' V.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' /\
  current_annotations_ok V H (FLAT annss) ==>
  LIST_REL (\anns inst. LIST_REL (\(t,v) n. current_token_name H' t = SOME n)
    anns inst.inst_outputs) annss insts'
Proof
  Induct >> simp[current_local_trace_def] >> rpt gen_tac >> strip_tac >>
  `current_annotations_ok V H h` by metis_tac[current_annotations_split, FLAT] >>
  `LIST_REL (\(t,v) n. current_token_name H1 t = SOME n) h inst1.inst_outputs` by
    metis_tac[current_inst_trace_outputs] >>
  `current_annotations_ok V H1 (FLAT annss)` by
    (fs[current_inst_trace_def] >>
     irule current_outputs_trace_remaining >> metis_tac[FLAT]) >>
  `?tail. H' = H1 ++ tail` by metis_tac[current_local_trace_history] >>
  simp[] >> conj_tac
  >- (irule LIST_REL_mono >> goal_assum $ drule_at Any >>
      simp[] >> rpt strip_tac >> PairCases_on `x` >> gvs[] >>
      metis_tac[current_token_name_append_stable]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem current_original_outputs_length[simp]:
  !vs start. LENGTH (current_original_outputs l i start vs) = LENGTH vs
Proof
  Induct >> simp[current_original_outputs_def]
QED

Theorem current_original_annotations_length[simp]:
  !insts start. LENGTH (current_original_annotations l start insts) = LENGTH insts
Proof
  Induct >> simp[current_original_annotations_def]
QED

Theorem current_original_outputs_index:
  !vs start j. j < LENGTH vs ==>
    EL j (current_original_outputs l i start vs) = (CurrentOriginal l i (start+j), EL j vs)
Proof
  Induct >> simp[current_original_outputs_def] >> rpt gen_tac >>
  Cases_on `j` >> simp[current_original_outputs_def, ADD_CLAUSES]
QED

Theorem current_original_annotations_index:
  !insts start i. i < LENGTH insts ==>
    EL i (current_original_annotations l start insts) =
      current_original_outputs l (start+i) 0 (EL i insts).inst_outputs
Proof
  Induct >> simp[current_original_annotations_def] >> rpt gen_tac >>
  Cases_on `i` >> simp[current_original_annotations_def, ADD_CLAUSES]
QED

Theorem current_block_annotations_index:
  i < LENGTH old.bb_instructions /\ j < LENGTH (EL i old.bb_instructions).inst_outputs ==>
  EL j (EL (LENGTH pre+i) (current_block_annotations old pre)) =
    (CurrentOriginal old.bb_label i j, EL j (EL i old.bb_instructions).inst_outputs)
Proof
  simp[current_block_annotations_def, current_inserted_annotations_def,
    EL_APPEND_EQN, current_original_annotations_index, current_original_outputs_index]
QED

Theorem current_local_original_output_name:
  current_local_trace (current_block_annotations old pre) insts s rs H E
    renamed s' rs' H' E' /\
  current_annotations_ok V H (FLAT (current_block_annotations old pre)) /\
  i < LENGTH old.bb_instructions /\ j < LENGTH (EL i old.bb_instructions).inst_outputs ==>
  LENGTH pre+i < LENGTH renamed /\
  j < LENGTH (EL (LENGTH pre+i) renamed).inst_outputs /\
  LENGTH (EL (LENGTH pre+i) renamed).inst_outputs = LENGTH (EL i old.bb_instructions).inst_outputs /\
  current_token_name H' (CurrentOriginal old.bb_label i j) =
    SOME (EL j (EL (LENGTH pre+i) renamed).inst_outputs)
Proof
  strip_tac >> drule_all current_local_trace_output_names >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  `LENGTH (current_block_annotations old pre) = LENGTH pre + LENGTH old.bb_instructions` by
    simp[NoAsms, current_block_annotations_def, current_inserted_annotations_def] >>
  `LENGTH pre+i < LENGTH renamed` by decide_tac >> simp[] >>
  qpat_x_assum `!n. _` (qspec_then `LENGTH pre+i` mp_tac) >> simp[] >> strip_tac >>
  `j < LENGTH (EL (LENGTH pre+i) (current_block_annotations old pre))` by
    simp[current_block_annotations_def, current_inserted_annotations_def, EL_APPEND_EQN,
       current_original_annotations_index] >>
  gvs[] >> first_x_assum (qspec_then `j` mp_tac) >>
  `i < LENGTH old.bb_instructions` by decide_tac >>
  gvs[current_block_annotations_def, current_inserted_annotations_def, EL_APPEND_EQN,
    current_original_annotations_index, current_original_outputs_index, ADD_COMM]
QED

Theorem current_event_original_output_name:
  current_event_trace A finalH
    (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  current_event_valid A V
    (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  A l = current_block_annotations old pre /\
  i < LENGTH old.bb_instructions /\ j < LENGTH (EL i old.bb_instructions).inst_outputs ==>
  LENGTH pre+i < LENGTH ren /\
  j < LENGTH (EL (LENGTH pre+i) ren).inst_outputs /\
  LENGTH (EL (LENGTH pre+i) ren).inst_outputs = LENGTH (EL i old.bb_instructions).inst_outputs /\
  current_token_name finalH (CurrentOriginal old.bb_label i j) =
    SOME (EL j (EL (LENGTH pre+i) ren).inst_outputs)
Proof
  simp[current_event_trace_def, current_event_valid_def] >> strip_tac >> gvs[] >>
  drule_all current_local_original_output_name >> strip_tac >>
  gvs[ADD_COMM] >> irule current_token_name_append_stable >> simp[]
QED

Theorem current_replay_edges_output_index:
  k < LENGTH bb.bb_instructions ==>
  k < LENGTH (current_replay_edges sm events bb).bb_instructions /\
  (EL k (current_replay_edges sm events bb).bb_instructions).inst_outputs =
    (EL k bb.bb_instructions).inst_outputs
Proof
  qspecl_then [`events`, `bb`] mp_tac current_replay_edges_shape >>
  simp[current_edge_shape_def, LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem current_provenance_annotation_lookup:
  !olds bbs annsss old l.
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\ lookup_block l olds = SOME old ==>
  ?pre inserted.
    lookup_block l bbs = SOME inserted /\
    inserted = old with bb_instructions := pre ++ old.bb_instructions /\
    current_annotation_map bbs annsss l = current_block_annotations old pre
Proof
  Induct_on `olds` >> Cases_on `bbs` >> Cases_on `annsss` >>
  simp[lookup_block_def, FIND_thm] >> rpt gen_tac >> strip_tac >>
  rename1 `current_block_provenance fn src dst anns` >>
  `?pre. dst = src with bb_instructions := pre ++ src.bb_instructions /\
    anns = current_block_annotations src pre` by metis_tac[current_block_provenance_def] >>
  Cases_on `src.bb_label = l` >> gvs[]
  >- (qexists_tac `pre` >> simp[current_annotation_map_def]) >>
  qpat_x_assum `!bbs annsss old l. _`
    (qspecl_then [`t`, `t'`, `old`, `l`] mp_tac) >>
  simp[lookup_block_def] >> strip_tac >> qexists_tac `pre'` >>
  gvs[current_annotation_map_def]
QED

Theorem current_annotated_tree_events_valid:
  LENGTH bbs = LENGTH annsss /\
  current_annotations_ok V ([] : (current_token # string # string) list)
    (FLAT (FLAT annsss)) /\
  current_allocation_consistent V [] s rs /\ current_env_realizes ([] : (current_token # string # string) list) E rs V /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s rs bbs [] E [] ctrs' s' bbs' H' visited' events ==>
  EVERY (current_event_valid (current_annotation_map bbs annsss) V) events
Proof
  strip_tac >>
  `current_pending_annotations V (current_annotation_map bbs annsss) [] []` by
    metis_tac[current_annotation_map_pending] >>
  `current_annotation_separation (current_annotation_map bbs annsss)` by
    (irule current_annotation_map_separation >> fs[current_annotations_ok_def]) >>
  drule (cj 1 current_tree_trace_events_valid) >> simp[] >>
  disch_then (qspec_then `V` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem current_tree_original_output_name:
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\
  current_annotations_ok V ([] : (current_token # string # string) list)
    (FLAT (FLAT annsss)) /\
  current_allocation_consistent V [] s rs /\ current_env_realizes ([] : (current_token # string # string) list) E rs V /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s rs bbs [] E [] ctrs' s' bbs' H' visited' events /\
  events = before ++ (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::after /\
  lookup_block l olds = SOME old /\
  i < LENGTH old.bb_instructions /\ j < LENGTH (EL i old.bb_instructions).inst_outputs ==>
  ?pre inserted final.
    lookup_block l bbs = SOME inserted /\
    inserted = old with bb_instructions := pre ++ old.bb_instructions /\
    lookup_block l bbs' = SOME final /\
    LENGTH pre+i < LENGTH final.bb_instructions /\
    j < LENGTH (EL (LENGTH pre+i) final.bb_instructions).inst_outputs /\
    LENGTH (EL (LENGTH pre+i) final.bb_instructions).inst_outputs =
      LENGTH (EL i old.bb_instructions).inst_outputs /\
    current_token_name H' (CurrentOriginal old.bb_label i j) =
      SOME (EL j (EL (LENGTH pre+i) final.bb_instructions).inst_outputs)
Proof
  strip_tac >>
  `LENGTH bbs = LENGTH annsss` by (drule LIST_REL_LENGTH >> simp[]) >>
  drule_all current_provenance_annotation_lookup >> strip_tac >>
  drule_all current_annotated_tree_events_valid >>
  simp[EVERY_APPEND] >> strip_tac >>
  drule (cj 1 current_tree_trace_events) >> simp[EVERY_APPEND] >> strip_tac >>
  drule_all current_event_original_output_name >> strip_tac >>
  drule_all current_trace_final_event >>
  simp[current_event_label_def, current_event_renamed_block_def] >> strip_tac >>
  qexists_tac `pre` >> simp[] >>
  qmatch_goalsub_abbrev_tac `current_replay_edges sm evs start` >>
  `LENGTH pre+i < LENGTH start.bb_instructions` by simp[Abbr `start`] >>
  `LENGTH pre+i < LENGTH (current_replay_edges sm evs start).bb_instructions /\
    (EL (LENGTH pre+i) (current_replay_edges sm evs start).bb_instructions).inst_outputs =
      (EL (LENGTH pre+i) start.bb_instructions).inst_outputs` by
    (irule current_replay_edges_output_index >> simp[]) >>
  gvs[Abbr `start`, ADD_COMM]
QED

Theorem current_provenance_tree_annotations_ok:
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\
  ALL_DISTINCT (MAP FST (FLAT (FLAT annsss))) ==>
  current_annotations_ok (FLAT (MAP block_ir_vars bbs))
    ([] : (current_token # string # string) list) (FLAT (FLAT annsss))
Proof
  strip_tac >>
  `LIST_REL (\bb anns.
      LIST_REL (\a inst. MAP SND a = inst.inst_outputs) anns bb.bb_instructions)
      bbs annsss` by
    (irule current_provenance_map_owners >> metis_tac[]) >>
  irule current_provenance_annotations_ok >> simp[] >> conj_tac
  >- (drule current_annotation_owners_in_vars >> simp[]) >>
  qexistsl_tac [`fn`, `ZIP (olds,bbs)`] >> simp[]
QED

Theorem current_provenance_tree_original_phi_output:
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\
  ALL_DISTINCT (MAP FST (FLAT (FLAT annsss))) /\
  ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) /\
  ssa_vars_covered s (MAP FST defs) /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s (init_current_rename_state defs) bbs [] CurrentDefault []
    ctrs' s' bbs' H' visited' events /\
  events = before ++ (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::after /\
  lookup_block l olds = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [v] ==>
  ?pre inserted final name.
    lookup_block l bbs = SOME inserted /\
    inserted = old with bb_instructions := pre ++ old.bb_instructions /\
    lookup_block l bbs' = SOME final /\
    LENGTH pre+i < LENGTH final.bb_instructions /\
    (EL (LENGTH pre+i) final.bb_instructions).inst_outputs = [name] /\
    current_token_name H' (CurrentOriginal old.bb_label i 0) = SOME name
Proof
  strip_tac >>
  drule_all current_provenance_tree_annotations_ok >> strip_tac >>
  `current_allocation_consistent (FLAT (MAP block_ir_vars bbs))
      ([] : (current_token # string # string) list) s (init_current_rename_state defs) /\
    current_env_realizes ([] : (current_token # string # string) list)
      CurrentDefault (init_current_rename_state defs) (FLAT (MAP block_ir_vars bbs))` by
    (irule current_initial_state_valid >> simp[]) >>
  `0 < LENGTH (EL i old.bb_instructions).inst_outputs` by simp[] >>
  drule_all current_tree_original_output_name >> strip_tac >>
  qexistsl_tac [`pre`, `inserted`, `final`,
    `EL 0 (EL (LENGTH pre+i) final.bb_instructions).inst_outputs`] >>
  gvs[ADD_COMM] >>
  Cases_on `(EL (i+LENGTH pre) final.bb_instructions).inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED
