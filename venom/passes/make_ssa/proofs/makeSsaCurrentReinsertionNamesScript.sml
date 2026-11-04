Theory makeSsaCurrentReinsertionNames
Ancestors
  makeSsaCurrentReinsertionTokens makeSsaCurrentOutputNames makeSsaCurrentSourceCuts
  makeSsaCurrentTraceCertificate makeSsaCurrentTreePaths makeSsaCurrentActualRetention
  makeSsaCurrentAllocation makeSsaCurrentRenameTrace makeSsaCurrentTreeTrace
  makeSsaCurrentTokens makeSsaCurrentInduct makeSsaCurrentCertificate makeSsaDefs
  makeSsaCurrentPhiLocality makeSsaCurrentPlacementCut venomWf venomInst venomExecProps cfgWf list pair

Theorem current_outputs_trace_owner_history:
  !anns s rs H E names s' rs' H' E'.
  current_outputs_trace anns s rs H E names s' rs' H' E' ==>
  MAP (\e. (FST e, FST (SND e))) H' =
    MAP (\e. (FST e, FST (SND e))) H ++ anns
Proof
  Induct >> simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[MAP_APPEND, APPEND_ASSOC]
QED

Theorem current_local_trace_owner_history:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  MAP (\e. (FST e, FST (SND e))) H' =
    MAP (\e. (FST e, FST (SND e))) H ++ FLAT annss
Proof
  Induct >> simp[current_local_trace_def] >> rpt strip_tac >>
  `MAP (\e. (FST e, FST (SND e))) H1 =
    MAP (\e. (FST e, FST (SND e))) H ++ h` by
    (fs[current_inst_trace_def] >> metis_tac[current_outputs_trace_owner_history]) >>
  first_x_assum drule >> simp[APPEND_ASSOC]
QED

Theorem current_tree_trace_owners_bound:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    !t v n. MEM (t,v,n) H' ==> (?m. MEM (t,v,m) H) \/
      ?l. MEM l (dom_tree_labels tree) /\ MEM (t,v) (FLAT (A l))) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    !t v n. MEM (t,v,n) H' ==> (?m. MEM (t,v,m) H) \/
      ?l. MEM l (FLAT (MAP dom_tree_labels trees)) /\ MEM (t,v) (FLAT (A l)))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def, Once dom_tree_labels_def] >>
      Cases_on `lookup_block lbl bbs`
      >- (simp[] >> metis_tac[]) >>
      simp[] >> strip_tac >> gvs[] >>
      drule current_local_trace_owner_history >> strip_tac >>
      rpt gen_tac >> strip_tac >> first_x_assum drule >>
      disch_then (qspecl_then [`t`, `v`, `n`] mp_tac) >> simp[] >> strip_tac
      >- (`MEM (t,v) (MAP (\e. (FST e, FST (SND e))) H1)` by
            (simp[MEM_MAP] >> metis_tac[FST, SND]) >>
          qpat_x_assum `MEM (t,v) (MAP _ H1)` mp_tac >>
          asm_rewrite_tac[] >> simp[MEM_MAP] >>
          strip_tac >> metis_tac[PAIR]) >>
      metis_tac[]) 
  >- (simp[current_tree_trace_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem current_pending_owner_count_zero:
  (!t n. MEM (t,v,n) finalH ==> ?l. MEM (t,v) (FLAT (A l))) /\
  (!t l. MEM (t,v) (FLAT (A l)) ==> l = h) /\
  current_annotations_ok V H (FLAT (A (h : string))) /\
  (?tail. finalH = H ++ tail) ==>
  current_owner_count H v = 0
Proof
  strip_tac >> simp[current_owner_count_def, FILTER_EQ_NIL, EVERY_MEM] >>
  rpt strip_tac >> PairCases_on `e` >> gvs[] >>
  `?l. MEM (e0,e1) (FLAT (A l))` by metis_tac[MEM_APPEND] >>
  `l = h` by metis_tac[] >> gvs[] >>
  fs[current_annotations_ok_def, EVERY_MEM] >>
  first_x_assum drule >> simp[] >> metis_tac[MEM_MAP, FST]
QED

Theorem current_annotation_fold_default:
  !anns E.
  EVERY (\(t,w). t <> CurrentDefault v) anns ==>
  (FOLDL (\env (t,w). (w =+ t) env) E anns v = CurrentDefault v <=>
    E v = CurrentDefault v /\ ~MEM v (MAP SND anns))
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  simp[] >> rpt strip_tac >> first_x_assum drule >>
  disch_then (qspec_then `(h1 =+ h0) E` mp_tac) >>
  Cases_on `h1 = v` >> simp[combinTheory.APPLY_UPDATE_THM] >> metis_tac[]
QED

Theorem current_provenance_owner_changes_token:
  current_block_provenance fn old new anns /\
  lookup_block old.bb_label fn.fn_blocks = SOME old /\
  MEM (t,v) (FLAT anns) ==>
  current_block_token fn (current_actual_inserted fn) v old.bb_label
    (CurrentDefault v) <> CurrentDefault v
Proof
  strip_tac >>
  `EVERY (\(t,w). t <> CurrentDefault v) (FLAT anns)` by
    (simp[EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >> gvs[] >>
     metis_tac[current_block_provenance_nondefault, MEM_MAP, FST]) >>
  drule current_annotation_fold_default >>
  disch_then (qspec_then `CurrentDefault` mp_tac) >>
  drule_all current_block_provenance_scan >>
  disch_then (qspecl_then [`v`, `CurrentDefault`] mp_tac) >>
  simp[MEM_MAP] >> metis_tac[SND]
QED

Theorem current_single_original_provenance_owner_local:
  lookup_block h fn.fn_blocks = SOME old /\
  i < LENGTH old.bb_instructions /\ (EL i old.bb_instructions).inst_outputs = [v] /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 /\
  (!l. current_actual_inserted fn v l ==> l = h) /\
  current_block_provenance fn src dst anns /\
  lookup_block src.bb_label fn.fn_blocks = SOME src /\ MEM (t,v) (FLAT anns) ==>
  src.bb_label = h
Proof
  strip_tac >> spose_not_then assume_tac >>
  drule_all current_provenance_owner_changes_token >>
  `current_block_token fn (current_actual_inserted fn) v src.bb_label
    (CurrentDefault v) = CurrentDefault v` by
    (irule current_single_original_other_block >> metis_tac[]) >> simp[]
QED

Theorem current_provenance_annotation_map_member:
  !olds bbs annsss l t v.
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\
  MEM (t,v) (FLAT (current_annotation_map bbs annsss l)) ==>
  ?old new anns.
    MEM old olds /\ old.bb_label = l /\
    current_block_provenance fn old new anns /\ MEM (t,v) (FLAT anns)
Proof
  Induct_on `olds` >> Cases_on `bbs` >> Cases_on `annsss` >>
  simp[current_annotation_map_def] >> rpt gen_tac >> strip_tac >>
  rename1 `current_block_provenance fn src dst anns` >>
  `dst.bb_label = src.bb_label` by fs[current_block_provenance_def] >>
  Cases_on `src.bb_label = l` >> gvs[]
  >- metis_tac[MEM] >>
  first_x_assum (qspecl_then [`t`, `t'`] mp_tac) >>
  simp[current_annotation_map_def] >> metis_tac[MEM]
QED

Theorem current_actual_phi_annotation_owner_local:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME eb /\
  fn_phi_outputs_single_def fn /\ blocks_have_leading_phi fn.fn_blocks /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [v] /\
  LENGTH fn.fn_blocks = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (fn.fn_blocks,bbs)) annsss /\
  MEM (t,v) (FLAT (current_annotation_map bbs annsss l)) ==> l = h
Proof
  strip_tac >>
  `MEM old fn.fn_blocks /\ MEM (EL i old.bb_instructions) old.bb_instructions` by
    metis_tac[lookup_block_MEM, EL_MEM] >>
  `LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1` by
    (fs[fn_phi_outputs_single_def_def] >> metis_tac[MEM]) >>
  `!k. current_actual_inserted fn v k ==> k = h` by
    (rpt strip_tac >> `k = old.bb_label` by
      metis_tac[current_actual_inserted_single_local, MEM] >>
     metis_tac[lookup_block_label]) >>
  drule_all current_provenance_annotation_map_member >> strip_tac >>
  `lookup_block old'.bb_label fn.fn_blocks = SOME old'` by
    (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
  metis_tac[current_single_original_provenance_owner_local]
QED

Theorem current_tree_event_first_owner:
  current_tree_trace A sm tree s rs bbs [] E [] ctrs' s' bbs' finalH visited' events /\
  (!t l. MEM (t,v) (FLAT (A l)) ==> l = h) /\
  EVERY (current_event_valid A V) events /\
  MEM (h,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) events ==>
  current_owner_count H0 v = 0
Proof
  strip_tac >>
  `!t n. MEM (t,v,n) finalH ==> ?l. MEM (t,v) (FLAT (A l))` by
    (drule (cj 1 current_tree_trace_owners_bound) >> simp[] >> metis_tac[]) >>
  drule (cj 1 current_tree_trace_events) >>
  simp[EVERY_MEM] >> disch_then drule >>
  simp[current_event_trace_def] >> strip_tac >>
  drule current_local_trace_history >> strip_tac >>
  `?tail. finalH = H0 ++ tail` by metis_tac[APPEND_ASSOC] >>
  `current_annotations_ok V H0 (FLAT (A h))` by
    (fs[EVERY_MEM] >> first_x_assum drule >> simp[current_event_valid_def]) >>
  irule current_pending_owner_count_zero >>
  qexistsl_tac [`A`, `V`, `finalH`, `h`] >> metis_tac[]
QED

Theorem current_outputs_trace_first_owner_name:
  !before s rs H E names s' rs' H' E'.
  current_outputs_trace (before ++ (t,v)::after) s rs H E names s' rs' H' E' /\
  current_annotations_ok V H (before ++ (t,v)::after) /\
  current_counter rs v = 0 /\ ~MEM v (MAP SND before) ==>
  current_token_name H' t = SOME v
Proof
  Induct >> simp[current_outputs_trace_def] >> rpt gen_tac >> strip_tac
  >- (drule current_push_choice >> strip_tac >> gvs[] >>
      drule current_outputs_trace_history >> strip_tac >> gvs[] >>
      irule current_token_name_append_stable >>
      irule current_token_name_new >> fs[current_annotations_ok_def]) >>
  PairCases_on `h` >> gvs[current_outputs_trace_def] >>
  `current_counter rs1 v = 0` by
    (drule current_push_counter >> disch_then (qspec_then `v` mp_tac) >> simp[]) >>
  `current_annotations_ok V (H ++ [(h0,h1,n)]) (before ++ (t,v)::after)` by
    metis_tac[current_annotations_tail, APPEND] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem current_outputs_trace_append:
  !xs s rs H E ns s1 rs1 H1 E1 ys ms s2 rs2 H2 E2.
  current_outputs_trace xs s rs H E ns s1 rs1 H1 E1 /\
  current_outputs_trace ys s1 rs1 H1 E1 ms s2 rs2 H2 E2 ==>
  current_outputs_trace (xs ++ ys) s rs H E (ns ++ ms) s2 rs2 H2 E2
Proof
  Induct >> simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem current_local_trace_flat_outputs:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  current_outputs_trace (FLAT annss) s rs H E
    (FLAT (MAP (\inst. inst.inst_outputs) insts')) s' rs' H' E'
Proof
  Induct >> simp[current_local_trace_def, current_outputs_trace_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  irule current_outputs_trace_append >>
  fs[current_inst_trace_def] >> first_x_assum drule >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[] >> metis_tac[]
QED

Theorem current_outputs_trace_unique_prefix_name:
  current_outputs_trace (prefix ++ suffix) s rs H E names s' rs' H' E' /\
  current_annotations_ok V H (prefix ++ suffix) /\
  current_counter rs v = 0 /\ ALL_DISTINCT (MAP SND prefix) /\ MEM (t,v) prefix ==>
  current_token_name H' t = SOME v
Proof
  strip_tac >> qpat_x_assum `MEM (t,v) prefix`
    (strip_assume_tac o REWRITE_RULE[MEM_SPLIT]) >> gvs[] >>
  `~MEM v (MAP SND l1)` by (fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  qpat_x_assum `current_outputs_trace _ _ _ _ _ _ _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE[GSYM APPEND_ASSOC, APPEND]) >> strip_tac >>
  drule current_outputs_trace_first_owner_name >>
  disch_then (qspec_then `V` mp_tac) >>
  qpat_x_assum `current_annotations_ok _ _ _`
    (mp_tac o PURE_REWRITE_RULE[GSYM APPEND_ASSOC, APPEND]) >> simp[]
QED

Theorem current_inserted_annotation_owner_list:
  MAP SND (FLAT (current_inserted_annotations l pre)) =
    FLAT (MAP (\inst. inst.inst_outputs) pre)
Proof
  simp[current_inserted_annotations_def] >>
  Induct_on `pre` >> simp[MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem current_inserted_annotation_member:
  MEM v (FLAT (MAP (\inst. inst.inst_outputs) pre)) ==>
  MEM (CurrentInserted v l,v) (FLAT (current_inserted_annotations l pre))
Proof
  simp[current_inserted_annotations_def] >>
  Induct_on `pre` >> simp[] >>
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem current_local_inserted_first_name:
  current_local_trace (current_block_annotations old pre) insts s rs H E
    renamed s' rs' H' E' /\
  current_annotations_ok V H (FLAT (current_block_annotations old pre)) /\
  current_counter rs v = 0 /\
  ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) pre)) /\
  MEM v (FLAT (MAP (\inst. inst.inst_outputs) pre)) ==>
  current_token_name H' (CurrentInserted v old.bb_label) = SOME v
Proof
  strip_tac >> drule current_local_trace_flat_outputs >>
  simp[current_block_annotations_def, FLAT_APPEND] >> strip_tac >>
  drule current_outputs_trace_unique_prefix_name >>
  disch_then (qspecl_then [`v`, `CurrentInserted v old.bb_label`, `V`] mp_tac) >>
  simp[current_inserted_annotation_owner_list, current_inserted_annotation_member] >>
  fs[current_block_annotations_def, FLAT_APPEND]
QED

Theorem current_tree_event_inserted_first_name:
  current_tree_trace A sm tree s rs bbs [] E [] ctrs' s' bbs' finalH visited' events /\
  (!t l. MEM (t,v) (FLAT (A l)) ==> l = h) /\
  EVERY (current_event_valid A V) events /\
  MEM (h,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) events /\
  A h = current_block_annotations old pre /\ old.bb_label = h /\
  ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) pre)) /\
  MEM v (FLAT (MAP (\inst. inst.inst_outputs) pre)) ==>
  current_token_name finalH (CurrentInserted v h) = SOME v
Proof
  strip_tac >>
  `current_owner_count H0 v = 0` by metis_tac[current_tree_event_first_owner] >>
  `current_event_valid A V
    (h,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)` by metis_tac[EVERY_MEM] >>
  drule (cj 1 current_tree_trace_events) >>
  simp[EVERY_MEM] >> disch_then drule >>
  simp[current_event_trace_def] >> strip_tac >>
  `current_counter rs0 v = 0 /\
    current_annotations_ok V H0 (FLAT (current_block_annotations old pre))` by
    (fs[current_event_valid_def, current_allocation_consistent_def] >> metis_tac[]) >>
  `current_token_name H1 (CurrentInserted v h) = SOME v` by
    (drule current_local_inserted_first_name >>
     disch_then (qspecl_then [`v`, `V`] mp_tac) >> gvs[]) >>
  metis_tac[current_token_name_append_stable]
QED

Theorem current_prefix_relation_lookup:
  !olds news old l.
  LIST_REL R olds news /\
  (!a b. R a b ==> a.bb_label = b.bb_label) /\
  lookup_block l olds = SOME old ==>
  ?new. lookup_block l news = SOME new /\ R old new
Proof
  Induct >> Cases_on `news` >> simp[lookup_block_def, FIND_thm] >>
  rpt strip_tac >> rename1 `R src dst` >>
  `src.bb_label = dst.bb_label` by metis_tac[] >>
  Cases_on `src.bb_label = l` >> gvs[lookup_block_def] >> metis_tac[]
QED

Theorem current_certificate_inserted_prefix:
  current_structural_certificate s fn fn' s' A H events /\
  lookup_block h fn.fn_blocks = SOME old /\
  current_actual_inserted fn v h ==>
  ?pre.
    A h = current_block_annotations old pre /\
    ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) pre)) /\
    MEM v (FLAT (MAP (\inst. inst.inst_outputs) pre))
Proof
  simp[current_structural_certificate_def] >> rpt strip_tac >>
  `LENGTH fn.fn_blocks = LENGTH ins` by
    (drule current_add_phi_nodes_unique_prefix >> metis_tac[LIST_REL_LENGTH]) >>
  drule_all current_provenance_annotation_lookup >> strip_tac >>
  drule current_add_phi_nodes_unique_prefix >> strip_tac >>
  drule current_prefix_relation_lookup >>
  disch_then (qspecl_then [`old`, `h`] mp_tac) >>
  simp[current_unique_prefix_def] >>
  (impl_tac >- (rpt strip_tac >> gvs[])) >> strip_tac >>
  drule current_actual_insertion_prefix >> strip_tac >>
  drule current_prefix_relation_lookup >>
  disch_then (qspecl_then [`old`, `h`] mp_tac) >>
  simp[] >> (impl_tac >- (rpt strip_tac >> gvs[])) >> strip_tac >>
  qpat_x_assum `old with bb_instructions := pre ++ _ = _`
    (mp_tac o Q.AP_TERM `\bb. bb.bb_instructions`) >> simp[] >> strip_tac >>
  qpat_x_assum `old with bb_instructions := pre' ++ _ = _`
    (mp_tac o Q.AP_TERM `\bb. bb.bb_instructions`) >> simp[] >> strip_tac >>
  `old.bb_label = h` by metis_tac[lookup_block_label] >>
  qexists_tac `pre` >> gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem current_certificate_events_valid:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s ==>
  ?V. EVERY (current_event_valid A V) events /\
    current_history_valid V H /\ EVERY (current_event_names H V) events
Proof
  simp[current_structural_certificate_def] >> rpt strip_tac >>
  `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks /\
    ssa_vars_covered si (FLAT (MAP block_ir_vars ins)) /\
    ssa_vars_covered si (MAP FST (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn))))))` by
    (irule current_insertion_initial_supply >> metis_tac[]) >>
  `LENGTH fn.fn_blocks = LENGTH ins` by metis_tac[LENGTH_MAP] >>
  `LENGTH ins = LENGTH annsss` by (drule LIST_REL_LENGTH >> simp[]) >>
  `LIST_REL (\old anns. ?new. current_block_provenance fn old new anns)
    fn.fn_blocks annsss` by
    (fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
     first_x_assum drule >> simp[EL_ZIP] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP FST (FLAT (FLAT annsss)))` by
    (irule current_provenance_global_distinct >>
     qexistsl_tac [`fn`, `fn.fn_blocks`] >> fs[wf_function_def, fn_labels_def]) >>
  drule_all current_provenance_tree_annotations_ok >> strip_tac >>
  `current_allocation_consistent (FLAT (MAP block_ir_vars ins))
      ([] : (current_token # string # string) list) si
      (init_current_rename_state (compute_defs (MAP THE (FILTER IS_SOME
        (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))))) /\
    current_env_realizes ([] : (current_token # string # string) list)
      CurrentDefault (init_current_rename_state (compute_defs (MAP THE (FILTER IS_SOME
        (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn))))))
      (FLAT (MAP block_ir_vars ins))` by
    (irule current_initial_state_valid >> simp[]) >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  gvs[] >> drule_all current_annotated_tree_events_valid >> strip_tac >>
  `current_env_history_owners [] CurrentDefault` by
    simp[current_env_history_owners_default] >>
  drule_all current_annotated_tree_history_valid >> strip_tac >>
  drule (cj 1 current_tree_trace_events) >> strip_tac >>
  drule_all current_events_names_valid >> strip_tac >>
  qexists_tac `FLAT (MAP block_ir_vars ins)` >> simp[]
QED

Theorem current_certificate_reinserted_first_name:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME eb /\
  fn_phi_outputs_single_def fn /\ blocks_have_leading_phi fn.fn_blocks /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [v] /\ current_actual_inserted fn v h ==>
  current_token_name H (CurrentInserted v h) = SOME v
Proof
  strip_tac >>
  drule_all current_certificate_inserted_prefix >> strip_tac >>
  drule_all current_certificate_events_valid >> strip_tac >>
  qpat_x_assum `current_structural_certificate _ _ _ _ _ _ _` mp_tac >>
  simp[current_structural_certificate_def] >> rpt strip_tac >> gvs[] >>
  `LENGTH fn.fn_blocks = LENGTH ins` by
    (drule current_add_phi_nodes_unique_prefix >> metis_tac[LIST_REL_LENGTH]) >>
  `!t l. MEM (t,v) (FLAT (current_annotation_map ins annsss l)) ==> l = h` by
    (rpt strip_tac >> irule current_actual_phi_annotation_owner_local >> metis_tac[]) >>
  `MAP (\b. b.bb_label) ins = MAP (\b. b.bb_label) fn.fn_blocks` by
    (irule (cj 1 current_insertion_initial_supply) >> metis_tac[]) >>
  `!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==> IS_SOME (lookup_block l ins)` by
    metis_tac[current_actual_tree_lookup_coverage] >>
  `MEM h (dom_tree_labels (current_dom_tree fn))` by
    (drule_all current_actual_tree_label_member >>
     simp[fn_labels_def, MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  drule_all current_tree_trace_event_coverage >> strip_tac >>
  PairCases_on `ev` >> gvs[current_event_label_def] >>
  rename1 `lookup_block h fn.fn_blocks = SOME old` >>
  `old.bb_label = h` by metis_tac[lookup_block_label] >>
  drule_all current_tree_event_inserted_first_name >> simp[]
QED
