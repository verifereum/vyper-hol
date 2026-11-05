Theory makeSsaCurrentRestrictedRuntime
Ancestors makeSsaCurrentRuntimeOwners makeSsaCurrentLastSite makeSsaCurrentTreePaths
  makeSsaCurrentPlacementCut makeSsaCurrentCertificate makeSsaCurrentTreeTrace
  makeSsaCurrentOutputNames makeSsaCurrentFinalBlock makeSsaCurrentTraceCertificate
  makeSsaCurrentActualRetention makeSsaCurrentRenameTrace
  makeSsaCurrentDefs makeSsaCurrentSourceCuts makeSsaCurrentReinsertionNames
  makeSsaCurrentCleanupShape makeSsaCurrentProps
  makeSsaCurrentReinsertionSlots makeSsaCurrentRestrictedSegment
  makeSsaCurrentExecutionHistory makeSsaCurrentSemanticHistory
  venomInst venomExecSemantics venomExecProps venomWf cfgWf list pair

Theorem current_original_annotations_output_members[local]:
  !insts i. MEM (t,w) (FLAT (current_original_annotations l i insts)) ==>
    MEM w (FLAT (MAP (\inst. inst.inst_outputs) insts))
Proof
  Induct >> simp[current_original_annotations_def] >> rpt strip_tac >>
  metis_tac[current_original_outputs_owners, MEM_MAP, SND]
QED

Theorem current_annotation_member_site[local]:
  lookup_block l fn.fn_blocks = SOME old /\
  (!v. current_actual_inserted fn v old.bb_label <=>
    ?i. MEM i pre /\ MEM v i.inst_outputs) /\
  MEM (t,w) (FLAT (current_block_annotations old pre)) ==>
  current_changing_site fn (current_actual_inserted fn) w l
Proof
  strip_tac >>
  `old.bb_label = l` by metis_tac[lookup_block_label] >>
  `MEM old fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  gvs[current_block_annotations_def, FLAT_APPEND] 
  >- (gvs[current_inserted_annotations_def, MEM_FLAT, MEM_MAP] >>
      simp[current_changing_site_def] >> metis_tac[]) >>
  drule current_original_annotations_output_members >>
  simp[MEM_FLAT, MEM_MAP, current_changing_site_def] >> metis_tac[]
QED

Theorem current_local_output_annotation:
  current_local_trace annss insts s rs H E renamed s' rs' H' E' /\
  MEM n (FLAT (MAP (\i. i.inst_outputs) renamed)) ==>
  ?t w. MEM (t,w,n) H' /\ MEM (t,w) (FLAT annss)
Proof
  strip_tac >> drule current_local_trace_owned_names >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  gvs[MEM_FLAT, MEM_MAP, MEM_EL] >>
  first_x_assum (qspec_then `n'` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `n''` mp_tac) >> simp[] >>
  Cases_on `EL n'' (EL n' annss)` >> simp[] >> rpt strip_tac >>
  qexistsl_tac [`q`, `r`] >> simp[] >>
  metis_tac[EL_MEM]
QED

Theorem current_tree_event_output_annotation:
  current_tree_trace A sm tree s rs bbs [] E [] ctrs' s' bbs' H' visited' events /\
  ALL_DISTINCT (dom_tree_labels tree) /\ MEM ev events /\
  lookup_block (current_event_label ev) bbs' = SOME final /\
  MEM n (FLAT (MAP (\i. i.inst_outputs) final.bb_instructions)) ==>
  ?t w. MEM (t,w,n) H' /\ MEM (t,w) (FLAT (A (current_event_label ev)))
Proof
  strip_tac >>
  `?before after. events = before ++ ev::after` by metis_tac[MEM_SPLIT] >>
  drule_all current_trace_final_event >> strip_tac >> gvs[] >>
  qpat_x_assum `MEM n _` mp_tac >> rewrite_tac[current_replay_edges_outputs] >>
  drule (cj 1 current_tree_trace_events) >> simp[EVERY_MEM] >> strip_tac >>
  `current_event_trace A H' ev` by metis_tac[] >>
  PairCases_on `ev` >>
  gvs[current_event_trace_def, current_event_renamed_block_def,
    current_event_label_def] >> strip_tac >>
  fs[ETA_THM, current_replay_edges_outputs] >>
  drule current_local_output_annotation >>
  disch_then (qspec_then `n` mp_tac) >> simp[ETA_THM, MEM_APPEND] >> metis_tac[]
QED

Theorem current_certificate_annotation_site:
  current_structural_certificate s fn fn' s' A H events /\
  lookup_block l fn.fn_blocks = SOME old /\ MEM (t,w) (FLAT (A l)) ==>
  current_changing_site fn (current_actual_inserted fn) w l
Proof
  simp[current_structural_certificate_def] >> rpt strip_tac >>
  `LENGTH fn.fn_blocks = LENGTH ins` by
    (drule current_add_phi_nodes_unique_prefix >> metis_tac[LIST_REL_LENGTH]) >>
  drule_all current_provenance_annotation_lookup >> strip_tac >>
  drule current_actual_insertion_prefix >> strip_tac >>
  drule current_prefix_relation_lookup >>
  disch_then (qspecl_then [`old`, `l`] mp_tac) >>
  simp[] >> (impl_tac >- (rpt strip_tac >> gvs[])) >> strip_tac >>
  qpat_x_assum `old with bb_instructions := pre ++ _ = _`
    (mp_tac o Q.AP_TERM `\bb. bb.bb_instructions`) >> simp[] >> strip_tac >>
  gvs[] >>
  irule current_annotation_member_site >> metis_tac[]
QED

Theorem current_certificate_event_output_annotation:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\ MEM ev events /\
  lookup_block (current_event_label ev) fn'.fn_blocks = SOME out /\
  MEM n (FLAT (MAP (\i. i.inst_outputs) out.bb_instructions)) ==>
  ?t w. MEM (t,w,n) H /\ MEM (t,w) (FLAT (A (current_event_label ev)))
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
  drule_all current_tree_event_output_annotation >> simp[]
QED

Theorem current_certificate_output_site:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  lookup_block l fn'.fn_blocks = SOME out /\
  MEM n (FLAT (MAP (\i. i.inst_outputs) out.bb_instructions)) ==>
  ?t w. MEM (t,w,n) H /\
    current_changing_site fn (current_actual_inserted fn) w l
Proof
  strip_tac >>
  `MEM l (fn_labels fn')` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `MEM l (fn_labels fn)` by metis_tac[current_certificate_output_labels] >>
  `?old. lookup_block l fn.fn_blocks = SOME old` by
    (gvs[fn_labels_def, MEM_MAP] >>
     metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def]) >>
  drule_all current_certificate_event_at >> strip_tac >>
  qpat_x_assum `current_event_label ev = l` (SUBST_ALL_TAC o SYM) >>
  drule_all current_certificate_event_output_annotation >> strip_tac >>
  qexistsl_tac [`t`, `w`] >> simp[] >>
  irule current_certificate_annotation_site >> metis_tac[]
QED

Theorem current_certificate_clean_output_excludes:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  current_history_valid U H /\ MEM v U /\
  lookup_block l fn'.fn_blocks = SOME out /\
  ~current_changing_site fn (current_actual_inserted fn) v l /\
  MEM n (FLAT (MAP (\i. i.inst_outputs) out.bb_instructions)) /\
  current_owner_name H v n ==> F
Proof
  strip_tac >> drule_all current_certificate_output_site >> strip_tac >>
  `MEM w U` by metis_tac[current_history_owner_covered] >>
  `current_owner_name H w n` by metis_tac[current_owner_name_def] >>
  `w = v` by metis_tac[current_owner_name_separate] >> gvs[]
QED

Theorem current_phase_occurs_output_block:
  current_phase_occurs fn phase /\ MEM n (current_phase_outputs phase) ==>
  ?l bb. lookup_block l fn.fn_blocks = SOME bb /\
    MEM n (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    (case phase of CurrentBatch label phis => l = label
      | CurrentOrdinary label idx inst => l = label | CurrentControl => F)
Proof
  Cases_on `phase` >>
  simp[current_phase_occurs_def, current_phase_outputs_def] >> rpt strip_tac
  >- (goal_assum $ drule_at Any >> simp[] >>
      gvs[MEM_FLAT, MEM_MAP] >> metis_tac[TAKE_DROP, MEM_APPEND]) >>
  goal_assum $ drule_at Any >> simp[] >>
  gvs[get_instruction_def, AllCaseEqs()] >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[EL_MEM]
QED

Theorem current_restricted_prefix_owner_exclusion:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  current_history_valid U H /\ MEM v U /\
  current_actual_prefix fn' ctx loc before phases next result after /\
  current_restricted_path fn v labels /\
  EVERY (\phase. case phase of CurrentBatch l phis => MEM l labels
    | CurrentOrdinary l i inst => MEM l labels | CurrentControl => T) phases ==>
  !phase n w. MEM phase phases /\ MEM n (current_phase_outputs phase) /\
    current_owner_name H w n ==> w <> v
Proof
  strip_tac >> drule_then assume_tac current_actual_prefix_occurs >>
  map_every qx_gen_tac [`phase`, `n`, `w`] >> strip_tac >>
  `current_phase_occurs fn' phase` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all current_phase_occurs_output_block >> strip_tac >>
  `MEM l labels` by
    (qpat_x_assum `EVERY (\p. case p of CurrentBatch l ps => _ | CurrentOrdinary l i inst => _ | CurrentControl => _) phases` mp_tac >>
     simp[EVERY_MEM] >> disch_then (qspec_then `phase` mp_tac) >>
     simp[] >> Cases_on `phase` >> gvs[]) >>
  `~current_changing_site fn (current_actual_inserted fn) v l` by
    (gvs[current_restricted_path_def, EVERY_MEM] >> metis_tac[]) >>
  strip_tac >> gvs[] >> metis_tac[current_certificate_clean_output_excludes]
QED
