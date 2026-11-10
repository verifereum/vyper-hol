Theory makeSsaRfTreeTrace
Ancestors makeSsaCurrentAllocation makeSsaCurrentRenameTrace makeSsaCurrentTokens makeSsaCurrentTreeTrace
  makeSsaRfAnnotations makeSsaRfEdgeShape makeSsaRfAllocation
  makeSsaRfRenameTrace makeSsaCurrentInduct makeSsaDefs
  makeSsaCurrentProps cfgTransform cfgTransformProps
   irSupply list pair alist
  venomExecProofs


Theorem rf_current_sibling_restore:
  current_env_realizes H E ((ctrs : (string # num) list),stacks) V /\
  current_env_owned V H E /\
  current_allocation_consistent V (H ++ tail) s'
    (ctrs',(stacks' : (string # string list) list)) /\
  ssa_stacks_covered s stacks /\ ssa_supply_extends s s' ==>
  current_env_realizes (H ++ tail) E (ctrs',stacks) V /\
  current_env_owned V (H ++ tail) E /\
  current_allocation_consistent V (H ++ tail) s' (ctrs',stacks)
Proof
  metis_tac[rf_current_env_realizes_restore, current_env_owned_append,
    current_allocation_consistent_restore, SND]
QED

















Theorem rf_current_tree_trace_preserves:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events V.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    ALL_DISTINCT (dom_tree_labels tree) /\
    (!l. MEM l (dom_tree_labels tree) ==> ~MEM l visited) /\
    current_pending_annotations V A H visited /\ current_annotation_separation A /\
    current_allocation_consistent V H s rs /\ current_env_realizes H E rs V /\
    current_env_owned V H E ==>
    current_allocation_consistent V H' s' (ctrs',SND rs) /\
    current_env_realizes H' E (ctrs',SND rs) V /\ current_env_owned V H' E) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events V.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    ALL_DISTINCT (FLAT (MAP dom_tree_labels trees)) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels trees)) ==> ~MEM l visited) /\
    current_pending_annotations V A H visited /\ current_annotation_separation A /\
    current_allocation_consistent V H s (ctrs,stacks) /\
    current_env_realizes H E (ctrs,stacks) V /\ current_env_owned V H E ==>
    current_allocation_consistent V H' s' (ctrs',stacks) /\
    current_env_realizes H' E (ctrs',stacks) V /\ current_env_owned V H' E)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `lookup_block lbl bbs`
      >- gvs[current_tree_trace_def] >>
      gvs[current_tree_trace_def] >>
      `current_annotations_ok V H (FLAT (A lbl))` by
        (fs[current_pending_annotations_def, dom_tree_labels_def] >> metis_tac[]) >>
      `current_allocation_consistent V H1 s1 rs1 /\ current_env_realizes H1 E1 rs1 V` by
        (irule current_local_trace_preserves >> metis_tac[]) >>
      `current_env_owned V H1 E1` by metis_tac[current_local_trace_owned] >>
      `current_pending_annotations V A H1 (lbl::visited)` by
        (drule current_local_trace_keys >> strip_tac >>
         irule current_pending_annotations_visit >> simp[] >> qexists_tac `H` >> simp[]) >>
      `ALL_DISTINCT (FLAT (MAP dom_tree_labels trees)) /\
        (!l. MEM l (FLAT (MAP dom_tree_labels trees)) ==> ~MEM l (lbl::visited))` by
        (fs[dom_tree_labels_def, EVERY_MEM] >> metis_tac[]) >>
      `current_allocation_consistent V H' s' (ctrs',SND rs1)` by
        (Cases_on `rs1` >> gvs[] >> first_x_assum drule >> simp[]) >>
      `?tail. H' = H ++ tail` by
        (drule current_local_trace_history >> drule (cj 2 current_tree_trace_history) >>
         metis_tac[APPEND_ASSOC]) >>
      `ssa_supply_extends s s'` by
        (drule current_local_trace_projection >> drule current_children_trace_extends >>
         metis_tac[rename_current_block_insts_extends, ssa_supply_extends_trans]) >>
      `ssa_stacks_covered s (SND rs)` by fs[current_allocation_consistent_def] >>
      gvs[] >> Cases_on `rs` >> gvs[] >>
      drule_all rf_current_sibling_restore >> simp[])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[current_tree_trace_def] >>
  `ALL_DISTINCT (dom_tree_labels tree) /\
    (!l. MEM l (dom_tree_labels tree) ==> ~MEM l visited)` by
    fs[ALL_DISTINCT_APPEND, EVERY_MEM] >>
  `current_allocation_consistent V H1 s1 (ctrs1,stacks) /\
    current_env_realizes H1 E (ctrs1,stacks) V /\ current_env_owned V H1 E` by
    (first_x_assum drule_all >> simp[]) >>
  `current_pending_annotations V A H1 visited1` by
    metis_tac[cj 1 current_tree_trace_pending] >>
  `!l. MEM l visited1 ==> MEM l visited \/ MEM l (dom_tree_labels tree)` by
    metis_tac[cj 1 current_tree_trace_visited] >>
  `ALL_DISTINCT (FLAT (MAP dom_tree_labels trees)) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels trees)) ==> ~MEM l visited1)` by
    (fs[ALL_DISTINCT_APPEND, EVERY_MEM] >> metis_tac[]) >>
  first_x_assum drule_all >> simp[]
QED





Definition rf_current_event_valid_def:
  rf_current_event_valid (A : string -> (current_token # string) list list) V
    (l,bb,s,rs,H,E,insts1,s1,rs1,H1,E1,
      (bbs1 : basic_block list),(bbs2 : basic_block list)) <=>
    current_annotations_ok V H (FLAT (A l)) /\
    current_allocation_consistent V H s rs /\ current_env_realizes H E rs V /\
    current_env_owned V H E
End

Theorem rf_current_tree_trace_events_valid:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events V.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    ALL_DISTINCT (dom_tree_labels tree) /\
    (!l. MEM l (dom_tree_labels tree) ==> ~MEM l visited) /\
    current_pending_annotations V A H visited /\ current_annotation_separation A /\
    current_allocation_consistent V H s rs /\ current_env_realizes H E rs V /\
    current_env_owned V H E ==>
    EVERY (rf_current_event_valid A V) events) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events V.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    ALL_DISTINCT (FLAT (MAP dom_tree_labels trees)) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels trees)) ==> ~MEM l visited) /\
    current_pending_annotations V A H visited /\ current_annotation_separation A /\
    current_allocation_consistent V H s (ctrs,stacks) /\
    current_env_realizes H E (ctrs,stacks) V /\ current_env_owned V H E ==>
    EVERY (rf_current_event_valid A V) events)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `lookup_block lbl bbs`
      >- gvs[current_tree_trace_def] >>
      gvs[current_tree_trace_def] >>
      `current_annotations_ok V H (FLAT (A lbl))` by
        (fs[current_pending_annotations_def, dom_tree_labels_def] >> metis_tac[]) >>
      `current_allocation_consistent V H1 s1 rs1 /\ current_env_realizes H1 E1 rs1 V` by
        (irule current_local_trace_preserves >> metis_tac[]) >>
      `current_env_owned V H1 E1` by metis_tac[current_local_trace_owned] >>
      `current_pending_annotations V A H1 (lbl::visited)` by
        (drule current_local_trace_keys >> strip_tac >>
         irule current_pending_annotations_visit >> simp[] >> qexists_tac `H` >> simp[]) >>
      `ALL_DISTINCT (FLAT (MAP dom_tree_labels trees)) /\
        (!l. MEM l (FLAT (MAP dom_tree_labels trees)) ==> ~MEM l (lbl::visited))` by
        (fs[dom_tree_labels_def, EVERY_MEM] >> metis_tac[]) >>
      simp[rf_current_event_valid_def] >>
      Cases_on `rs1` >> gvs[] >> first_x_assum drule >> simp[])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[current_tree_trace_def] >>
  `ALL_DISTINCT (dom_tree_labels tree) /\
    (!l. MEM l (dom_tree_labels tree) ==> ~MEM l visited)` by
    fs[ALL_DISTINCT_APPEND, EVERY_MEM] >>
  `current_allocation_consistent V H1 s1 (ctrs1,stacks) /\
    current_env_realizes H1 E (ctrs1,stacks) V /\ current_env_owned V H1 E` by
    (drule (cj 1 rf_current_tree_trace_preserves) >> simp[]) >>
  `current_pending_annotations V A H1 visited1` by
    metis_tac[cj 1 current_tree_trace_pending] >>
  `!l. MEM l visited1 ==> MEM l visited \/ MEM l (dom_tree_labels tree)` by
    metis_tac[cj 1 current_tree_trace_visited] >>
  `ALL_DISTINCT (FLAT (MAP dom_tree_labels trees)) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels trees)) ==> ~MEM l visited1)` by
    (fs[ALL_DISTINCT_APPEND, EVERY_MEM] >> metis_tac[]) >>
  simp[EVERY_APPEND] >> conj_tac
  >- (qpat_x_assum `!A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events V. _ ==> EVERY _ _`
        drule >> simp[]) >>
  first_x_assum drule >> simp[]
QED

Definition rf_current_event_names_def:
  rf_current_event_names finalH V
    (l,bb,s,rs,H,E,insts1,s1,rs1,H1,E1,
      (bbs1 : basic_block list),(bbs2 : basic_block list)) <=>
    current_env_realizes finalH E rs V /\ current_env_realizes finalH E1 rs1 V /\
    current_env_owned V finalH E /\ current_env_owned V finalH E1
End

Theorem rf_current_event_names_valid:
  rf_current_event_valid A V ev /\ current_event_trace A finalH ev ==>
  rf_current_event_names finalH V ev
Proof
  PairCases_on `ev` >>
  simp[rf_current_event_valid_def, current_event_trace_def, rf_current_event_names_def] >>
  rpt gen_tac >> strip_tac >>
  `current_allocation_consistent V ev11 ev8 (ev9,ev10) /\
    current_env_realizes ev11 ev12 (ev9,ev10) V` by
    (irule current_local_trace_preserves >> metis_tac[]) >>
  `current_env_owned V ev11 ev12` by metis_tac[current_local_trace_owned] >>
  drule current_local_trace_history >> strip_tac >> gvs[] >>
  metis_tac[current_env_realizes_append, current_env_owned_append, APPEND_ASSOC]
QED

Theorem rf_current_events_names_valid:
  EVERY (rf_current_event_valid A V) events /\
  EVERY (current_event_trace A finalH) events ==>
  EVERY (rf_current_event_names finalH V) events
Proof
  simp[EVERY_MEM] >> metis_tac[rf_current_event_names_valid]
QED

Theorem rf_current_annotated_tree_names:
  LENGTH bbs = LENGTH annsss /\
  current_annotations_ok V ([] : (current_token # string # string) list)
    (FLAT (FLAT annsss)) /\
  current_allocation_consistent V [] s rs /\
  current_env_realizes ([] : (current_token # string # string) list) E rs V /\
  current_env_owned V ([] : (current_token # string # string) list) E /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s rs bbs [] E [] ctrs' s' bbs' H' visited' events ==>
  current_allocation_consistent V H' s' (ctrs',SND rs) /\
  EVERY (rf_current_event_names H' V) events
Proof
  strip_tac >>
  `current_pending_annotations V (current_annotation_map bbs annsss) [] []` by
    metis_tac[current_annotation_map_pending] >>
  `current_annotation_separation (current_annotation_map bbs annsss)` by
    (irule current_annotation_map_separation >> fs[current_annotations_ok_def]) >>
  conj_tac
  >- (drule (cj 1 rf_current_tree_trace_preserves) >> simp[] >>
      disch_then (qspec_then `V` mp_tac) >> metis_tac[]) >>
  irule rf_current_events_names_valid >>
  qexists_tac `current_annotation_map bbs annsss` >> conj_tac
  >- (drule (cj 1 current_tree_trace_events) >> simp[]) >>
  drule (cj 1 rf_current_tree_trace_events_valid) >> simp[] >>
  disch_then (qspec_then `V` mp_tac) >> simp[]
QED
