Theory makeSsaRfFinalBlock
Ancestors makeSsaRfTreeTrace makeSsaRfEdgeShape makeSsaRfAnnotations
  makeSsaCurrentInduct makeSsaCurrentDefs makeSsaDefs makeSsaHelper
  cfgTransformProps list pair rich_list

Definition current_event_label_def:
  current_event_label (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,bbs1,bbs2) = l
End

Definition current_event_renamed_block_def:
  current_event_renamed_block (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,bbs1,bbs2) =
    bb with bb_instructions := ren
End

Definition current_event_lookup_def:
  current_event_lookup sm q prior ev =
    if q = current_event_label ev then
      SOME (current_event_edge sm ev (current_event_renamed_block ev))
    else OPTION_MAP (current_event_edge sm ev) prior
End

Theorem current_trace_event_labels:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    !l. MEM l (MAP current_event_label events) ==> MEM l (dom_tree_labels tree)) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    !l. MEM l (MAP current_event_label events) ==>
      MEM l (FLAT (MAP dom_tree_labels trees)))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      simp[current_event_label_def, dom_tree_labels_def] >>
      first_x_assum drule >> metis_tac[])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >> simp[] >> metis_tac[]
QED

Theorem current_trace_event_labels_distinct:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events /\ ALL_DISTINCT (dom_tree_labels tree) ==>
    ALL_DISTINCT (MAP current_event_label events)) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events /\
      ALL_DISTINCT (FLAT (MAP dom_tree_labels trees)) ==>
    ALL_DISTINCT (MAP current_event_label events))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      fs[dom_tree_labels_def] >> simp[current_event_label_def] >>
      drule (cj 2 current_trace_event_labels) >>
      first_x_assum drule_all >> metis_tac[])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >> fs[ALL_DISTINCT_APPEND] >>
  drule (cj 1 current_trace_event_labels) >>
  drule (cj 2 current_trace_event_labels) >>
  simp[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem current_trace_lookup_fold:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    !q. lookup_block q bbs' =
      FOLDL (current_event_lookup sm q) (lookup_block q bbs) events) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    !q. lookup_block q bbs' =
      FOLDL (current_event_lookup sm q) (lookup_block q bbs) events)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      first_x_assum drule >> strip_tac >> gen_tac >>
      simp[current_event_lookup_def, current_event_label_def,
        current_event_edge_def, current_event_renamed_block_def] >>
      `x.bb_label = lbl` by metis_tac[lookup_block_label] >>
      Cases_on `q = lbl` >>
      simp[current_succ_phis_fold_lookup_option,
        lookup_block_replace_eq, lookup_block_replace_neq])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[FOLDL_APPEND]
QED

Theorem current_unvisited_lookup_fold:
  !events bb.
    ~MEM q (MAP current_event_label events) ==>
    FOLDL (current_event_lookup sm q) (SOME bb) events =
      SOME (current_replay_edges sm events bb)
Proof
  Induct >> simp[current_replay_edges_def] >> rpt strip_tac >>
  simp[current_event_lookup_def] >> simp[GSYM current_replay_edges_def]
QED

Theorem current_event_suffix_fold:
  ~MEM (current_event_label ev) (MAP current_event_label after) ==>
  FOLDL (current_event_lookup sm (current_event_label ev)) initial
    (before ++ ev::after) =
    SOME (current_replay_edges sm (ev::after) (current_event_renamed_block ev))
Proof
  strip_tac >> simp[FOLDL_APPEND, current_event_lookup_def] >>
  simp[Once current_replay_edges_def] >> simp[GSYM current_replay_edges_def] >>
  irule current_unvisited_lookup_fold >> simp[]
QED

Theorem current_trace_final_event:
  current_tree_trace A sm tree s rs bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  ALL_DISTINCT (dom_tree_labels tree) /\ events = before ++ ev::after ==>
  lookup_block (current_event_label ev) bbs' =
    SOME (current_replay_edges sm (ev::after) (current_event_renamed_block ev))
Proof
  strip_tac >> drule (cj 1 current_trace_lookup_fold) >> strip_tac >>
  drule_all (cj 1 current_trace_event_labels_distinct) >>
  simp[ALL_DISTINCT_APPEND] >> strip_tac >>
  simp[] >> irule current_event_suffix_fold >> simp[]
QED

Theorem current_trace_unvisited_lookup:
  current_tree_trace A sm tree s rs bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  lookup_block q bbs = SOME bb /\ ~MEM q (MAP current_event_label events) ==>
  lookup_block q bbs' = SOME (current_replay_edges sm events bb)
Proof
  strip_tac >> drule (cj 1 current_trace_lookup_fold) >>
  disch_then (qspec_then `q` mp_tac) >> simp[current_unvisited_lookup_fold]
QED

Theorem current_children_unvisited_lookup:
  current_children_trace A sm trees s ctrs stacks bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  lookup_block q bbs = SOME bb /\ ~MEM q (MAP current_event_label events) ==>
  lookup_block q bbs' = SOME (current_replay_edges sm events bb)
Proof
  strip_tac >> drule (cj 2 current_trace_lookup_fold) >>
  disch_then (qspec_then `q` mp_tac) >> simp[current_unvisited_lookup_fold]
QED

Definition current_event_input_block_def:
  current_event_input_block
    (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,
     (bbs1 : basic_block list),(bbs2 : basic_block list)) = bb
End

Theorem current_trace_event_input_shape:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    ALL_DISTINCT (MAP current_event_label events) ==>
    !ev old. MEM ev events /\ lookup_block (current_event_label ev) bbs = SOME old ==>
      current_edge_shape old (current_event_input_block ev)) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    ALL_DISTINCT (MAP current_event_label events) ==>
    !ev old. MEM ev events /\ lookup_block (current_event_label ev) bbs = SOME old ==>
      current_edge_shape old (current_event_input_block ev))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      simp[current_event_label_def] >> rpt strip_tac
      >- (gvs[current_event_label_def, current_event_input_block_def] >>
          simp[current_edge_shape_refl]) >>
      `current_event_label ev <> lbl` by metis_tac[MEM_MAP] >>
      `x.bb_label = lbl` by metis_tac[lookup_block_label] >>
      `lookup_block (current_event_label ev)
         (replace_block lbl (x with bb_instructions := insts1) bbs) = SOME old` by
        simp[lookup_block_replace_neq] >>
      drule current_succ_phis_fold_lookup >> strip_tac >>
      first_x_assum drule >> disch_then drule >> strip_tac >>
      metis_tac[current_edge_shape_trans, current_block_edge_fold_shape])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  simp[ALL_DISTINCT_APPEND, MEM_MAP] >> rpt strip_tac
  >- (first_x_assum drule >> disch_then drule >> metis_tac[]) >>
  `~MEM (current_event_label ev) (MAP current_event_label events1)` by
    metis_tac[MEM_MAP] >>
  `lookup_block (current_event_label ev) bbs1 =
     SOME (current_replay_edges sm events1 old)` by
    metis_tac[current_trace_unvisited_lookup] >>
  `current_edge_shape (current_replay_edges sm events1 old)
     (current_event_input_block ev)` by metis_tac[] >>
  metis_tac[current_edge_shape_trans, current_replay_edges_shape]
QED

Theorem current_trace_final_block:
  current_tree_trace A sm tree s rs bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  EVERY (current_event_names H' V) events /\
  lookup_block q bbs = SOME old /\ lookup_block q bbs' = SOME final ==>
  current_edge_shape old final \/
  ?ev. MEM ev events /\ current_event_label ev = q /\
    current_edge_shape old (current_event_input_block ev) /\
    current_event_trace A H' ev /\ current_event_names H' V ev /\
    current_edge_shape (current_event_renamed_block ev) final
Proof
  strip_tac >> Cases_on `MEM q (MAP current_event_label events)`
  >- (disj2_tac >>
      `?ev. MEM ev events /\ current_event_label ev = q` by
        metis_tac[MEM_MAP] >>
      qexists_tac `ev` >> simp[] >>
      `ALL_DISTINCT (MAP current_event_label events)` by
        metis_tac[cj 1 current_trace_event_labels_distinct] >>
      `current_edge_shape old (current_event_input_block ev)` by
        metis_tac[cj 1 current_trace_event_input_shape] >>
      `current_event_trace A H' ev` by
        metis_tac[cj 1 current_tree_trace_events, EVERY_MEM] >>
      `current_event_names H' V ev` by fs[EVERY_MEM] >> simp[] >>
      `?before after. events = before ++ ev::after` by metis_tac[MEM_SPLIT] >>
      `lookup_block (current_event_label ev) bbs' =
         SOME (current_replay_edges sm (ev::after) (current_event_renamed_block ev))` by
        metis_tac[current_trace_final_event] >>
      gvs[] >> simp[current_replay_edges_shape]) >>
  disj1_tac >>
  `lookup_block q bbs' = SOME (current_replay_edges sm events old)` by
    metis_tac[current_trace_unvisited_lookup] >>
  gvs[] >> simp[current_replay_edges_shape]
QED
