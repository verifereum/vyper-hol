Theory makeSsaRfFinalBlock
Ancestors makeSsaCurrentFinalBlock makeSsaCurrentSourceCuts makeSsaCurrentTreePaths makeSsaCurrentTreeTrace
  makeSsaRfTreeTrace makeSsaRfEdgeShape makeSsaRfAnnotations
  makeSsaCurrentInduct makeSsaDefs
  cfgTransformProps list pair rich_list
  venomExecProofs










Theorem rf_current_trace_unvisited_lookup:
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



Theorem current_trace_final_block:
  current_tree_trace A sm tree s rs bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  EVERY (rf_current_event_names H' V) events /\
  lookup_block q bbs = SOME old /\ lookup_block q bbs' = SOME final ==>
  current_edge_shape old final \/
  ?ev. MEM ev events /\ current_event_label ev = q /\
    current_edge_shape old (current_event_input_block ev) /\
    current_event_trace A H' ev /\ rf_current_event_names H' V ev /\
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
      `rf_current_event_names H' V ev` by fs[EVERY_MEM] >> simp[] >>
      `?before after. events = before ++ ev::after` by metis_tac[MEM_SPLIT] >>
      `lookup_block (current_event_label ev) bbs' =
         SOME (current_replay_edges sm (ev::after) (current_event_renamed_block ev))` by
        metis_tac[current_trace_final_event] >>
      gvs[] >> simp[current_replay_edges_shape]) >>
  disj1_tac >>
  `lookup_block q bbs' = SOME (current_replay_edges sm events old)` by
    metis_tac[rf_current_trace_unvisited_lookup] >>
  gvs[] >> simp[current_replay_edges_shape]
QED
