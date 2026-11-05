Theory makeSsaCurrentPreorderHistory
Ancestors makeSsaCurrentTraceHistory makeSsaCurrentTreePaths
  makeSsaCurrentFinalBlock makeSsaCurrentTreeTrace list

Definition current_preorder_history_def:
  current_preorder_history A labels bbs = FLAT (MAP (\l.
    current_local_delta (A l)
      (case lookup_block l bbs of NONE => [] | SOME bb => bb.bb_instructions)) labels)
End

Theorem current_local_delta_outputs:
  !xs ys aa.
    LENGTH aa = LENGTH xs /\
    MAP instruction_inst_outputs xs = MAP instruction_inst_outputs ys ==>
    current_local_delta aa xs = current_local_delta aa ys
Proof
  Induct_on `xs` >> rpt gen_tac >> Cases_on `ys` >> simp[] >>
  strip_tac >> Cases_on `aa` >> gvs[current_local_delta_def] >>
  first_x_assum irule >> simp[]
QED

Theorem current_event_trace_arity:
  current_event_trace A H ev ==>
  LENGTH (A (current_event_label ev)) =
    LENGTH (current_event_renamed_block ev).bb_instructions
Proof
  PairCases_on `ev` >>
  simp[current_event_trace_def, current_event_label_def,
       current_event_renamed_block_def] >>
  rpt strip_tac >> drule current_local_trace_delta >> simp[]
QED

Theorem current_trace_event_outputs:
  current_tree_trace A sm tree s rs bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  ALL_DISTINCT (dom_tree_labels tree) /\ MEM ev events ==>
  ?bb. lookup_block (current_event_label ev) bbs' = SOME bb /\
    MAP instruction_inst_outputs bb.bb_instructions =
    MAP instruction_inst_outputs (current_event_renamed_block ev).bb_instructions
Proof
  rpt strip_tac >>
  `?before after. events = before ++ ev::after` by metis_tac[MEM_SPLIT] >>
  drule_all current_trace_final_event >> strip_tac >>
  simp[current_replay_edges_outputs]
QED

Theorem current_event_delta_final_lookup:
  current_tree_trace A sm tree s rs bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  ALL_DISTINCT (dom_tree_labels tree) /\ MEM ev events ==>
  current_event_delta A ev =
    current_local_delta (A (current_event_label ev))
      (case lookup_block (current_event_label ev) bbs' of
         NONE => [] | SOME bb => bb.bb_instructions)
Proof
  strip_tac >> drule_all current_trace_event_outputs >> strip_tac >>
  drule (cj 1 current_tree_trace_events) >>
  simp[EVERY_MEM] >> strip_tac >>
  `current_event_trace A H' ev` by metis_tac[] >>
  drule current_event_trace_arity >> strip_tac >>
  simp[] >>
  `current_local_delta (A (current_event_label ev))
     (current_event_renamed_block ev).bb_instructions =
   current_local_delta (A (current_event_label ev)) bb.bb_instructions` by
    (irule current_local_delta_outputs >> simp[]) >>
  PairCases_on `ev` >>
  gvs[current_event_delta_def, current_event_label_def,
      current_event_renamed_block_def]
QED

Theorem current_tree_trace_preorder_history:
  current_tree_trace A sm tree s rs bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  (!l. MEM l (dom_tree_labels tree) ==> IS_SOME (lookup_block l bbs)) ==>
  H' = H ++ current_preorder_history A (dom_tree_labels tree) bbs'
Proof
  strip_tac >>
  drule_all (cj 1 current_tree_trace_event_labels) >> strip_tac >>
  drule (cj 1 current_tree_trace_delta) >> strip_tac >>
  simp[current_preorder_history_def] >>
  qpat_x_assum `MAP current_event_label events = _`
    (fn th => rewrite_tac[GSYM th]) >>
  rewrite_tac[MAP_MAP_o, combinTheory.o_DEF] >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[] >>
  rpt strip_tac >> irule current_event_delta_final_lookup >>
  metis_tac[]
QED

Theorem current_preorder_history_nil[simp]:
  current_preorder_history A [] bbs = []
Proof
  simp[current_preorder_history_def]
QED

Theorem current_preorder_history_cons_some:
  lookup_block l bbs = SOME bb ==>
  current_preorder_history A (l::ls) bbs =
    current_local_delta (A l) bb.bb_instructions ++
    current_preorder_history A ls bbs
Proof
  simp[current_preorder_history_def]
QED

Theorem current_preorder_history_cons_none:
  lookup_block l bbs = NONE ==>
  current_preorder_history A (l::ls) bbs =
    current_local_delta (A l) [] ++ current_preorder_history A ls bbs
Proof
  simp[current_preorder_history_def]
QED
