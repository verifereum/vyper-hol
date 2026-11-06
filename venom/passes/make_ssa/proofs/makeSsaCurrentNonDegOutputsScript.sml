Theory makeSsaCurrentNonDegOutputs
Ancestors
  makeSsaCurrentRenameTrace makeSsaCurrentAllocation makeSsaCurrentTreeTrace
  makeSsaCurrentFinalBlock makeSsaCurrentTreePaths list

Theorem current_nondeg_local_trace_outputs:
  !annss insts s rs H E insts' s' rs' H' E' V.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' /\
  current_annotations_ok V H (FLAT annss) /\
  current_allocation_consistent V H s rs /\ current_env_realizes H E rs V ==>
  LIST_REL (\anns inst.
    LIST_REL (\(t,v) n. current_token_name H' t = SOME n) anns inst.inst_outputs)
    annss insts'
Proof
  Induct >> simp[current_local_trace_def] >> rpt gen_tac >> strip_tac >>
  `current_annotations_ok V H h` by
    metis_tac[current_annotations_split, FLAT] >>
  `current_allocation_consistent V H1 s1 rs1 /\ current_env_realizes H1 E1 rs1 V` by
    (irule current_inst_trace_preserves >> metis_tac[]) >>
  `current_annotations_ok V H1 (FLAT annss)` by
    (fs[current_inst_trace_def] >>
     irule current_outputs_trace_remaining >> metis_tac[FLAT]) >>
  `LIST_REL (\(t,v) n. current_token_name H1 t = SOME n) h inst1.inst_outputs` by
    metis_tac[current_inst_trace_outputs] >>
  `?tail. H' = H1 ++ tail` by metis_tac[current_local_trace_history] >>
  simp[] >> conj_tac
  >- (fs[listTheory.LIST_REL_EL_EQN] >> rpt strip_tac >>
      qpat_x_assum `!n. n < LENGTH h ==> _`
        (qspec_then `n` mp_tac) >>
      pairarg_tac >> simp[] >>
      disch_then (fn th => irule current_token_name_append_stable >> ACCEPT_TAC th)) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem current_nondeg_trace_final_outputs:
  current_tree_trace A sm tree s rs bbs H E visited ctrs' s' bbs' H' visited' events /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  EVERY (current_event_valid A V) events /\ MEM ev events ==>
  ?new. lookup_block (current_event_label ev) bbs' = SOME new /\
    LIST_REL (\anns inst.
      LIST_REL (\(t,v) n. current_token_name H' t = SOME n) anns inst.inst_outputs)
      (A (current_event_label ev)) new.bb_instructions
Proof
  strip_tac >>
  `current_event_trace A H' ev /\ current_event_valid A V ev` by
    metis_tac[cj 1 current_tree_trace_events, EVERY_MEM] >>
  `?before after. events = before ++ ev::after` by metis_tac[MEM_SPLIT] >>
  drule_all current_trace_final_event >> strip_tac >>
  qexists `current_replay_edges sm (ev::after) (current_event_renamed_block ev)` >>
  conj_tac >- simp[] >>
  `LIST_REL (\anns inst.
      LIST_REL (\(t,v) n. current_token_name H' t = SOME n) anns inst.inst_outputs)
      (A (current_event_label ev))
      (current_event_renamed_block ev).bb_instructions` suffices_by
    (simp[GSYM LIST_REL_MAP2, current_replay_edges_outputs]) >>
  PairCases_on `ev` >>
  gvs[current_event_trace_def, current_event_valid_def,
      current_event_label_def, current_event_renamed_block_def] >>
  drule_all current_nondeg_local_trace_outputs >>
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `n'` mp_tac) >> simp[] >>
  pairarg_tac >> simp[] >>
  disch_then (fn th => irule current_token_name_append_stable >> ACCEPT_TAC th)
QED
