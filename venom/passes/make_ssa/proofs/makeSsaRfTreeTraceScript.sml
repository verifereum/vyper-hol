Theory makeSsaRfTreeTrace
Ancestors makeSsaRfAnnotations makeSsaRfEdgeShape makeSsaRfAllocation
  makeSsaRfRenameTrace makeSsaCurrentInduct makeSsaCurrentDefs
  makeSsaCurrentProps makeSsaHelper cfgTransform cfgTransformProps
  makeSsaDefs irSupply list pair alist

Theorem current_allocation_consistent_restore:
  current_allocation_consistent V H' s'
    (ctrs',(stacks' : (string # string list) list)) /\
  ssa_stacks_covered s (stacks : (string # string list) list) /\ ssa_supply_extends s s' ==>
  current_allocation_consistent V H' s' (ctrs',stacks)
Proof
  simp[current_allocation_consistent_def, current_counter_def] >>
  metis_tac[ssa_stacks_covered_mono]
QED

Theorem current_sibling_restore:
  current_env_realizes H E ((ctrs : (string # num) list),stacks) V /\
  current_env_owned V H E /\
  current_allocation_consistent V (H ++ tail) s'
    (ctrs',(stacks' : (string # string list) list)) /\
  ssa_stacks_covered s stacks /\ ssa_supply_extends s s' ==>
  current_env_realizes (H ++ tail) E (ctrs',stacks) V /\
  current_env_owned V (H ++ tail) E /\
  current_allocation_consistent V (H ++ tail) s' (ctrs',stacks)
Proof
  metis_tac[current_env_realizes_restore, current_env_owned_append,
    current_allocation_consistent_restore, SND]
QED

Theorem current_unvisited_annotations_edge_step:
  current_unvisited_annotations A visited bbs ==>
  current_unvisited_annotations A visited (current_edge_step rs p bbs h)
Proof
  simp[current_unvisited_annotations_def, current_edge_step_lookup] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `lookup_block l bbs` >> simp[] >>
  Cases_on `l = h` >> simp[current_edge_block_def,
    current_annotations_edge_insts] >> metis_tac[]
QED

Theorem current_unvisited_annotations_succs:
  !succs bbs.
  current_unvisited_annotations A visited bbs ==>
  current_unvisited_annotations A visited
    (update_current_succ_phis rs p bbs succs)
Proof
  Induct >> simp[current_succ_phis_cons] >> rpt strip_tac >>
  first_x_assum irule >> irule current_unvisited_annotations_edge_step >> simp[]
QED

Theorem current_unvisited_annotations_visit:
  current_unvisited_annotations A visited bbs /\ bb.bb_label = l ==>
  current_unvisited_annotations A (l::visited) (replace_block l bb bbs)
Proof
  simp[current_unvisited_annotations_def] >> rpt strip_tac >>
  drule lookup_block_replace_neq >> strip_tac >> metis_tac[]
QED

Definition current_tree_trace_def:
  (current_tree_trace (A : string -> (current_token # string) list list) sm (DNode l children) s rs bbs H E visited
      ctrs' s' bbs' H' visited' events <=>
    case lookup_block l bbs of
      NONE => ctrs' = FST rs /\ s' = s /\ bbs' = bbs /\
              H' = H /\ visited' = visited /\ events = []
    | SOME bb =>
      ?insts1 rs1 s1 H1 E1 bbs1 bbs2 succs rest_events.
        current_local_trace (A l) bb.bb_instructions s rs H E
          insts1 s1 rs1 H1 E1 /\
        bbs1 = replace_block l (bb with bb_instructions := insts1) bbs /\
        succs = (case ALOOKUP sm l of NONE => [] | SOME ss => ss) /\
        bbs2 = update_current_succ_phis rs1 l bbs1 succs /\
        events = (l,bb,s,rs,H,E,insts1,s1,rs1,H1,E1,bbs1,bbs2)::rest_events /\
        current_children_trace A sm children s1 (FST rs1) (SND rs1)
          bbs2 H1 E1 (l::visited) ctrs' s' bbs' H' visited' rest_events) /\
  (current_children_trace A sm [] s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events <=>
    ctrs' = ctrs /\ s' = s /\ bbs' = bbs /\ H' = H /\
    visited' = visited /\ events = []) /\
  (current_children_trace A sm (child::rest) s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events <=>
    ?ctrs1 s1 bbs1 H1 visited1 events1 events2.
      current_tree_trace A sm child s (ctrs,stacks) bbs H E visited
        ctrs1 s1 bbs1 H1 visited1 events1 /\
      current_children_trace A sm rest s1 ctrs1 stacks bbs1 H1 E visited1
        ctrs' s' bbs' H' visited' events2 /\ events = events1 ++ events2)
End

Theorem current_tree_trace_projection:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    rename_current_blocks s rs bbs sm tree = (ctrs',s',bbs')) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    rename_current_children s ctrs stacks bbs sm trees = (ctrs',s',bbs'))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def, Once rename_current_blocks_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      drule current_local_trace_projection >> strip_tac >> simp[] >>
      first_x_assum drule >> simp[])
  >- simp[current_tree_trace_def, rename_current_blocks_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def, Once rename_current_blocks_def] >>
  strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> simp[] >>
  first_x_assum drule >> simp[]
QED

Theorem current_tree_trace_history:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events ==> ?tail. H' = H ++ tail) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events ==> ?tail. H' = H ++ tail)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      drule current_local_trace_history >> strip_tac >>
      first_x_assum drule >> strip_tac >> gvs[] >>
      metis_tac[APPEND_ASSOC])
  >- (simp[current_tree_trace_def] >> metis_tac[APPEND_NIL]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  metis_tac[APPEND_ASSOC]
QED

Theorem current_tree_trace_unvisited:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    current_unvisited_annotations A visited bbs ==>
    current_unvisited_annotations A visited' bbs') /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    current_unvisited_annotations A visited bbs ==>
    current_unvisited_annotations A visited' bbs')
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      `current_unvisited_annotations A (lbl::visited)
        (replace_block lbl (x with bb_instructions := insts1) bbs)` by
        (irule current_unvisited_annotations_visit >> simp[] >>
         metis_tac[lookup_block_label]) >>
      drule current_unvisited_annotations_succs >>
      disch_then assume_tac >>
      first_x_assum irule >> metis_tac[])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem current_tree_trace_visited:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    !l. MEM l visited' ==> MEM l visited \/ MEM l (dom_tree_labels tree)) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    !l. MEM l visited' ==> MEM l visited \/ MEM l (FLAT (MAP dom_tree_labels trees)))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def, Once dom_tree_labels_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      first_x_assum drule >> simp[] >> metis_tac[])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem current_tree_trace_exists:
  (!tree A sm s rs bbs H E visited.
    ALL_DISTINCT (dom_tree_labels tree) /\
    (!l. MEM l (dom_tree_labels tree) ==> ~MEM l visited) /\
    current_unvisited_annotations A visited bbs ==>
    ?ctrs' s' bbs' H' visited' events.
      current_tree_trace A sm tree s rs bbs H E visited
        ctrs' s' bbs' H' visited' events) /\
  (!trees A sm s ctrs stacks bbs H E visited.
    ALL_DISTINCT (FLAT (MAP dom_tree_labels trees)) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels trees)) ==> ~MEM l visited) /\
    current_unvisited_annotations A visited bbs ==>
    ?ctrs' s' bbs' H' visited' events.
      current_children_trace A sm trees s ctrs stacks bbs H E visited
        ctrs' s' bbs' H' visited' events)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `lookup_block lbl bbs`
      >- simp[current_tree_trace_def] >>
      rename1 `lookup_block lbl bbs = SOME bb` >>
      `LIST_REL (\anns inst. MAP SND anns = inst.inst_outputs)
        (A lbl) bb.bb_instructions` by
        (fs[current_unvisited_annotations_def, Once dom_tree_labels_def] >>
         metis_tac[]) >>
      Cases_on `rename_current_block_insts s rs bb.bb_instructions` >>
      PairCases_on `r` >>
      `?H1 E1. current_local_trace (A lbl) bb.bb_instructions s rs H E
        r1 r0 q H1 E1` by
        (irule current_local_trace_exists >> simp[]) >>
      qabbrev_tac `bs1 = replace_block lbl (bb with bb_instructions := r1) bbs` >>
      qabbrev_tac `ss = case ALOOKUP sm lbl of NONE => [] | SOME ls => ls` >>
      qabbrev_tac `bs2 = update_current_succ_phis q lbl bs1 ss` >>
      `current_unvisited_annotations A (lbl::visited) bs2` by
        (simp[Abbr `bs2`] >> irule current_unvisited_annotations_succs >>
         simp[Abbr `bs1`] >> irule current_unvisited_annotations_visit >>
         simp[] >> metis_tac[lookup_block_label]) >>
      `ALL_DISTINCT (FLAT (MAP dom_tree_labels trees)) /\
        (!l. MEM l (FLAT (MAP dom_tree_labels trees)) ==> ~MEM l (lbl::visited))` by
        (fs[dom_tree_labels_def, ALL_DISTINCT_APPEND, EVERY_MEM] >> metis_tac[]) >>
      `?ctrs' s' bbs' H' visited' events.
        current_children_trace A sm trees r0 (FST q) (SND q) bs2 H1 E1
          (lbl::visited) ctrs' s' bbs' H' visited' events` by
        (first_x_assum irule >> simp[]) >>
      simp[current_tree_trace_def] >>
      qexistsl_tac [`ctrs'`, `s'`, `bbs'`, `H'`, `visited'`,
        `r1`, `q`, `r0`, `H1`, `E1`, `events`] >>
      gvs[Abbr `bs2`, Abbr `bs1`])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (dom_tree_labels tree) /\
    (!l. MEM l (dom_tree_labels tree) ==> ~MEM l visited)` by
    fs[ALL_DISTINCT_APPEND, EVERY_MEM] >>
  `?ctrs1 s1 bbs1 H1 visited1 events1.
    current_tree_trace A sm tree s (ctrs,stacks) bbs H E visited
      ctrs1 s1 bbs1 H1 visited1 events1` by
    (first_x_assum irule >> simp[]) >>
  `current_unvisited_annotations A visited1 bbs1` by
    metis_tac[current_tree_trace_unvisited] >>
  `!l. MEM l visited1 ==> MEM l visited \/ MEM l (dom_tree_labels tree)` by
    metis_tac[current_tree_trace_visited] >>
  `ALL_DISTINCT (FLAT (MAP dom_tree_labels trees)) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels trees)) ==> ~MEM l visited1)` by
    (fs[ALL_DISTINCT_APPEND, EVERY_MEM] >> metis_tac[]) >>
  `?ctrs' s' bbs' H' visited' events2.
    current_children_trace A sm trees s1 ctrs1 stacks bbs1 H1 E visited1
      ctrs' s' bbs' H' visited' events2` by
    (first_x_assum irule >> simp[]) >>
  simp[current_tree_trace_def] >>
  qexistsl_tac [`ctrs'`, `s'`, `bbs'`, `H'`, `visited'`] >> metis_tac[]
QED

Theorem current_tree_trace_for_result:
  ALL_DISTINCT (dom_tree_labels tree) /\
  (!l. MEM l (dom_tree_labels tree) ==> ~MEM l visited) /\
  current_unvisited_annotations A visited bbs /\
  rename_current_blocks s rs bbs sm tree = (ctrs',s',bbs') ==>
  ?H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events
Proof
  strip_tac >>
  `?ctrs1 s1 bbs1 H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs1 s1 bbs1 H' visited' events` by
    (irule (cj 1 current_tree_trace_exists) >> simp[]) >>
  drule (cj 1 current_tree_trace_projection) >> strip_tac >> gvs[] >> metis_tac[]
QED
Theorem current_outputs_trace_keys:
  !anns s rs H E names s' rs' H' E'.
  current_outputs_trace anns s rs H E names s' rs' H' E' ==>
  MAP FST H' = MAP FST H ++ MAP FST anns
Proof
  Induct >> simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[MAP_APPEND, APPEND_ASSOC]
QED

Theorem current_local_trace_keys:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  MAP FST H' = MAP FST H ++ MAP FST (FLAT annss)
Proof
  Induct >> simp[current_local_trace_def] >> rpt strip_tac >>
  fs[current_inst_trace_def] >>
  drule current_outputs_trace_keys >> strip_tac >>
  first_x_assum drule >> simp[MAP_APPEND, APPEND_ASSOC]
QED


Theorem current_pending_annotations_visit:
  current_pending_annotations V A H visited /\
  current_annotation_separation A /\
  MAP FST H1 = MAP FST H ++ MAP FST (FLAT (A l)) ==>
  current_pending_annotations V A H1 (l::visited)
Proof
  rw[current_pending_annotations_def] >>
  `current_annotations_ok V H (FLAT (A l'))` by
    metis_tac[current_pending_annotations_def] >>
  gvs[current_annotations_ok_def, EVERY_MEM, pairTheory.FORALL_PROD] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[current_annotation_separation_def, MEM_MAP, FST]
QED

Theorem current_tree_trace_pending:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events V.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    current_pending_annotations V A H visited /\ current_annotation_separation A ==>
    current_pending_annotations V A H' visited') /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events V.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    current_pending_annotations V A H visited /\ current_annotation_separation A ==>
    current_pending_annotations V A H' visited')
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      drule current_local_trace_keys >> strip_tac >>
      first_x_assum irule >> metis_tac[current_pending_annotations_visit])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem current_tree_trace_extends:
  current_tree_trace A sm tree s rs bbs H E visited
    ctrs' s' bbs' H' visited' events ==> ssa_supply_extends s s'
Proof
  strip_tac >> drule (cj 1 current_tree_trace_projection) >>
  metis_tac[cj 1 rename_current_blocks_extends]
QED

Theorem current_children_trace_extends:
  current_children_trace A sm trees s ctrs stacks bbs H E visited
    ctrs' s' bbs' H' visited' events ==> ssa_supply_extends s s'
Proof
  strip_tac >> drule (cj 2 current_tree_trace_projection) >>
  metis_tac[cj 2 rename_current_blocks_extends]
QED

Theorem current_tree_trace_preserves:
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
      drule_all current_sibling_restore >> simp[])
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

Definition current_event_trace_def:
  current_event_trace (A : string -> (current_token # string) list list) finalH
    (l,bb,s,rs,H,E,insts1,s1,rs1,H1,E1,
      (bbs1 : basic_block list),(bbs2 : basic_block list)) <=>
    current_local_trace (A l) bb.bb_instructions s rs H E
      insts1 s1 rs1 H1 E1 /\ ?tail. finalH = H1 ++ tail
End

Theorem current_event_trace_extend:
  current_event_trace A H ev ==> current_event_trace A (H ++ tail) ev
Proof
  PairCases_on `ev` >> simp[current_event_trace_def] >> metis_tac[APPEND_ASSOC]
QED

Theorem current_events_trace_extend:
  EVERY (current_event_trace A H) events ==>
  EVERY (current_event_trace A (H ++ tail)) events
Proof
  simp[EVERY_MEM] >> metis_tac[current_event_trace_extend]
QED

Theorem current_tree_trace_events:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    EVERY (current_event_trace A H') events) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    EVERY (current_event_trace A H') events)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      drule (cj 2 current_tree_trace_history) >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      simp[current_event_trace_def] >> metis_tac[])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  drule (cj 2 current_tree_trace_history) >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  simp[EVERY_APPEND] >> metis_tac[current_events_trace_extend]
QED

Definition current_event_valid_def:
  current_event_valid (A : string -> (current_token # string) list list) V
    (l,bb,s,rs,H,E,insts1,s1,rs1,H1,E1,
      (bbs1 : basic_block list),(bbs2 : basic_block list)) <=>
    current_annotations_ok V H (FLAT (A l)) /\
    current_allocation_consistent V H s rs /\ current_env_realizes H E rs V /\
    current_env_owned V H E
End

Theorem current_tree_trace_events_valid:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events V.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    ALL_DISTINCT (dom_tree_labels tree) /\
    (!l. MEM l (dom_tree_labels tree) ==> ~MEM l visited) /\
    current_pending_annotations V A H visited /\ current_annotation_separation A /\
    current_allocation_consistent V H s rs /\ current_env_realizes H E rs V /\
    current_env_owned V H E ==>
    EVERY (current_event_valid A V) events) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events V.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    ALL_DISTINCT (FLAT (MAP dom_tree_labels trees)) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels trees)) ==> ~MEM l visited) /\
    current_pending_annotations V A H visited /\ current_annotation_separation A /\
    current_allocation_consistent V H s (ctrs,stacks) /\
    current_env_realizes H E (ctrs,stacks) V /\ current_env_owned V H E ==>
    EVERY (current_event_valid A V) events)
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
      simp[current_event_valid_def] >>
      Cases_on `rs1` >> gvs[] >> first_x_assum drule >> simp[])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[current_tree_trace_def] >>
  `ALL_DISTINCT (dom_tree_labels tree) /\
    (!l. MEM l (dom_tree_labels tree) ==> ~MEM l visited)` by
    fs[ALL_DISTINCT_APPEND, EVERY_MEM] >>
  `current_allocation_consistent V H1 s1 (ctrs1,stacks) /\
    current_env_realizes H1 E (ctrs1,stacks) V /\ current_env_owned V H1 E` by
    (drule (cj 1 current_tree_trace_preserves) >> simp[]) >>
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

Definition current_event_names_def:
  current_event_names finalH V
    (l,bb,s,rs,H,E,insts1,s1,rs1,H1,E1,
      (bbs1 : basic_block list),(bbs2 : basic_block list)) <=>
    current_env_realizes finalH E rs V /\ current_env_realizes finalH E1 rs1 V /\
    current_env_owned V finalH E /\ current_env_owned V finalH E1
End

Theorem current_event_names_valid:
  current_event_valid A V ev /\ current_event_trace A finalH ev ==>
  current_event_names finalH V ev
Proof
  PairCases_on `ev` >>
  simp[current_event_valid_def, current_event_trace_def, current_event_names_def] >>
  rpt gen_tac >> strip_tac >>
  `current_allocation_consistent V ev11 ev8 (ev9,ev10) /\
    current_env_realizes ev11 ev12 (ev9,ev10) V` by
    (irule current_local_trace_preserves >> metis_tac[]) >>
  `current_env_owned V ev11 ev12` by metis_tac[current_local_trace_owned] >>
  drule current_local_trace_history >> strip_tac >> gvs[] >>
  metis_tac[current_env_realizes_append, current_env_owned_append, APPEND_ASSOC]
QED

Theorem current_events_names_valid:
  EVERY (current_event_valid A V) events /\
  EVERY (current_event_trace A finalH) events ==>
  EVERY (current_event_names finalH V) events
Proof
  simp[EVERY_MEM] >> metis_tac[current_event_names_valid]
QED

Theorem current_annotated_tree_names:
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
  EVERY (current_event_names H' V) events
Proof
  strip_tac >>
  `current_pending_annotations V (current_annotation_map bbs annsss) [] []` by
    metis_tac[current_annotation_map_pending] >>
  `current_annotation_separation (current_annotation_map bbs annsss)` by
    (irule current_annotation_map_separation >> fs[current_annotations_ok_def]) >>
  conj_tac
  >- (drule (cj 1 current_tree_trace_preserves) >> simp[] >>
      disch_then (qspec_then `V` mp_tac) >> metis_tac[]) >>
  irule current_events_names_valid >>
  qexists_tac `current_annotation_map bbs annsss` >> conj_tac
  >- (drule (cj 1 current_tree_trace_events) >> simp[]) >>
  drule (cj 1 current_tree_trace_events_valid) >> simp[] >>
  disch_then (qspec_then `V` mp_tac) >> simp[]
QED
