Theory makeSsaCurrentTreeTrace
Ancestors
  makeSsaCurrentCertificate makeSsaCurrentAllocation makeSsaCurrentRenameTrace
  makeSsaCurrentEdgeTrace makeSsaCurrentInduct makeSsaCurrentDefs
  makeSsaCurrentProps makeSsaDefs cfgTransform cfgTransformProps makeSsaHelper list pair

(* Sibling calls retain global counters/history but restore the lexical
   stacks and environment of their parent. These boundaries do not equate
   the sibling's final stacks with those of the parent. *)
Theorem current_env_realizes_restore:
  current_env_realizes H E (ctrs,stacks) V ==>
  current_env_realizes (H ++ tail) E (ctrs',stacks) V
Proof
  simp[current_env_realizes_def, latest_current_name_def] >>
  rpt strip_tac >> first_x_assum drule >>
  disch_then (mp_tac o MATCH_MP current_token_name_append_stable) >> simp[]
QED

Theorem current_allocation_consistent_restore:
  current_allocation_consistent V H' s' (ctrs',stacks') /\
  ssa_stacks_covered s stacks /\ ssa_supply_extends s s' ==>
  current_allocation_consistent V H' s' (ctrs',stacks)
Proof
  simp[current_allocation_consistent_def, current_counter_def] >>
  metis_tac[ssa_stacks_covered_mono]
QED

Theorem current_sibling_restore:
  current_env_realizes H E (ctrs,stacks) V /\
  current_allocation_consistent V (H ++ tail) s' (ctrs',stacks') /\
  ssa_stacks_covered s stacks /\ ssa_supply_extends s s' ==>
  current_env_realizes (H ++ tail) E (ctrs',stacks) V /\
  current_allocation_consistent V (H ++ tail) s' (ctrs',stacks)
Proof
  metis_tac[current_env_realizes_restore, current_allocation_consistent_restore]
QED

(* The same annotated allocation trace works whether an incoming predecessor
   has already updated this block's PHI slots or does so after block visitation. *)
Theorem current_inst_trace_edge:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' ==>
  current_inst_trace anns (current_edge_inst rt p inst) s rs H E
    (current_edge_inst rt p inst') s' rs' H' E'
Proof
  simp[current_inst_trace_def, current_edge_inst_def] >> rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
  qexists_tac `names` >> simp[]
QED

Theorem current_local_trace_edge:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  current_local_trace annss (MAP (current_edge_inst rt p) insts) s rs H E
    (MAP (current_edge_inst rt p) insts') s' rs' H' E'
Proof
  Induct >> simp[current_local_trace_def] >> rpt strip_tac >> gvs[] >>
  drule current_inst_trace_edge >> strip_tac >>
  first_x_assum drule >> strip_tac >> metis_tac[]
QED

(* Immutable annotations are required only at labels not yet visited. Output
   renaming invalidates owner spelling at the visited label, whereas incoming
   edge updates preserve it at every label. *)
Definition current_unvisited_annotations_def:
  current_unvisited_annotations A visited bbs <=>
    !l bb. ~MEM l visited /\ lookup_block l bbs = SOME bb ==>
      LIST_REL (\anns inst. MAP SND anns = inst.inst_outputs)
        (A l) bb.bb_instructions
End

Theorem current_annotations_edge_insts:
  !anns insts.
  LIST_REL (\a inst. MAP SND a = inst.inst_outputs) anns
    (MAP (current_edge_inst rs p) insts) <=>
  LIST_REL (\a inst. MAP SND a = inst.inst_outputs) anns insts
Proof
  Induct >> Cases_on `insts` >> simp[]
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

(* Each event keeps the local call endpoints and the concrete before/after
   edge-update snapshots. A is immutable, unlike the threaded block list.
   The lexical environment is an input to a subtree, not its return value. *)
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
        (fs[dom_tree_labels_def, ALL_DISTINCT_APPEND, EVERY_MEM] >>
         metis_tac[]) >>
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
  qexistsl_tac [`ctrs'`, `s'`, `bbs'`, `H'`, `visited'`] >>
  metis_tac[]
QED

(* Consumer boundary: a certificate for a specified concrete result. *)
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
  drule (cj 1 current_tree_trace_projection) >> strip_tac >> gvs[] >>
  metis_tac[]
QED
