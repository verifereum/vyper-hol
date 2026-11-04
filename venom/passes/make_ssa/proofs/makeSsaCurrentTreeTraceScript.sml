Theory makeSsaCurrentTreeTrace
Ancestors
  makeSsaCurrentCertificate makeSsaCurrentAllocation makeSsaCurrentRenameTrace
  makeSsaCurrentEdgeTrace makeSsaCurrentInduct makeSsaCurrentDefs
  makeSsaCurrentProps makeSsaDefs cfgTransform cfgTransformProps makeSsaHelper
  makeSsaCurrentAnalysis venomInst venomWf irSupply list pair sorting

(* Sibling calls retain global counters/history but restore the lexical
   stacks and environment of their parent. These boundaries do not equate
   the sibling's final stacks with those of the parent. *)
Theorem current_env_realizes_restore:
  current_env_realizes H E ((ctrs : (string # num) list),stacks) V ==>
  current_env_realizes (H ++ tail) E ((ctrs' : (string # num) list),stacks) V
Proof
  simp[current_env_realizes_def, latest_current_name_def] >>
  rpt strip_tac >> first_x_assum drule >>
  disch_then (mp_tac o MATCH_MP current_token_name_append_stable) >> simp[]
QED

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
  current_allocation_consistent V (H ++ tail) s'
    (ctrs',(stacks' : (string # string list) list)) /\
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

Definition current_annotation_map_def:
  current_annotation_map bbs
    (annsss : (current_token # string) list list list) l =
    case ALOOKUP (ZIP (MAP (\bb. bb.bb_label) bbs,annsss)) l of
      NONE => [] | SOME anns => anns
End

Theorem current_annotation_map_owners:
  !bbs annsss.
    LIST_REL (\bb anns.
      LIST_REL (\a inst. MAP SND a = inst.inst_outputs) anns bb.bb_instructions)
      bbs annsss ==>
    !l bb. lookup_block l bbs = SOME bb ==>
      LIST_REL (\a inst. MAP SND a = inst.inst_outputs)
        (current_annotation_map bbs annsss l) bb.bb_instructions
Proof
  Induct >> Cases_on `annsss` >>
  simp[lookup_block_def, FIND_thm, current_annotation_map_def] >>
  rpt strip_tac >> rename1 `old.bb_label = l` >>
  Cases_on `old.bb_label = l` >> gvs[] >>
  first_x_assum drule >> simp[current_annotation_map_def, lookup_block_def]
QED

Theorem current_annotation_map_initial:
  LIST_REL (\bb anns.
    LIST_REL (\a inst. MAP SND a = inst.inst_outputs) anns bb.bb_instructions)
    bbs annsss ==>
  current_unvisited_annotations (current_annotation_map bbs annsss) [] bbs
Proof
  simp[current_unvisited_annotations_def] >>
  metis_tac[current_annotation_map_owners]
QED

Theorem current_provenance_map_owners:
  !olds news annsss.
  LENGTH olds = LENGTH news /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,news)) annsss ==>
  LIST_REL (\bb anns.
    LIST_REL (\a inst. MAP SND a = inst.inst_outputs) anns bb.bb_instructions)
    news annsss
Proof
  Induct >> Cases_on `news` >> Cases_on `annsss` >> simp[] >>
  rpt gen_tac >> strip_tac
  >- (fs[current_block_provenance_def, LIST_REL_EL_EQN] >> metis_tac[]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem current_provenance_map_initial:
  LENGTH olds = LENGTH news /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,news)) annsss ==>
  current_unvisited_annotations (current_annotation_map news annsss) [] news
Proof
  strip_tac >> irule current_annotation_map_initial >>
  irule current_provenance_map_owners >> metis_tac[]
QED

Theorem current_tree_labels_postorder:
  (!tree.
    (!l. MEM l (dom_tree_labels tree) <=> MEM l (dom_tree_postorder tree)) /\
    (ALL_DISTINCT (dom_tree_labels tree) <=> ALL_DISTINCT (dom_tree_postorder tree))) /\
  (!trees.
    (!l. MEM l (FLAT (MAP dom_tree_labels trees)) <=>
         MEM l (FLAT (MAP dom_tree_postorder trees))) /\
    (ALL_DISTINCT (FLAT (MAP dom_tree_labels trees)) <=>
     ALL_DISTINCT (FLAT (MAP dom_tree_postorder trees))))
Proof
  ho_match_mp_tac current_dom_tree_induction >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[dom_tree_labels_def, dom_tree_postorder_def, ALL_DISTINCT_APPEND,
        EVERY_MEM] >> metis_tac[]) >>
  conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[ALL_DISTINCT_APPEND, EVERY_MEM] >> metis_tac[]
QED

Theorem current_actual_tree_labels_distinct:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME bb ==>
  ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))
Proof
  strip_tac >> drule_all current_dom_postorder_perm >> strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by fs[wf_function_def] >>
  `ALL_DISTINCT (current_dom_postorder fn)` by
    metis_tac[ALL_DISTINCT_PERM] >>
  gvs[current_dom_postorder_def, current_tree_labels_postorder]
QED

Theorem current_actual_tree_trace:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME bb /\
  add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
    (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) fn.fn_blocks
    (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))))
    = (bbs1,s1) /\
  rename_current_blocks s1 rs bbs1 sm (current_dom_tree fn) = (ctrs',s',bbs') ==>
  ?annsss H' visited' events.
    LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
      (ZIP (fn.fn_blocks,bbs1)) annsss /\
    ALL_DISTINCT (MAP FST (FLAT (FLAT annsss))) /\
    current_tree_trace (current_annotation_map bbs1 annsss) sm (current_dom_tree fn)
      s1 rs bbs1 H E [] ctrs' s' bbs' H' visited' events
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  drule_all current_actual_provenance >> strip_tac >>
  `LENGTH fn.fn_blocks = LENGTH bbs1` by
    (drule current_actual_block_provenance >>
     metis_tac[LIST_REL_LENGTH]) >>
  `current_unvisited_annotations (current_annotation_map bbs1 annsss) [] bbs1` by
    (irule current_provenance_map_initial >> metis_tac[]) >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  qexists_tac `annsss` >> simp[] >>
  irule current_tree_trace_for_result >> simp[]
QED

(* Local trace endpoints stay interpretable in the final global history. *)
Definition current_event_trace_def:
  current_event_trace (A : string -> (current_token # string) list list) finalH
    (l,bb,s,rs,H,E,insts1,s1,rs1,H1,E1,
      (bbs1 : basic_block list),(bbs2 : basic_block list)) <=>
    current_local_trace (A l) bb.bb_instructions s rs H E
      insts1 s1 rs1 H1 E1 /\ ?tail. finalH = H1 ++ tail
End

Theorem current_event_trace_extend:
  current_event_trace A H ev ==>
  current_event_trace A (H ++ tail) ev
Proof
  PairCases_on `ev` >> simp[current_event_trace_def] >>
  metis_tac[APPEND_ASSOC]
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

(* Allocation keys can only originate in the immutable annotations of a
   visited subtree. This boundary is independent of allocation freshness. *)
Theorem current_tree_trace_keys_bound:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    !t. MEM t (MAP FST H') ==> MEM t (MAP FST H) \/
      ?l. MEM l (dom_tree_labels tree) /\ MEM t (MAP FST (FLAT (A l)))) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    !t. MEM t (MAP FST H') ==> MEM t (MAP FST H) \/
      ?l. MEM l (FLAT (MAP dom_tree_labels trees)) /\
        MEM t (MAP FST (FLAT (A l))))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def, Once dom_tree_labels_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      drule current_local_trace_keys >> strip_tac >>
      first_x_assum drule >> simp[] >> metis_tac[]) 
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

(* Pending labels retain fresh tokens even though history is global. *)
Definition current_pending_annotations_def:
  current_pending_annotations V A (H : (current_token # string # string) list) visited <=>
    !l. ~MEM l visited ==> current_annotations_ok V H (FLAT (A l))
End

Definition current_annotation_separation_def:
  current_annotation_separation (A : string -> (current_token # string) list list) <=>
    !l k t. MEM t (MAP FST (FLAT (A l))) /\
      MEM t (MAP FST (FLAT (A k))) ==> l = k
End

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
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> simp[]
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
    current_allocation_consistent V H s rs /\ current_env_realizes H E rs V ==>
    current_allocation_consistent V H' s' (ctrs',SND rs) /\
    current_env_realizes H' E (ctrs',SND rs) V) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events V.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    ALL_DISTINCT (FLAT (MAP dom_tree_labels trees)) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels trees)) ==> ~MEM l visited) /\
    current_pending_annotations V A H visited /\ current_annotation_separation A /\
    current_allocation_consistent V H s (ctrs,stacks) /\
    current_env_realizes H E (ctrs,stacks) V ==>
    current_allocation_consistent V H' s' (ctrs',stacks) /\
    current_env_realizes H' E (ctrs',stacks) V)
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
      `current_pending_annotations V A H1 (lbl::visited)` by
        (drule current_local_trace_keys >> strip_tac >>
         irule current_pending_annotations_visit >> simp[] >>
         qexists_tac `H` >> simp[]) >>
      `ALL_DISTINCT (FLAT (MAP dom_tree_labels trees)) /\
        (!l. MEM l (FLAT (MAP dom_tree_labels trees)) ==> ~MEM l (lbl::visited))` by
        (fs[dom_tree_labels_def, EVERY_MEM] >> metis_tac[]) >>
      `current_allocation_consistent V H' s' (ctrs',SND rs1)` by
        (Cases_on `rs1` >> gvs[] >> first_x_assum drule >> simp[]) >>
      `?tail. H' = H ++ tail` by
        (drule current_local_trace_history >>
         drule (cj 2 current_tree_trace_history) >>
         metis_tac[APPEND_ASSOC]) >>
      `ssa_supply_extends s s'` by
        (drule current_local_trace_projection >>
         drule current_children_trace_extends >>
         metis_tac[rename_current_block_insts_extends, ssa_supply_extends_trans]) >>
      gvs[] >> Cases_on `rs` >> gvs[] >> conj_tac
      >- (`ssa_stacks_covered s r` by
            (qpat_x_assum `current_allocation_consistent V H s (q,r)` mp_tac >>
             simp[current_allocation_consistent_def]) >>
          irule current_allocation_consistent_restore >> conj_tac
          >- (qexists_tac `s` >> simp[]) >>
          qexists_tac `SND rs1` >> simp[]) >>
      irule current_env_realizes_restore >> simp[] >>
      qexists_tac `q` >> simp[])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[current_tree_trace_def] >>
  `ALL_DISTINCT (dom_tree_labels tree) /\
    (!l. MEM l (dom_tree_labels tree) ==> ~MEM l visited)` by
    fs[ALL_DISTINCT_APPEND, EVERY_MEM] >>
  `current_allocation_consistent V H1 s1 (ctrs1,stacks) /\
    current_env_realizes H1 E (ctrs1,stacks) V` by
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

Definition current_event_valid_def:
  current_event_valid (A : string -> (current_token # string) list list) V
    (l,bb,s,rs,H,E,insts1,s1,rs1,H1,E1,
      (bbs1 : basic_block list),(bbs2 : basic_block list)) <=>
    current_annotations_ok V H (FLAT (A l)) /\
    current_allocation_consistent V H s rs /\ current_env_realizes H E rs V
End

Theorem current_tree_trace_events_valid:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events V.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    ALL_DISTINCT (dom_tree_labels tree) /\
    (!l. MEM l (dom_tree_labels tree) ==> ~MEM l visited) /\
    current_pending_annotations V A H visited /\ current_annotation_separation A /\
    current_allocation_consistent V H s rs /\ current_env_realizes H E rs V ==>
    EVERY (current_event_valid A V) events) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events V.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    ALL_DISTINCT (FLAT (MAP dom_tree_labels trees)) /\
    (!l. MEM l (FLAT (MAP dom_tree_labels trees)) ==> ~MEM l visited) /\
    current_pending_annotations V A H visited /\ current_annotation_separation A /\
    current_allocation_consistent V H s (ctrs,stacks) /\
    current_env_realizes H E (ctrs,stacks) V ==>
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
      `current_pending_annotations V A H1 (lbl::visited)` by
        (drule current_local_trace_keys >> strip_tac >>
         irule current_pending_annotations_visit >> simp[] >>
         qexists_tac `H` >> simp[]) >>
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
    current_env_realizes H1 E (ctrs1,stacks) V` by
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
    !v. MEM v V ==>
      current_token_name finalH (E v) = SOME (latest_current_name rs v) /\
      current_token_name finalH (E1 v) = SOME (latest_current_name rs1 v)
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
  drule current_local_trace_history >> strip_tac >> gvs[] >>
  rpt strip_tac >>
  `current_token_name ev5 (ev6 v) = SOME (latest_current_name (ev3,ev4) v)` by
    fs[current_env_realizes_def] >>
  `current_token_name (ev5 ++ tail') (ev12 v) = SOME (latest_current_name (ev9,ev10) v)` by
    fs[current_env_realizes_def] >>
  metis_tac[current_token_name_append_stable, APPEND_ASSOC]
QED

Theorem current_events_names_valid:
  EVERY (current_event_valid A V) events /\
  EVERY (current_event_trace A finalH) events ==>
  EVERY (current_event_names finalH V) events
Proof
  simp[EVERY_MEM] >> metis_tac[current_event_names_valid]
QED

Theorem current_annotation_map_keys_bound:
  !bbs annsss l t.
    LENGTH bbs = LENGTH annsss /\
    MEM t (MAP FST (FLAT (current_annotation_map bbs annsss l))) ==>
    MEM t (MAP FST (FLAT (FLAT annsss)))
Proof
  Induct >> Cases_on `annsss` >>
  simp[current_annotation_map_def, MAP_APPEND] >> rpt gen_tac >> strip_tac >>
  Cases_on `h'.bb_label = l` >> gvs[] >>
  disj2_tac >> first_x_assum irule >> simp[] >>
  qexists_tac `l` >> simp[current_annotation_map_def]
QED

Theorem current_annotation_map_separation:
  !bbs annsss.
    LENGTH bbs = LENGTH annsss /\
    ALL_DISTINCT (MAP FST (FLAT (FLAT annsss))) ==>
    current_annotation_separation (current_annotation_map bbs annsss)
Proof
  Induct >> Cases_on `annsss` >>
  simp[current_annotation_map_def, current_annotation_separation_def, MAP_APPEND,
    ALL_DISTINCT_APPEND] >> rpt gen_tac >> strip_tac >>
  `current_annotation_separation (current_annotation_map bbs t)` by
    (first_x_assum irule >> simp[]) >>
  qspecl_then [`bbs`, `t`] mp_tac current_annotation_map_keys_bound >>
  simp[current_annotation_map_def] >> strip_tac >>
  rpt gen_tac >>
  Cases_on `h'.bb_label = l` >> Cases_on `h'.bb_label = k` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  fs[current_annotation_map_def, current_annotation_separation_def] >> metis_tac[]
QED

Theorem current_annotation_map_ok:
  !bbs annsss V H.
    LENGTH bbs = LENGTH annsss /\
    current_annotations_ok V H (FLAT (FLAT annsss)) ==>
    !l. current_annotations_ok V H (FLAT (current_annotation_map bbs annsss l))
Proof
  Induct >> Cases_on `annsss` >> simp[current_annotation_map_def,
    current_annotations_ok_def, MAP_APPEND, ALL_DISTINCT_APPEND] >>
  rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `h'.bb_label = l` >> gvs[] >>
  first_x_assum (qspecl_then [`t`, `V`, `H`] mp_tac) >>
  simp[current_annotation_map_def, current_annotations_ok_def] >>
  disch_then (qspec_then `l` ACCEPT_TAC)
QED

Theorem current_annotation_map_pending:
  LENGTH bbs = LENGTH annsss /\
  current_annotations_ok V H (FLAT (FLAT annsss)) ==>
  current_pending_annotations V (current_annotation_map bbs annsss) H visited
Proof
  simp[current_pending_annotations_def] >> metis_tac[current_annotation_map_ok]
QED

(* An initially empty allocation history gives valid final-history names at
   every local entry and exit, including across restored sibling stacks. *)
Theorem current_annotated_tree_names:
  LENGTH bbs = LENGTH annsss /\
  current_annotations_ok V ([] : (current_token # string # string) list)
    (FLAT (FLAT annsss)) /\
  current_allocation_consistent V [] s rs /\
  current_env_realizes ([] : (current_token # string # string) list) E rs V /\
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
    (irule current_annotation_map_separation >>
     fs[current_annotations_ok_def]) >>
  conj_tac
  >- (drule (cj 1 current_tree_trace_preserves) >> simp[] >>
      disch_then (qspec_then `V` mp_tac) >> simp[]) >>
  irule current_events_names_valid >>
  qexists_tac `current_annotation_map bbs annsss` >> conj_tac
  >- (drule (cj 1 current_tree_trace_events) >> simp[]) >>
  drule (cj 1 current_tree_trace_events_valid) >> simp[] >>
  disch_then (qspec_then `V` mp_tac) >> simp[]
QED

Theorem current_provenance_annotations_nondefault:
  !pairs annsss.
    LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
      pairs annsss ==>
    !t. MEM t (MAP FST (FLAT (FLAT annsss))) ==> !v. t <> CurrentDefault v
Proof
  Induct >> Cases_on `annsss` >> simp[] >> rpt strip_tac >>
  gvs[MAP_APPEND]
  >- metis_tac[current_block_provenance_nondefault] >>
  first_x_assum drule >> disch_then drule >> simp[]
QED

Theorem current_provenance_annotations_ok:
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    pairs annsss /\ ALL_DISTINCT (MAP FST (FLAT (FLAT annsss))) /\
  (!v. MEM v (MAP SND (FLAT (FLAT annsss))) ==> MEM v V) ==>
  current_annotations_ok V ([] : (current_token # string # string) list)
    (FLAT (FLAT annsss))
Proof
  strip_tac >> simp[current_annotations_ok_def, EVERY_MEM, pairTheory.FORALL_PROD] >>
  rpt strip_tac
  >- (drule current_provenance_annotations_nondefault >>
      disch_then (qspec_then `CurrentDefault w` mp_tac) >>
      simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  first_x_assum irule >> simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]
QED

Theorem current_instruction_annotations_erase:
  !insts annss.
    LIST_REL (\anns inst. MAP SND anns = inst.inst_outputs) annss insts ==>
    MAP SND (FLAT annss) = FLAT (MAP (\inst. inst.inst_outputs) insts)
Proof
  Induct >> Cases_on `annss` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[MAP_APPEND]
QED

Theorem current_block_annotations_erase:
  !bbs annsss.
    LIST_REL (\bb anns.
      LIST_REL (\a inst. MAP SND a = inst.inst_outputs) anns bb.bb_instructions)
      bbs annsss ==>
    MAP SND (FLAT (FLAT annsss)) =
      FLAT (MAP (\bb. FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions)) bbs)
Proof
  Induct >> Cases_on `annsss` >> simp[] >> rpt strip_tac >>
  drule current_instruction_annotations_erase >> strip_tac >>
  first_x_assum drule >> simp[MAP_APPEND]
QED

Theorem current_annotation_owners_in_vars:
  LIST_REL (\bb anns.
    LIST_REL (\a inst. MAP SND a = inst.inst_outputs) anns bb.bb_instructions)
    bbs annsss ==>
  !v. MEM v (MAP SND (FLAT (FLAT annsss))) ==>
    MEM v (FLAT (MAP block_ir_vars bbs))
Proof
  strip_tac >> drule current_block_annotations_erase >> strip_tac >>
  simp[] >> rw[MEM_FLAT, MEM_MAP, block_ir_vars_def] >>
  gvs[MEM_FLAT, MEM_MAP] >>
  qexists_tac `FLAT (MAP inst_ir_vars bb.bb_instructions)` >> conj_tac
  >- (qexists_tac `bb` >> simp[]) >>
  simp[MEM_FLAT, MEM_MAP] >>
  qexists_tac `inst_ir_vars inst` >> conj_tac
  >- (qexists_tac `inst` >> simp[]) >>
  simp[inst_ir_vars_def]
QED

Theorem current_provenance_tree_names:
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\
  ALL_DISTINCT (MAP FST (FLAT (FLAT annsss))) /\
  current_allocation_consistent (FLAT (MAP block_ir_vars bbs)) [] s rs /\
  current_env_realizes ([] : (current_token # string # string) list) E rs
    (FLAT (MAP block_ir_vars bbs)) /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree s rs bbs
    [] E [] ctrs' s' bbs' H' visited' events ==>
  current_allocation_consistent (FLAT (MAP block_ir_vars bbs)) H' s'
    (ctrs',SND rs) /\
  EVERY (current_event_names H' (FLAT (MAP block_ir_vars bbs))) events
Proof
  strip_tac >>
  `LENGTH bbs = LENGTH annsss` by
    (drule LIST_REL_LENGTH >> simp[]) >>
  `LIST_REL (\bb anns.
      LIST_REL (\a inst. MAP SND a = inst.inst_outputs) anns bb.bb_instructions)
      bbs annsss` by
    (irule current_provenance_map_owners >> metis_tac[]) >>
  `current_annotations_ok (FLAT (MAP block_ir_vars bbs))
    ([] : (current_token # string # string) list) (FLAT (FLAT annsss))` by
    (irule current_provenance_annotations_ok >> simp[] >> conj_tac
     >- (drule current_annotation_owners_in_vars >> simp[]) >>
     qexistsl_tac [`fn`, `ZIP (olds,bbs)`] >> simp[]) >>
  drule_all current_annotated_tree_names >> simp[]
QED

Theorem current_initial_counter:
  !defs v. current_counter (init_current_rename_state defs) v = 0
Proof
  Induct >> simp[init_current_rename_state_def, current_counter_def] >>
  rpt gen_tac >> Cases_on `FST h = v` >> simp[] >>
  fs[init_current_rename_state_def, current_counter_def, latest_current_name_def]
QED

Theorem current_initial_latest:
  !defs v. latest_current_name (init_current_rename_state defs) v = v
Proof
  Induct >> simp[init_current_rename_state_def, latest_current_name_def] >>
  rpt gen_tac >> Cases_on `FST h = v` >> simp[] >>
  fs[init_current_rename_state_def, current_counter_def, latest_current_name_def]
QED

Theorem current_initial_state_valid:
  ssa_vars_covered s V /\ ssa_vars_covered s (MAP FST defs) ==>
  current_allocation_consistent V ([] : (current_token # string # string) list)
    s (init_current_rename_state defs) /\
  current_env_realizes ([] : (current_token # string # string) list)
    CurrentDefault (init_current_rename_state defs) V
Proof
  simp[current_allocation_consistent_def, current_history_valid_def,
    current_initial_counter, current_owner_count_def, current_env_realizes_def,
    current_initial_latest, init_current_rename_state_def,
    ssa_stacks_covered_def, ssa_vars_covered_def, EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem current_provenance_initial_tree_names:
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\
  ALL_DISTINCT (MAP FST (FLAT (FLAT annsss))) /\
  ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) /\
  ssa_vars_covered s (MAP FST defs) /\
  ALL_DISTINCT (dom_tree_labels tree) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s (init_current_rename_state defs) bbs [] CurrentDefault []
    ctrs' s' bbs' H' visited' events ==>
  current_allocation_consistent (FLAT (MAP block_ir_vars bbs)) H' s'
    (ctrs',SND (init_current_rename_state defs)) /\
  EVERY (current_event_names H' (FLAT (MAP block_ir_vars bbs))) events
Proof
  strip_tac >>
  `current_allocation_consistent (FLAT (MAP block_ir_vars bbs))
      ([] : (current_token # string # string) list) s (init_current_rename_state defs) /\
    current_env_realizes ([] : (current_token # string # string) list)
      CurrentDefault (init_current_rename_state defs) (FLAT (MAP block_ir_vars bbs))` by
    (irule current_initial_state_valid >> simp[]) >>
  drule_all current_provenance_tree_names >> simp[]
QED
