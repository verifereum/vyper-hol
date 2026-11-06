Theory makeSsaCurrentFinalBlock
Ancestors
  makeSsaCurrentTreeTrace makeSsaCurrentTreePaths makeSsaCurrentEdgeTrace
  makeSsaCurrentInduct makeSsaCurrentDefs makeSsaHelper cfgTransformProps
  makeSsaDefs list pair

Definition current_block_edge_fold_def:
  current_block_edge_fold rs p succs bb =
    FOLDL (\b q. if q = b.bb_label then current_edge_block rs p b else b) bb succs
End

Definition current_event_edge_def:
  current_event_edge sm
    (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,bbs1,bbs2) =
    current_block_edge_fold rs1 l
      (case ALOOKUP sm l of NONE => [] | SOME ss => ss)
End

Definition current_replay_edges_def:
  current_replay_edges sm events blk =
    FOLDL (\b ev. current_event_edge sm ev b) blk events
End

Theorem current_block_edge_fold_label[simp]:
  !succs bb. (current_block_edge_fold rs p succs bb).bb_label = bb.bb_label
Proof
  Induct >> simp[current_block_edge_fold_def] >>
  rpt gen_tac >> Cases_on `h = bb.bb_label` >>
  simp[GSYM current_block_edge_fold_def]
QED

Theorem current_succ_phis_fold_lookup:
  !succs bbs bb.
    lookup_block q bbs = SOME bb ==>
    lookup_block q (update_current_succ_phis rs p bbs succs) =
      SOME (current_block_edge_fold rs p succs bb)
Proof
  Induct >> simp[current_succ_phis_nil, current_block_edge_fold_def] >>
  rpt strip_tac >> rewrite_tac[current_succ_phis_cons] >>
  `bb.bb_label = q` by metis_tac[lookup_block_label] >>
  Cases_on `q = h` >> gvs[GSYM current_block_edge_fold_def] >>
  first_x_assum irule >> simp[current_edge_step_lookup]
QED

Theorem current_event_edge_label[simp]:
  (current_event_edge sm ev bb).bb_label = bb.bb_label
Proof
  PairCases_on `ev` >> simp[current_event_edge_def]
QED

Theorem current_replay_edges_label[simp]:
  !events bb. (current_replay_edges sm events bb).bb_label = bb.bb_label
Proof
  Induct >- simp[current_replay_edges_def] >>
  simp[Once current_replay_edges_def] >>
  simp[GSYM current_replay_edges_def]
QED

Theorem current_replay_edges_append:
  current_replay_edges sm (xs ++ ys) bb =
    current_replay_edges sm ys (current_replay_edges sm xs bb)
Proof
  simp[current_replay_edges_def, rich_listTheory.FOLDL_APPEND]
QED

Theorem current_trace_unvisited_lookup:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    !q bb. lookup_block q bbs = SOME bb /\
      ~MEM q (MAP current_event_label events) ==>
      lookup_block q bbs' = SOME (current_replay_edges sm events bb)) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    !q bb. lookup_block q bbs = SOME bb /\
      ~MEM q (MAP current_event_label events) ==>
      lookup_block q bbs' = SOME (current_replay_edges sm events bb))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[]
      >- simp[current_replay_edges_def] >>
      rpt strip_tac >>
      gvs[current_event_label_def] >>
      simp[Once current_replay_edges_def] >>
      simp[GSYM current_replay_edges_def, current_event_edge_def] >>
      first_x_assum drule >> disch_then irule >> simp[] >>
      irule current_succ_phis_fold_lookup >>
      `x.bb_label = lbl` by metis_tac[lookup_block_label] >>
      simp[lookup_block_replace_neq])
  >- simp[current_tree_trace_def, current_replay_edges_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  rpt strip_tac >> gvs[MEM_MAP, current_replay_edges_append] >>
  first_x_assum (drule_then irule) >> simp[] >>
  first_x_assum (drule_then irule) >> simp[]
QED

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
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  simp[] >> metis_tac[]
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
      fs[dom_tree_labels_def] >>
      simp[current_event_label_def] >>
      drule (cj 2 current_trace_event_labels) >>
      first_x_assum drule_all >> metis_tac[])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  fs[ALL_DISTINCT_APPEND] >>
  drule (cj 1 current_trace_event_labels) >>
  drule (cj 2 current_trace_event_labels) >>
  simp[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Definition current_event_renamed_block_def:
  current_event_renamed_block
    (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,bbs1,bbs2) =
    bb with bb_instructions := ren
End

(* Project an event onto one lookup. The overriding case is justified by
   the actual trace's successful lookup, not by insertion into missing lists. *)
Definition current_event_lookup_def:
  current_event_lookup sm q prior ev =
    if q = current_event_label ev then
      SOME (current_event_edge sm ev (current_event_renamed_block ev))
    else OPTION_MAP (current_event_edge sm ev) prior
End

Theorem current_succ_phis_fold_lookup_option:
  !succs bbs.
    lookup_block q (update_current_succ_phis rs p bbs succs) =
      OPTION_MAP (current_block_edge_fold rs p succs) (lookup_block q bbs)
Proof
  Induct
  >- (gen_tac >> Cases_on `lookup_block q bbs` >>
      simp[current_succ_phis_nil, current_block_edge_fold_def]) >>
  rpt gen_tac >> rewrite_tac[current_succ_phis_cons] >>
  first_x_assum (qspec_then `current_edge_step rs p bbs h` mp_tac) >>
  simp[current_edge_step_lookup] >>
  Cases_on `lookup_block q bbs` >> simp[] >>
  `x.bb_label = q` by metis_tac[lookup_block_label] >>
  Cases_on `q = h` >> gvs[current_block_edge_fold_def]
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
  first_x_assum drule >> strip_tac >>
  simp[rich_listTheory.FOLDL_APPEND]
QED

Theorem current_unvisited_lookup_fold:
  !events bb.
    ~MEM q (MAP current_event_label events) ==>
    FOLDL (current_event_lookup sm q) (SOME bb) events =
      SOME (current_replay_edges sm events bb)
Proof
  Induct >> simp[current_replay_edges_def] >>
  rpt strip_tac >>
  simp[current_event_lookup_def] >>
  simp[GSYM current_replay_edges_def]
QED

Theorem current_event_suffix_fold:
  ~MEM (current_event_label ev) (MAP current_event_label after) ==>
  FOLDL (current_event_lookup sm (current_event_label ev)) initial
    (before ++ ev::after) =
    SOME (current_replay_edges sm (ev::after) (current_event_renamed_block ev))
Proof
  strip_tac >>
  simp[rich_listTheory.FOLDL_APPEND, current_event_lookup_def] >>
  simp[Once current_replay_edges_def] >>
  simp[GSYM current_replay_edges_def] >>
  irule current_unvisited_lookup_fold >> simp[]
QED

Theorem current_trace_final_event:
  current_tree_trace A sm tree s rs bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  ALL_DISTINCT (dom_tree_labels tree) /\ events = before ++ ev::after ==>
  lookup_block (current_event_label ev) bbs' =
    SOME (current_replay_edges sm (ev::after) (current_event_renamed_block ev))
Proof
  strip_tac >>
  drule (cj 1 current_trace_lookup_fold) >> strip_tac >>
  drule_all (cj 1 current_trace_event_labels_distinct) >>
  simp[ALL_DISTINCT_APPEND] >> strip_tac >>
  simp[] >> irule current_event_suffix_fold >> simp[]
QED

Theorem current_children_final_event:
  current_children_trace A sm trees s ctrs stacks bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  ALL_DISTINCT (FLAT (MAP dom_tree_labels trees)) /\
  events = before ++ ev::after ==>
  lookup_block (current_event_label ev) bbs' =
    SOME (current_replay_edges sm (ev::after) (current_event_renamed_block ev))
Proof
  strip_tac >>
  drule (cj 2 current_trace_lookup_fold) >> strip_tac >>
  drule_all (cj 2 current_trace_event_labels_distinct) >>
  simp[ALL_DISTINCT_APPEND] >> strip_tac >>
  simp[] >> irule current_event_suffix_fold >> simp[]
QED

(* One common shape relation records all instruction-preservation facts. *)
Definition current_edge_shape_def:
  current_edge_shape old new <=>
    old.bb_label = new.bb_label /\
    LIST_REL (\i j. i.inst_outputs = j.inst_outputs /\
      i.inst_opcode = j.inst_opcode /\ (i.inst_opcode <> PHI ==> i = j))
      old.bb_instructions new.bb_instructions
End

Theorem current_edge_shape_refl:
  current_edge_shape bb bb
Proof
  simp[current_edge_shape_def, LIST_REL_EL_EQN]
QED

Theorem current_edge_shape_trans:
  current_edge_shape a b /\ current_edge_shape b c ==>
  current_edge_shape a c
Proof
  simp[current_edge_shape_def, LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem current_edge_block_shape:
  current_edge_shape bb (current_edge_block rs p bb)
Proof
  simp[current_edge_shape_def, current_edge_block_def,
    LIST_REL_EL_EQN, EL_MAP] >>
  rpt strip_tac >> simp[current_edge_inst_def] >>
  Cases_on `(EL n bb.bb_instructions).inst_opcode = PHI` >> simp[]
QED

Theorem current_block_edge_fold_shape:
  !succs bb. current_edge_shape bb (current_block_edge_fold rs p succs bb)
Proof
  Induct >- simp[current_block_edge_fold_def, current_edge_shape_refl] >>
  rpt gen_tac >> simp[Once current_block_edge_fold_def] >>
  simp[GSYM current_block_edge_fold_def] >>
  Cases_on `h = bb.bb_label` >> simp[] >>
  metis_tac[current_edge_shape_trans, current_edge_block_shape]
QED

Theorem current_event_edge_shape:
  current_edge_shape bb (current_event_edge sm ev bb)
Proof
  PairCases_on `ev` >> simp[current_event_edge_def, current_block_edge_fold_shape]
QED

Theorem current_replay_edges_shape:
  !events bb. current_edge_shape bb (current_replay_edges sm events bb)
Proof
  Induct >- simp[current_replay_edges_def, current_edge_shape_refl] >>
  rpt gen_tac >> simp[Once current_replay_edges_def] >>
  simp[GSYM current_replay_edges_def] >>
  metis_tac[current_edge_shape_trans, current_event_edge_shape]
QED

Theorem current_replay_edges_length:
  LENGTH (current_replay_edges sm events bb).bb_instructions =
    LENGTH bb.bb_instructions
Proof
  mp_tac current_replay_edges_shape >>
  simp[current_edge_shape_def, LIST_REL_EL_EQN]
QED

Theorem current_replay_edges_outputs:
  MAP instruction_inst_outputs (current_replay_edges sm events bb).bb_instructions =
    MAP instruction_inst_outputs bb.bb_instructions
Proof
  qspecl_then [`events`, `bb`] mp_tac current_replay_edges_shape >>
  simp[current_edge_shape_def, LIST_REL_EL_EQN] >> strip_tac >>
  irule LIST_EQ >> simp[EL_MAP]
QED

Theorem current_replay_edges_non_phi:
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode <> PHI ==>
  EL i (current_replay_edges sm events bb).bb_instructions = EL i bb.bb_instructions
Proof
  mp_tac current_replay_edges_shape >>
  simp[current_edge_shape_def, LIST_REL_EL_EQN] >> metis_tac[]
QED
