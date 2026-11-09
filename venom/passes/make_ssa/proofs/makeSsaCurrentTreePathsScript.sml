Theory makeSsaCurrentTreePaths
Ancestors
  makeSsaCurrentTreeTrace makeSsaCurrentCertificate makeSsaCurrentInduct
  makeSsaCurrentRenameTrace makeSsaDefs makeSsaCurrentTokens
   makeSsaCurrentProps cfgTransformProps
  venomInst list rich_list pair
  venomExecProofs

Definition current_event_label_def:
  current_event_label (l,bb,s,rs,H,E,insts1,s1,rs1,H1,E1,bbs1,bbs2) = l
End

Definition current_event_entry_env_def:
  current_event_entry_env (l,bb,s,rs,H,E,insts1,s1,rs1,H1,E1,bbs1,bbs2) = E
End

Definition current_event_exit_env_def:
  current_event_exit_env (l,bb,s,rs,H,E,insts1,s1,rs1,H1,E1,bbs1,bbs2) = E1
End

Definition current_event_entry_rs_def:
  current_event_entry_rs (l,bb,s,rs,H,E,insts1,s1,rs1,H1,E1,bbs1,bbs2) = rs
End

Definition current_event_exit_rs_def:
  current_event_exit_rs (l,bb,s,rs,H,E,insts1,s1,rs1,H1,E1,bbs1,bbs2) = rs1
End

Inductive current_tree_ancestor_path:
  (!l children. current_tree_ancestor_path (DNode l children) l []) /\
  (!p children child l path.
    MEM child children /\ current_tree_ancestor_path child l path ==>
    current_tree_ancestor_path (DNode p children) l (p::path))
End

Definition current_advance_annotations_def:
  current_advance_annotations (A : string -> (current_token # string) list list) l E =
    FOLDL (\env (t,v). (v =+ t) env) E (FLAT (A l))
End

Definition current_path_env_def:
  (current_path_env A E [] = E) /\
  (current_path_env A E (l::path) =
    current_path_env A (current_advance_annotations A l E) path)
End

Theorem current_path_env_append:
  !xs E ys. current_path_env A E (xs ++ ys) =
    current_path_env A (current_path_env A E xs) ys
Proof
  Induct >> simp[current_path_env_def]
QED

Definition current_event_path_def:
  current_event_path A tree E ev <=>
    ?path. current_tree_ancestor_path tree (current_event_label ev) path /\
      current_event_entry_env ev = current_path_env A E path /\
      current_event_exit_env ev = current_advance_annotations A
        (current_event_label ev) (current_event_entry_env ev)
End

Theorem current_event_path_parent:
  MEM child children /\ current_event_path A child
    (current_advance_annotations A p E) ev ==>
  current_event_path A (DNode p children) E ev
Proof
  rw[current_event_path_def] >> qexists_tac `p::path` >>
  simp[current_path_env_def] >>
  metis_tac[current_tree_ancestor_path_rules]
QED

Theorem current_tree_trace_paths:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    EVERY (current_event_path A tree E) events) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    EVERY (\ev. ?tree. MEM tree trees /\ current_event_path A tree E ev) events)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      drule current_local_trace_exit_env >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      simp[EVERY_MEM] >> conj_tac
      >- (simp[current_event_path_def, current_event_label_def,
            current_event_entry_env_def, current_event_exit_env_def,
            current_advance_annotations_def] >>
          qexists_tac `[]` >> simp[current_path_env_def,
            current_tree_ancestor_path_rules]) >>
      fs[EVERY_MEM, current_advance_annotations_def] >> rpt strip_tac >>
      irule current_event_path_parent >>
      simp[current_advance_annotations_def] >> metis_tac[]) 
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem current_tree_ancestor_path_labels:
  !tree l path. current_tree_ancestor_path tree l path ==>
    MEM l (dom_tree_labels tree) /\
    (!p. MEM p path ==> MEM p (dom_tree_labels tree))
Proof
  ho_match_mp_tac current_tree_ancestor_path_ind >>
  simp[dom_tree_labels_def, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem current_path_env_tokens:
  !path E.
    (!l E v. MEM l path ==> current_advance_annotations A l E v =
      current_block_token fn ins v l (E v)) ==>
    !v. current_path_env A E path v = current_chain_token fn ins v path (E v)
Proof
  Induct >> simp[current_path_env_def, current_chain_token_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem current_tree_trace_static_env:
  current_tree_trace A sm tree s rs bbs H CurrentDefault visited
    ctrs' s' bbs' H' visited' events /\
  (!l E v. MEM l (dom_tree_labels tree) ==>
    current_advance_annotations A l E v =
      current_block_token fn (current_actual_inserted fn) v l (E v)) /\
  MEM ev events ==>
  ?path. current_tree_ancestor_path tree (current_event_label ev) path /\
    (!v. current_event_entry_env ev v =
      current_inherited_token fn (current_actual_inserted fn) v path) /\
    (!v. current_event_exit_env ev v =
      current_block_token fn (current_actual_inserted fn) v (current_event_label ev)
        (current_inherited_token fn (current_actual_inserted fn) v path))
Proof
  strip_tac >> drule (cj 1 current_tree_trace_paths) >>
  simp[EVERY_MEM] >> disch_then drule >>
  simp[current_event_path_def] >> strip_tac >> qexists_tac `path` >> simp[] >>
  drule current_tree_ancestor_path_labels >> strip_tac >>
  `!v. current_path_env A CurrentDefault path v =
    current_inherited_token fn (current_actual_inserted fn) v path` by
    (simp[current_inherited_token_def] >> irule current_path_env_tokens >> metis_tac[]) >>
  metis_tac[]
QED

Theorem current_provenance_annotation_map_scan:
  !olds bbs annsss.
    LENGTH olds = LENGTH bbs /\
    LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
      (ZIP (olds,bbs)) annsss /\
    (!old. MEM old olds ==> lookup_block old.bb_label fn.fn_blocks = SOME old) ==>
    !l bb E v. lookup_block l bbs = SOME bb ==>
      current_advance_annotations (current_annotation_map bbs annsss) l E v =
        current_block_token fn (current_actual_inserted fn) v l (E v)
Proof
  Induct >> namedCases_on `bbs` ["", "new news"] >>
  namedCases_on `annsss` ["", "anns annrest"] >>
  simp[lookup_block_def, FIND_thm] >> rpt gen_tac >> strip_tac >>
  `new.bb_label = h.bb_label` by fs[current_block_provenance_def] >>
  simp[lookup_block_def, FIND_thm, current_advance_annotations_def,
    current_annotation_map_def] >>
  rpt gen_tac >> Cases_on `new.bb_label = l` >> simp[] >> strip_tac
  >- (gvs[] >> irule current_block_provenance_scan >>
      fs[lookup_block_def] >> metis_tac[]) >>
  first_x_assum drule >> simp[lookup_block_def] >>
  strip_tac >>
  gvs[current_advance_annotations_def, current_annotation_map_def,
    lookup_block_def] >> metis_tac[]
QED

Theorem current_tree_trace_labels:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events ==>
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs)
Proof
  conj_tac >> rpt strip_tac
  >- (drule (cj 1 current_tree_trace_projection) >>
      metis_tac[cj 1 rename_current_blocks_labels]) >>
  drule (cj 2 current_tree_trace_projection) >>
  metis_tac[cj 2 rename_current_blocks_labels]
QED

Theorem current_edge_visit_labels:
  lookup_block l bbs = SOME bb ==>
  MAP (\b. b.bb_label)
    (update_current_succ_phis rs l
      (replace_block l (bb with bb_instructions := insts) bbs) succs) =
  MAP (\b. b.bb_label) bbs
Proof
  strip_tac >> drule lookup_block_label >> strip_tac >>
  simp[update_current_succ_phis_labels, fn_labels_replace_block]
QED

Theorem current_tree_trace_event_labels:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    (!l. MEM l (dom_tree_labels tree) ==> IS_SOME (lookup_block l bbs)) ==>
    MAP current_event_label events = dom_tree_labels tree) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events /\
    (!l. MEM l (FLAT (MAP dom_tree_labels trees)) ==> IS_SOME (lookup_block l bbs)) ==>
    MAP current_event_label events = FLAT (MAP dom_tree_labels trees))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      `IS_SOME (lookup_block lbl bbs)` by fs[dom_tree_labels_def] >>
      Cases_on `lookup_block lbl bbs` >> gvs[current_tree_trace_def] >>
      qmatch_asmsub_abbrev_tac `update_current_succ_phis rs1 lbl changed succs` >>
      `!l. IS_SOME (lookup_block l (update_current_succ_phis rs1 lbl changed succs)) <=>
           IS_SOME (lookup_block l bbs)` by
        (irule lookup_block_labels_agree >>
         simp[Abbr `changed`] >> irule current_edge_visit_labels >> simp[]) >>
      simp[current_event_label_def, dom_tree_labels_def] >>
      first_x_assum irule >> goal_assum $ drule_at Any >>
      fs[dom_tree_labels_def] >> metis_tac[])
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[current_tree_trace_def] >>
  `MAP (\bb. bb.bb_label) bbs1 = MAP (\bb. bb.bb_label) bbs` by
    metis_tac[cj 1 current_tree_trace_labels] >>
  drule lookup_block_labels_agree >> strip_tac >>
  simp[MAP_APPEND] >>
  `MAP current_event_label events1 = dom_tree_labels tree` by
    (first_x_assum irule >> goal_assum $ drule_at Any >> fs[]) >>
  simp[] >> first_x_assum irule >> goal_assum $ drule_at Any >>
  fs[] >> metis_tac[]
QED

Theorem current_tree_trace_event_labels_distinct:
  current_tree_trace A sm tree s rs bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  (!l. MEM l (dom_tree_labels tree) ==> IS_SOME (lookup_block l bbs)) /\
  ALL_DISTINCT (dom_tree_labels tree) ==>
  ALL_DISTINCT (MAP current_event_label events)
Proof
  strip_tac >> drule_all (cj 1 current_tree_trace_event_labels) >> simp[]
QED

Theorem current_tree_trace_event_coverage:
  current_tree_trace A sm tree s rs bbs H E visited
    ctrs' s' bbs' H' visited' events /\
  (!l. MEM l (dom_tree_labels tree) ==> IS_SOME (lookup_block l bbs)) /\
  MEM l (dom_tree_labels tree) ==>
  ?ev. MEM ev events /\ current_event_label ev = l
Proof
  strip_tac >> drule_all (cj 1 current_tree_trace_event_labels) >>
  metis_tac[MEM_MAP]
QED

Theorem current_provenance_tree_static_env:
  LENGTH olds = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,bbs)) annsss /\
  (!old. MEM old olds ==> lookup_block old.bb_label fn.fn_blocks = SOME old) /\
  (!l. MEM l (dom_tree_labels tree) ==> IS_SOME (lookup_block l bbs)) /\
  current_tree_trace (current_annotation_map bbs annsss) sm tree
    s rs bbs H CurrentDefault visited ctrs' s' bbs' H' visited' events /\
  MEM ev events ==>
  ?path. current_tree_ancestor_path tree (current_event_label ev) path /\
    (!v. current_event_entry_env ev v =
      current_inherited_token fn (current_actual_inserted fn) v path) /\
    (!v. current_event_exit_env ev v =
      current_block_token fn (current_actual_inserted fn) v (current_event_label ev)
        (current_inherited_token fn (current_actual_inserted fn) v path))
Proof
  strip_tac >>
  `!l E v. MEM l (dom_tree_labels tree) ==>
    current_advance_annotations (current_annotation_map bbs annsss) l E v =
      current_block_token fn (current_actual_inserted fn) v l (E v)` by
    (rpt strip_tac >> `IS_SOME (lookup_block l bbs)` by metis_tac[] >>
     Cases_on `lookup_block l bbs` >> fs[] >>
     drule_all current_provenance_annotation_map_scan >> simp[]) >>
  drule_all current_tree_trace_static_env >> simp[]
QED
