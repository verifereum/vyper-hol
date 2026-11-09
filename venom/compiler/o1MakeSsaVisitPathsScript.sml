Theory o1MakeSsaVisitPaths
Ancestors
  o1MakeSsaVisitTrace o1MakeSsaReachableTree o1MakeSsaRootedTree
  o1MakeSsaActualMaps makeSsaDefs makeSsaCurrentInduct
  dominatorAnalysisProps venomInst list pair

Definition tree_parent_paths_def:
  tree_parent_paths parent root ancestors (DNode lbl children) <=>
    rooted_parent_path parent root ancestors lbl /\
    EVERY (tree_parent_paths parent root (lbl::ancestors)) children
End

Theorem aux_tree_parent_paths:
  (!a b. MEM b (dominated_of dom a) ==> parent b = SOME a) ==>
  !fuel lbl ancestors. rooted_parent_path parent root ancestors lbl ==>
    tree_parent_paths parent root ancestors (current_dom_tree_aux dom fuel lbl)
Proof
  strip_tac >> Induct >>
  simp[current_dom_tree_aux_def, tree_parent_paths_def, EVERY_MAP,
    EVERY_MEM, rooted_parent_path_def] >> metis_tac[]
QED

(* Soundness needs no lookup hypothesis: a missing block suppresses its entire
   subtree. Snapshots record the tree label, not an assumed block label. *)
Theorem visit_parent_paths:
  (!tree path s rs bbs sm parent root.
    tree_parent_paths parent root (REVERSE (MAP FST path)) tree ==>
    !e. MEM e (SND (visit_blocks path s rs bbs sm tree)) ==>
      rooted_parent_path parent root (REVERSE (MAP FST e.sve_path)) e.sve_label) /\
  (!trees path s ctrs stacks bbs sm parent root.
    EVERY (tree_parent_paths parent root (REVERSE (MAP FST path))) trees ==>
    !e. MEM e (SND (visit_children path s ctrs stacks bbs sm trees)) ==>
      rooted_parent_path parent root (REVERSE (MAP FST e.sve_path)) e.sve_label)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once visit_blocks_def, tree_parent_paths_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
      first_x_assum (qspec_then `path ++ [(lbl,x.bb_instructions,insts)]` mp_tac) >>
      simp[MAP_APPEND, REVERSE_APPEND] >> metis_tac[SND])
  >- simp[visit_blocks_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once visit_blocks_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> metis_tac[SND]
QED

Theorem actual_visit_path_dominators:
  wf_function fn /\ fn_entry_label fn = SOME entry /\
  MEM e (SND (visit_blocks [] s rs bbs sm (current_dom_tree fn))) /\
  cfg_reachable_of (cfg_analyze fn) e.sve_label ==>
  !d. MEM d (MAP FST e.sve_path) <=>
    strict_dominates (dom_analyze (cfg_analyze fn) fn) d e.sve_label
Proof
  strip_tac >>
  `tree_parent_paths (idom_of (dom_analyze (cfg_analyze fn) fn)) entry []
      (current_dom_tree fn)` by
    (simp[current_dom_tree_def] >> irule aux_tree_parent_paths >>
     simp[rooted_parent_path_def, actual_dom_children]) >>
  `rooted_parent_path (idom_of (dom_analyze (cfg_analyze fn) fn)) entry
      (REVERSE (MAP FST e.sve_path)) e.sve_label` by
    metis_tac[visit_parent_paths, MAP, REVERSE_DEF] >>
  `?bb. entry_block fn = SOME bb /\ bb.bb_label = entry` by
    fs[fn_entry_label_def, AllCaseEqs()] >>
  metis_tac[reachable_parent_path_dominators, MEM_REVERSE]
QED
