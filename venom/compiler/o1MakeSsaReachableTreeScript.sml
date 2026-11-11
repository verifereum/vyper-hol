Theory o1MakeSsaReachableTree
Ancestors
  o1MakeSsaRootedTree dominatorRankProofs o1MakeSsaActualMaps
  dominatorProofs dominatorDefs cfgAnalysisProps cfgDefs venomInst
  makeSsaCurrentDefs list pred_set cfgCorrectnessProof

Theorem reachable_parent_chain:
  wf_function fn /\ entry_block fn = SOME bb ==>
  !p. cfg_reachable_of (cfg_analyze fn) p ==>
  ?ps. rooted_parent_path (idom_of (dom_analyze (cfg_analyze fn) fn))
      bb.bb_label ps p /\
    EVERY (cfg_reachable_of (cfg_analyze fn)) (p::ps) /\
    LENGTH ps <= dominator_query_rank fn p
Proof
  strip_tac >> gen_tac >> completeInduct_on `dominator_query_rank fn p` >>
  rpt strip_tac >> Cases_on `p = bb.bb_label`
  >- (qexists `[]` >> simp[rooted_parent_path_def]) >>
  `?d. idom_of (dom_analyze (cfg_analyze fn) fn) p = SOME d` by
    metis_tac[idom_exists] >>
  `strict_dominates (dom_analyze (cfg_analyze fn) fn) d p` by
    metis_tac[idom_is_immediate] >>
  `cfg_reachable_of (cfg_analyze fn) d` by
    metis_tac[dominates_reachable, strict_dominates_def] >>
  `dominator_query_rank fn d < dominator_query_rank fn p` by
    (irule dominator_query_rank_strict >>
     metis_tac[cfg_analyze_reachable_in_labels]) >>
  `?ps. rooted_parent_path (idom_of (dom_analyze (cfg_analyze fn) fn))
      bb.bb_label ps d /\
    EVERY (cfg_reachable_of (cfg_analyze fn)) (d::ps) /\
    LENGTH ps <= dominator_query_rank fn d` by metis_tac[] >>
  qexists `d::ps` >> simp[rooted_parent_path_def] >> decide_tac
QED

Theorem tree_member_suc:
  MEM p (dom_tree_postorder (current_dom_tree_aux dom (SUC fuel) root)) <=>
    p = root \/ ?child. MEM child (dominated_of dom root) /\
      MEM p (dom_tree_postorder (current_dom_tree_aux dom fuel child))
Proof
  simp[current_dom_tree_aux_def, dom_tree_postorder_def, MEM_FLAT,
    MEM_MAP, MAP_MAP_o, combinTheory.o_DEF] >> metis_tac[]
QED

Theorem tree_member_child_extension:
  !fuel root p node.
    MEM p (dom_tree_postorder (current_dom_tree_aux dom fuel root)) /\
    MEM node (dominated_of dom p) ==>
    MEM node (dom_tree_postorder (current_dom_tree_aux dom (SUC fuel) root))
Proof
  Induct
  >- (simp[tree_member_suc, current_dom_tree_aux_def, dom_tree_postorder_def,
        MAP_MAP_o, combinTheory.o_DEF] >> metis_tac[]) >>
  rpt gen_tac >> pure_once_rewrite_tac[tree_member_suc] >>
  rpt strip_tac
  >- (simp[tree_member_suc] >> metis_tac[]) >>
  disj2_tac >> goal_assum (drule_at Any) >>
  first_x_assum drule_all >> simp[tree_member_suc]
QED

Theorem tree_member_more_fuel:
  !fuel extra root p.
    MEM p (dom_tree_postorder (current_dom_tree_aux dom fuel root)) ==>
    MEM p (dom_tree_postorder (current_dom_tree_aux dom (fuel + extra) root))
Proof
  Induct
  >- (rpt strip_tac >> gvs[current_dom_tree_aux_def, dom_tree_postorder_def] >>
      Cases_on `extra` >> simp[tree_member_suc, current_dom_tree_aux_def,
        dom_tree_postorder_def]) >>
  rpt gen_tac >> rewrite_tac[arithmeticTheory.ADD_CLAUSES] >>
  pure_once_rewrite_tac[tree_member_suc] >> metis_tac[]
QED

Theorem reachable_path_in_tree:
  !ps p. rooted_parent_path (idom_of (dom_analyze (cfg_analyze fn) fn))
      root ps p /\ EVERY (cfg_reachable_of (cfg_analyze fn)) (p::ps) ==>
    MEM p (dom_tree_postorder (current_dom_tree_aux
      (dom_analyze (cfg_analyze fn) fn) (LENGTH ps) root))
Proof
  Induct
  >- simp[rooted_parent_path_def, current_dom_tree_aux_def, dom_tree_postorder_def] >>
  simp[rooted_parent_path_def] >> rpt strip_tac >>
  irule tree_member_child_extension >> qexists `h` >>
  simp[actual_dom_children] >> metis_tac[cfg_analyze_reachable_in_labels]
QED

Theorem actual_reachable_tree_coverage:
  wf_function fn /\ fn_entry_label fn = SOME entry /\
  cfg_reachable_of (cfg_analyze fn) p ==>
    MEM p (dom_tree_postorder (current_dom_tree fn))
Proof
  strip_tac >>
  `?bb. entry_block fn = SOME bb /\ bb.bb_label = entry` by
    fs[fn_entry_label_def, AllCaseEqs()] >>
  drule_all reachable_parent_chain >> strip_tac >>
  `MEM p (dom_tree_postorder (current_dom_tree_aux
    (dom_analyze (cfg_analyze fn) fn) (LENGTH ps) entry))` by
    metis_tac[reachable_path_in_tree] >>
  `dominator_query_rank fn p < LENGTH (fn_labels fn)` by
    metis_tac[dominator_query_rank_bound, cfg_analyze_reachable_in_labels] >>
  `LENGTH (fn_labels fn) = LENGTH ps + (LENGTH (fn_labels fn) - LENGTH ps)` by
    decide_tac >>
  simp[current_dom_tree_def] >> metis_tac[tree_member_more_fuel]
QED

Theorem reachable_idom_strict:
  wf_function fn /\ cfg_reachable_of (cfg_analyze fn) p /\
  idom_of (dom_analyze (cfg_analyze fn) fn) p = SOME h ==>
  (strict_dominates (dom_analyze (cfg_analyze fn) fn) d p <=>
    d = h \/ strict_dominates (dom_analyze (cfg_analyze fn) fn) d h)
Proof
  strip_tac >>
  `strict_dominates (dom_analyze (cfg_analyze fn) fn) h p /\
   (!d'. strict_dominates (dom_analyze (cfg_analyze fn) fn) d' p /\ d' <> h ==>
      dominates (dom_analyze (cfg_analyze fn) fn) d' h)` by
    metis_tac[idom_is_immediate] >>
  `cfg_reachable_of (cfg_analyze fn) h` by
    metis_tac[dominates_reachable, strict_dominates_def] >>
  eq_tac
  >- (gvs[strict_dominates_def] >> metis_tac[]) >>
  strip_tac >- simp[] >>
  gvs[strict_dominates_def] >>
  `dominates (dom_analyze (cfg_analyze fn) fn) d p` by
    metis_tac[dominates_trans] >>
  metis_tac[dominates_antisym]
QED

Theorem reachable_parent_path_dominators:
  wf_function fn /\ entry_block fn = SOME bb ==>
  !ps p. rooted_parent_path (idom_of (dom_analyze (cfg_analyze fn) fn))
      bb.bb_label ps p /\ cfg_reachable_of (cfg_analyze fn) p ==>
    !d. MEM d ps <=> strict_dominates (dom_analyze (cfg_analyze fn) fn) d p
Proof
  strip_tac >> Induct
  >- (simp[rooted_parent_path_def] >> rpt strip_tac >>
      `set (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators
         bb.bb_label) = {bb.bb_label}` by metis_tac[dom_entry_self] >>
      fs[strict_dominates_def, dominates_def, EXTENSION] >> metis_tac[]) >>
  simp[rooted_parent_path_def] >> rpt strip_tac >>
  `strict_dominates (dom_analyze (cfg_analyze fn) fn) h p` by
    metis_tac[idom_is_immediate] >>
  `cfg_reachable_of (cfg_analyze fn) h` by
    metis_tac[dominates_reachable, strict_dominates_def] >>
  `MEM d ps <=> strict_dominates (dom_analyze (cfg_analyze fn) fn) d h` by
    metis_tac[] >>
  metis_tac[reachable_idom_strict]
QED
