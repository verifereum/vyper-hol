(* Finite-tree distinctness slice from the proved MakeSSA reference. *)
Theory makeSsaRfDomDistinct
Ancestors makeSsaRfDomQuery makeSsaCurrentDefs makeSsaCurrentInduct makeSsaDefs
  dominatorDefs relation list sorting combin cfgAnalysisProps cfgHelpers
  dominatorAnalysisProps venomWf cfgWf cfgDefs venomInst venomExecProps

Definition current_tree_edge_def:
  current_tree_edge dom x y <=> MEM y (dominated_of dom x)
End

Theorem current_tree_postorder_zero[simp]:
  dom_tree_postorder (current_dom_tree_aux dom 0 x) = [x]
Proof
  simp[current_dom_tree_aux_def, dom_tree_postorder_def]
QED

Theorem current_tree_postorder_suc:
  dom_tree_postorder (current_dom_tree_aux dom (SUC n) x) =
  FLAT (MAP (\y. dom_tree_postorder (current_dom_tree_aux dom n y))
    (dominated_of dom x)) ++ [x]
Proof
  simp[current_dom_tree_aux_def, dom_tree_postorder_def, MAP_MAP_o, o_DEF]
QED

Theorem current_tree_postorder_mem_suc:
  MEM z (dom_tree_postorder (current_dom_tree_aux dom (SUC n) x)) <=>
  z = x \/ ?y. current_tree_edge dom x y /\
    MEM z (dom_tree_postorder (current_dom_tree_aux dom n y))
Proof
  simp[current_tree_postorder_suc, MEM_FLAT, MEM_MAP, current_tree_edge_def] >>
  metis_tac[]
QED

Theorem current_tree_postorder_path:
  !n x z. MEM z (dom_tree_postorder (current_dom_tree_aux dom n x)) ==>
    RTC (current_tree_edge dom) x z
Proof
  Induct >> simp[current_tree_postorder_mem_suc] >> rpt strip_tac >>
  metis_tac[RTC_REFL, RTC_RULES]
QED

Theorem current_tree_path_domain:
  (!a b. MEM a labels /\ current_tree_edge dom a b ==> MEM b labels) ==>
  !x z. RTC (current_tree_edge dom) x z ==> MEM x labels ==> MEM z labels
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT >> simp[] >> metis_tac[]
QED

Theorem current_tree_path_rank:
  (!a b. MEM a labels /\ current_tree_edge dom a b ==>
    MEM b labels /\ (r a : num) < r b) ==>
  !x z. RTC (current_tree_edge dom) x z ==> MEM x labels ==> r x <= r z
Proof
  strip_tac >> ho_match_mp_tac RTC_INDUCT >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  first_x_assum drule >> decide_tac
QED

Theorem current_tree_path_comparable:
  (!x y. MEM x labels /\ current_tree_edge dom x y ==>
    MEM y labels /\ (r x : num) < r y) /\
  (!p q y. MEM p labels /\ MEM q labels /\
    current_tree_edge dom p y /\ current_tree_edge dom q y ==> p = q) ==>
  !z a b. MEM a labels /\ MEM b labels /\
    RTC (current_tree_edge dom) a z /\ RTC (current_tree_edge dom) b z ==>
    RTC (current_tree_edge dom) a b \/ RTC (current_tree_edge dom) b a
Proof
  strip_tac >> gen_tac >> completeInduct_on `r z` >> rpt strip_tac >>
  Cases_on `a = z` >- gvs[] >>
  Cases_on `b = z` >- gvs[] >>
  `?p. RTC (current_tree_edge dom) a p /\ current_tree_edge dom p z`
    by metis_tac[RTC_CASES2] >>
  `?q. RTC (current_tree_edge dom) b q /\ current_tree_edge dom q z`
    by metis_tac[RTC_CASES2] >>
  `MEM p labels /\ MEM q labels` by
    metis_tac[current_tree_path_domain] >>
  `p = q` by metis_tac[] >> gvs[] >>
  rename1 `current_tree_edge dom c z` >>
  `r c < r z` by metis_tac[] >>
  qpat_x_assum `!m. _` (qspec_then `r c` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`r`, `c`] mp_tac) >> simp[] >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qspecl_then [`a`, `b`] mp_tac) >> simp[]
QED

Theorem current_tree_sibling_not_path:
  (!a b. MEM a labels /\ current_tree_edge dom a b ==>
    MEM b labels /\ (r a : num) < r b) /\
  (!p q y. MEM p labels /\ MEM q labels /\
    current_tree_edge dom p y /\ current_tree_edge dom q y ==> p = q) /\
  MEM x labels /\ current_tree_edge dom x a /\ current_tree_edge dom x b /\
  RTC (current_tree_edge dom) a b ==> a = b
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `MEM a labels /\ MEM b labels` by metis_tac[] >>
  `?p. RTC (current_tree_edge dom) a p /\ current_tree_edge dom p b`
    by metis_tac[RTC_CASES2] >>
  `MEM p labels` by metis_tac[current_tree_path_domain] >>
  `p = x` by metis_tac[] >> gvs[] >>
  rename1 `current_tree_edge dom c a` >>
  `r a <= r c` by
    (drule_all current_tree_path_rank >> simp[]) >>
  `r c < r a` by metis_tac[] >> fs[]
QED

Theorem current_tree_sibling_disjoint:
  (!x y. MEM x labels /\ current_tree_edge dom x y ==>
    MEM y labels /\ (r x : num) < r y) /\
  (!p q y. MEM p labels /\ MEM q labels /\
    current_tree_edge dom p y /\ current_tree_edge dom q y ==> p = q) /\
  MEM x labels /\ current_tree_edge dom x a /\ current_tree_edge dom x b /\
  MEM z (dom_tree_postorder (current_dom_tree_aux dom n a)) /\
  MEM z (dom_tree_postorder (current_dom_tree_aux dom m b)) ==> a = b
Proof
  rpt strip_tac >>
  `MEM a labels /\ MEM b labels` by metis_tac[] >>
  `RTC (current_tree_edge dom) a z /\ RTC (current_tree_edge dom) b z`
    by metis_tac[current_tree_postorder_path] >>
  `RTC (current_tree_edge dom) a b \/ RTC (current_tree_edge dom) b a` by
    (irule current_tree_path_comparable >> conj_tac
     >- (qexistsl [`labels`, `r`] >> simp[] >> metis_tac[]) >>
     qexists `z` >> simp[]) >>
  drule_all current_tree_sibling_not_path >> simp[]
QED

Theorem distinct_flat_map_quantified[local]:
  !g ys. ALL_DISTINCT ys /\
    (!a. MEM a ys ==> ALL_DISTINCT (g a)) /\
    (!a b c. MEM a ys /\ MEM b ys /\ MEM c (g a) /\ MEM c (g b) ==> a = b)
    ==> ALL_DISTINCT (FLAT (MAP g ys))
Proof
  Induct_on `ys` >>
  simp[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem current_tree_parent_not_in_child:
  (!a b. MEM a labels /\ current_tree_edge dom a b ==>
    MEM b labels /\ (r a : num) < r b) /\
  MEM parent labels /\ current_tree_edge dom parent child ==>
  ~MEM parent (dom_tree_postorder (current_dom_tree_aux dom n child))
Proof
  rpt strip_tac >>
  `MEM child labels /\ r parent < r child` by metis_tac[] >>
  `RTC (current_tree_edge dom) child parent` by
    metis_tac[current_tree_postorder_path] >>
  `r child <= r parent` by
    (drule_all current_tree_path_rank >> simp[]) >> fs[]
QED

Theorem current_tree_postorder_distinct:
  (!a. MEM a labels ==> ALL_DISTINCT (dominated_of dom a)) /\
  (!a b. MEM a labels /\ current_tree_edge dom a b ==>
    MEM b labels /\ (r a : num) < r b) /\
  (!p q y. MEM p labels /\ MEM q labels /\
    current_tree_edge dom p y /\ current_tree_edge dom q y ==> p = q) ==>
  !n node. MEM node labels ==>
    ALL_DISTINCT (dom_tree_postorder (current_dom_tree_aux dom n node))
Proof
  strip_tac >> Induct >- simp[] >> rpt strip_tac >>
  simp[current_tree_postorder_suc, ALL_DISTINCT_APPEND] >> conj_tac
  >- (irule distinct_flat_map_quantified >> conj_tac
      >- (rpt strip_tac >> irule current_tree_sibling_disjoint >>
          qexistsl [`dom`, `labels`, `n`, `n`, `r`, `node`, `c`] >>
          gvs[current_tree_edge_def] >> metis_tac[]) >>
      simp[] >> rpt strip_tac >> first_x_assum irule >>
      metis_tac[current_tree_edge_def]) >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
  metis_tac[current_tree_parent_not_in_child, current_tree_edge_def]
QED

Theorem current_cfg_edge_succs:
  wf_function fn ==>
  (fn_cfg_edge fn a b <=> MEM b (cfg_succs_of (cfg_analyze fn) a))
Proof
  strip_tac >> eq_tac
  >- (rw[fn_cfg_edge_def] >>
      drule_all cfg_analyze_preserves_bb_succs >> simp[]) >>
  strip_tac >>
  `MEM a (fn_labels fn)` by
    (spose_not_then assume_tac >>
     gvs[cfg_analyze_succs, fn_labels_def, cfg_succs_of_not_in_labels]) >>
  gvs[fn_labels_def, MEM_MAP] >>
  drule_all cfg_analyze_preserves_bb_succs >> strip_tac >>
  simp[fn_cfg_edge_def] >> metis_tac[]
QED

Theorem current_cfg_path:
  wf_function fn ==>
  cfgDefs$cfg_path (cfg_analyze fn) = RTC (fn_cfg_edge fn)
Proof
  strip_tac >>
  `fn_cfg_edge fn = (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a))` by
    simp[FUN_EQ_THM, current_cfg_edge_succs] >>
  simp[cfgDefsTheory.cfg_path_def]
QED

Theorem current_cfg_reachable:
  wf_function fn ==>
  (cfg_reachable_of (cfg_analyze fn) lbl <=> fn_reachable fn lbl)
Proof
  strip_tac >> Cases_on `entry_block fn`
  >- (gvs[entry_block_def, NULL_EQ, cfg_analyze_def, fn_reachable_def,
          fn_entry_label_def, cfg_reachable_of_def,
          fmap_lookup_list_def, build_reachable_def]) >>
  drule_all cfg_analyze_semantic_reachability >>
  simp[current_cfg_path, fn_reachable_def, fn_entry_label_def]
QED

Theorem current_all_labels_reachable:
  wf_function fn /\ all_reachable fn /\ MEM lbl (fn_labels fn) ==>
  cfg_reachable_of (cfg_analyze fn) lbl
Proof
  simp[current_cfg_reachable] >>
  rw[all_reachable_def, fn_labels_def, MEM_MAP] >> metis_tac[]
QED

Theorem current_dom_child_reachable:
  wf_function fn /\ all_reachable fn /\
  MEM c (dominated_of (dom_analyze (cfg_analyze fn) fn) n) ==>
  cfg_reachable_of (cfg_analyze fn) c
Proof
  rw[dominated_query_membership] >>
  irule current_all_labels_reachable >> simp[]
QED

Theorem current_dom_child_strict:
  wf_function fn /\ all_reachable fn /\
  MEM c (dominated_of (dom_analyze (cfg_analyze fn) fn) n) ==>
  strict_dominates (dom_analyze (cfg_analyze fn) fn) n c
Proof
  rpt strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) c` by
    (irule current_dom_child_reachable >> metis_tac[]) >>
  gvs[dominated_query_membership] >>
  metis_tac[idom_is_immediate]
QED

Theorem current_dom_child_rank:
  wf_function fn /\ all_reachable fn /\ MEM n (fn_labels fn) /\
  current_tree_edge (dom_analyze (cfg_analyze fn) fn) n c ==>
  MEM c (fn_labels fn) /\ dominator_query_rank fn n < dominator_query_rank fn c
Proof
  simp[current_tree_edge_def] >> strip_tac >>
  `MEM c (fn_labels fn)` by metis_tac[dominated_query_membership] >>
  simp[] >> irule dominator_query_rank_strict >> simp[] >>
  metis_tac[current_all_labels_reachable, current_dom_child_strict]
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
  wf_function fn /\ all_reachable fn ==>
  ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))
Proof
  strip_tac >> Cases_on `fn_entry_label fn`
  >- simp[current_dom_tree_def, dom_tree_labels_def] >>
  `MEM x (fn_labels fn)` by
    (gvs[fn_entry_label_def, entry_block_def, AllCaseEqs()] >>
     Cases_on `fn.fn_blocks` >> gvs[fn_labels_def]) >>
  simp[current_dom_tree_def, current_tree_labels_postorder] >>
  irule current_tree_postorder_distinct >>
  qexistsl [`fn_labels fn`, `dominator_query_rank fn`] >> simp[] >>
  conj_tac
  >- (simp[current_tree_edge_def, dominated_query_membership] >> rpt strip_tac >> gvs[]) >>
  conj_tac >- metis_tac[current_dom_child_rank] >>
  simp[dominated_query_distinct]
QED
