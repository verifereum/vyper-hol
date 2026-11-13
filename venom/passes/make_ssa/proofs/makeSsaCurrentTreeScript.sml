(* Finite traversal boundaries for the supply-aware dominator tree. *)
Theory makeSsaCurrentTree
Ancestors
  makeSsaDefs dominatorDefs relation list sorting combin

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

Theorem current_tree_postorder_root:
  MEM x (dom_tree_postorder (current_dom_tree_aux dom n x))
Proof
  Cases_on `n` >> simp[current_tree_postorder_mem_suc]
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

Theorem current_tree_rank_gap[local]:
  !a b c:num. a < b /\ b < c ==> ~(c <= a + 1)
Proof
  decide_tac
QED

Theorem current_tree_path_fuel:
  (!a. MEM a labels ==> (r a : num) < bound) /\
  (!a b. MEM a labels /\ current_tree_edge dom a b ==>
    MEM b labels /\ (r a : num) < r b) ==>
  !n x z. MEM x labels /\ bound <= n + r x + 1 /\
    RTC (current_tree_edge dom) x z ==>
    MEM z (dom_tree_postorder (current_dom_tree_aux dom n x))
Proof
  strip_tac >> Induct >> rpt strip_tac
  >- (gvs[Once RTC_CASES1] >> rename1 `current_tree_edge dom x y` >>
      first_x_assum drule >> strip_tac >>
      `r x < r y` by metis_tac[] >>
      `r y < bound` by metis_tac[] >>
      metis_tac[current_tree_rank_gap]) >>
  qpat_x_assum `RTC _ x z` mp_tac >>
  once_rewrite_tac[RTC_CASES1] >> strip_tac
  >- gvs[current_tree_postorder_root] >>
  rename1 `current_tree_edge dom x y` >>
  simp[current_tree_postorder_mem_suc] >> disj2_tac >>
  qexists `y` >> simp[] >> first_x_assum irule >>
  metis_tac[DECIDE ``a < b /\ c <= SUC n + a + 1 ==> c <= n + b + 1``]
QED

Theorem current_tree_root_path:
  (!a b. MEM a labels /\ current_tree_edge dom a b ==>
    MEM b labels /\ (r a : num) < r b) /\
  (!z. MEM z labels /\ z <> root ==>
    ?p. MEM p labels /\ current_tree_edge dom p z) ==>
  !z. MEM z labels ==> RTC (current_tree_edge dom) root z
Proof
  strip_tac >> gen_tac >> completeInduct_on `r z` >> rpt strip_tac >>
  Cases_on `z = root` >- simp[RTC_REFL] >>
  `?p. MEM p labels /\ current_tree_edge dom p z` by metis_tac[] >>
  `r p < r z` by metis_tac[] >>
  `RTC (current_tree_edge dom) root p` by metis_tac[] >>
  metis_tac[RTC_RULES_RIGHT1]
QED

Theorem current_tree_postorder_domain:
  (!a b. MEM a labels /\ current_tree_edge dom a b ==> MEM b labels) /\
  MEM x labels /\ MEM z (dom_tree_postorder (current_dom_tree_aux dom n x)) ==>
  MEM z labels
Proof
  metis_tac[current_tree_postorder_path, current_tree_path_domain]
QED

Theorem current_tree_postorder_coverage:
  MEM root labels /\
  (!a. MEM a labels ==> (r a : num) < LENGTH labels) /\
  (!a b. MEM a labels /\ current_tree_edge dom a b ==>
    MEM b labels /\ r a < r b) /\
  (!z. MEM z labels /\ z <> root ==>
    ?p. MEM p labels /\ current_tree_edge dom p z) ==>
  !z. MEM z (dom_tree_postorder
    (current_dom_tree_aux dom (LENGTH labels) root)) <=> MEM z labels
Proof
  rpt strip_tac >> eq_tac
  >- metis_tac[current_tree_postorder_domain] >>
  strip_tac >> irule current_tree_path_fuel >>
  conj_tac
  >- (qexistsl [`LENGTH labels`, `labels`, `r`] >> simp[] >> metis_tac[]) >>
  drule_all current_tree_root_path >> simp[]
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

Theorem current_tree_postorder_perm:
  ALL_DISTINCT labels /\ MEM root labels /\
  (!a. MEM a labels ==> ALL_DISTINCT (dominated_of dom a)) /\
  (!a b. MEM a labels /\ current_tree_edge dom a b ==>
    MEM b labels /\ (r a : num) < r b) /\
  (!p q y. MEM p labels /\ MEM q labels /\
    current_tree_edge dom p y /\ current_tree_edge dom q y ==> p = q) /\
  (!a. MEM a labels ==> r a < LENGTH labels) /\
  (!z. MEM z labels /\ z <> root ==>
    ?p. MEM p labels /\ current_tree_edge dom p z) ==>
  PERM (dom_tree_postorder
    (current_dom_tree_aux dom (LENGTH labels) root)) labels
Proof
  strip_tac >> irule PERM_ALL_DISTINCT >> simp[] >> conj_tac
  >- (drule_all current_tree_postorder_coverage >> simp[]) >>
  drule_all current_tree_postorder_distinct >> simp[]
QED

Theorem current_tree_zero_budget:
  (!a. MEM a labels ==> (r a : num) < bound) /\
  (!a b. MEM a labels /\ current_tree_edge dom a b ==>
    MEM b labels /\ r a < r b) /\
  MEM node labels /\ bound <= r node + 1 ==>
  dominated_of dom node = []
Proof
  rpt strip_tac >> Cases_on `dominated_of dom node` >> simp[] >>
  `current_tree_edge dom node h` by simp[current_tree_edge_def] >>
  `MEM h labels /\ r node < r h` by metis_tac[] >>
  `r h < bound` by metis_tac[] >> metis_tac[current_tree_rank_gap]
QED

Theorem current_tree_child_budget:
  (!a b. MEM a labels /\ current_tree_edge dom a b ==>
    MEM b labels /\ (r a : num) < r b) /\
  MEM node labels /\ bound <= SUC n + r node + 1 /\
  MEM child (dominated_of dom node) ==>
  MEM child labels /\ bound <= n + r child + 1
Proof
  rpt strip_tac >>
  `MEM child labels /\ r node < r child` by
    metis_tac[current_tree_edge_def] >> simp[] >>
  metis_tac[DECIDE ``a < b /\ c <= SUC n + a + 1 ==> c <= n + b + 1``]
QED

Theorem current_tree_fuel_stable:
  (!a. MEM a labels ==> (r a : num) < bound) /\
  (!a b. MEM a labels /\ current_tree_edge dom a b ==>
    MEM b labels /\ r a < r b) ==>
  !n node. MEM node labels /\ bound <= n + r node + 1 ==>
  !extra. current_dom_tree_aux dom n node =
    current_dom_tree_aux dom (n + extra) node
Proof
  strip_tac >> Induct >> rpt strip_tac
  >- (`dominated_of dom node = []` by
        (irule current_tree_zero_budget >>
         qexistsl [`bound`, `labels`, `r`] >> simp[] >> metis_tac[]) >>
      Cases_on `extra` >> simp[current_dom_tree_aux_def]) >>
  simp[arithmeticTheory.ADD_CLAUSES, current_dom_tree_aux_def] >>
  irule listTheory.MAP_CONG >> simp[] >>
  rpt strip_tac >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  first_x_assum irule >> drule_all current_tree_child_budget >> simp[]
QED

Theorem current_tree_root_fuel_stable:
  (!a. MEM a labels ==> (r a : num) < LENGTH labels) /\
  (!a b. MEM a labels /\ current_tree_edge dom a b ==>
    MEM b labels /\ r a < r b) /\ MEM root labels ==>
  !extra. current_dom_tree_aux dom (LENGTH labels) root =
    current_dom_tree_aux dom (LENGTH labels + extra) root
Proof
  rpt strip_tac >> irule current_tree_fuel_stable >>
  qexistsl [`LENGTH labels`, `labels`, `r`] >> simp[] >> metis_tac[]
QED
