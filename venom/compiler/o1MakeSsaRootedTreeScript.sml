Theory o1MakeSsaRootedTree
Ancestors
  o1MakeSsaActualMaps dominatorProofs makeSsaCurrentDefs venomInst list

(* Ancestors are stored nearest first; the endpoint is separate. *)
Definition rooted_parent_path_def:
  (rooted_parent_path parent root [] node = (node = root)) /\
  (rooted_parent_path parent root (p::ps) node =
    (parent node = SOME p /\ rooted_parent_path parent root ps p))
End

Theorem rooted_parent_path_unique:
  !ps qs node. parent root = NONE /\
    rooted_parent_path parent root ps node /\
    rooted_parent_path parent root qs node ==> ps = qs
Proof
  Induct >> Cases_on `qs` >> simp[rooted_parent_path_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem rooted_parent_path_root_unique:
  !ps node a b. rooted_parent_path parent a ps node /\
    rooted_parent_path parent b ps node ==> a = b
Proof
  Induct >> simp[rooted_parent_path_def] >> metis_tac[]
QED

Theorem rooted_parent_path_append:
  !ps qs node mid root.
    rooted_parent_path parent mid ps node /\
    rooted_parent_path parent root qs mid ==>
    rooted_parent_path parent root (ps ++ qs) node
Proof
  Induct >> simp[rooted_parent_path_def] >> metis_tac[]
QED

Theorem rooted_tree_member_path:
  (!a b. MEM b (dominated_of dom a) ==> parent b = SOME a) ==>
  !fuel node z. MEM z (dom_tree_postorder (current_dom_tree_aux dom fuel node)) ==>
    ?ps. rooted_parent_path parent node ps z
Proof
  strip_tac >> Induct >>
  simp[current_dom_tree_aux_def, dom_tree_postorder_def, MEM_FLAT, MEM_MAP,
    PULL_EXISTS] >> rpt strip_tac
  >- (qexists `[]` >> simp[rooted_parent_path_def])
  >- (rename1 `MEM child (dominated_of dom node)` >>
      first_x_assum drule >> strip_tac >>
      qexists `ps ++ [node]` >> irule rooted_parent_path_append >>
      qexists `child` >> simp[rooted_parent_path_def] >> metis_tac[])
  >> qexists `[]` >> simp[rooted_parent_path_def]
QED

Theorem rooted_tree_siblings_disjoint:
  (!a b. MEM b (dominated_of dom a) ==> parent b = SOME a) /\
  parent root = NONE /\ rooted_parent_path parent root ancestors node /\
  MEM a (dominated_of dom node) /\ MEM b (dominated_of dom node) /\
  MEM z (dom_tree_postorder (current_dom_tree_aux dom n a)) /\
  MEM z (dom_tree_postorder (current_dom_tree_aux dom m b)) ==> a = b
Proof
  strip_tac >>
  `?ps. rooted_parent_path parent a ps z` by
    metis_tac[rooted_tree_member_path] >>
  `?qs. rooted_parent_path parent b qs z` by
    metis_tac[rooted_tree_member_path] >>
  `rooted_parent_path parent root (node::ancestors) a /\
   rooted_parent_path parent root (node::ancestors) b` by
    simp[rooted_parent_path_def] >>
  `rooted_parent_path parent root (ps ++ node::ancestors) z /\
   rooted_parent_path parent root (qs ++ node::ancestors) z` by
    metis_tac[rooted_parent_path_append] >>
  `ps ++ node::ancestors = qs ++ node::ancestors` by
    metis_tac[rooted_parent_path_unique] >>
  `ps = qs` by fs[] >> metis_tac[rooted_parent_path_root_unique]
QED

Theorem rooted_tree_parent_absent:
  (!a b. MEM b (dominated_of dom a) ==> parent b = SOME a) /\
  parent root = NONE /\ rooted_parent_path parent root ancestors node /\
  MEM child (dominated_of dom node) ==>
  ~MEM node (dom_tree_postorder (current_dom_tree_aux dom n child))
Proof
  strip_tac >> strip_tac >>
  `?ps. rooted_parent_path parent child ps node` by
    metis_tac[rooted_tree_member_path] >>
  `rooted_parent_path parent root (node::ancestors) child` by
    simp[rooted_parent_path_def] >>
  `rooted_parent_path parent root (ps ++ node::ancestors) node` by
    metis_tac[rooted_parent_path_append] >>
  `ps ++ node::ancestors = ancestors` by
    metis_tac[rooted_parent_path_unique] >>
  `LENGTH (ps ++ node::ancestors) = LENGTH ancestors` by metis_tac[] >> fs[]
QED

(* Ported from the reference Tree theory: purely a list boundary. *)
Theorem rooted_tree_postorder_distinct:
  (!a. ALL_DISTINCT (dominated_of dom a)) /\
  (!a b. MEM b (dominated_of dom a) ==> parent b = SOME a) /\
  parent root = NONE ==>
  !fuel node ancestors. rooted_parent_path parent root ancestors node ==>
    ALL_DISTINCT (dom_tree_postorder (current_dom_tree_aux dom fuel node))
Proof
  strip_tac >> Induct >- simp[current_dom_tree_aux_def, dom_tree_postorder_def] >>
  rpt strip_tac >>
  simp[current_dom_tree_aux_def, dom_tree_postorder_def, MAP_MAP_o,
    combinTheory.o_DEF, ALL_DISTINCT_APPEND] >> conj_tac
  >- (`!(g:string -> string list) (ys:string list). ALL_DISTINCT ys /\ (!a. MEM a ys ==> ALL_DISTINCT (g a)) /\
           (!a b c. MEM a ys /\ MEM b ys /\ MEM c (g a) /\ MEM c (g b) ==> a = b)
           ==> ALL_DISTINCT (FLAT (MAP g ys))`
        by (Induct_on `ys` >>
            simp[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
            rpt strip_tac >> metis_tac[]) >>
      pop_assum irule >> simp[] >> conj_tac
      >- (rpt strip_tac >> irule rooted_tree_siblings_disjoint >>
          metis_tac[]) >>
      rpt strip_tac >> first_x_assum irule >>
      qexists `node::ancestors` >> simp[rooted_parent_path_def]) >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
  metis_tac[rooted_tree_parent_absent]
QED

Theorem actual_rooted_tree_distinct:
  wf_function fn /\ fn_entry_label fn = SOME entry ==>
    ALL_DISTINCT (dom_tree_postorder (current_dom_tree fn))
Proof
  strip_tac >>
  `?bb. entry_block fn = SOME bb /\ bb.bb_label = entry` by
    (fs[fn_entry_label_def, AllCaseEqs()]) >>
  `idom_of (dom_analyze (cfg_analyze fn) fn) entry = NONE` by
    metis_tac[idom_entry_none] >>
  simp[current_dom_tree_def] >>
  irule rooted_tree_postorder_distinct >>
  simp[actual_dom_children_distinct] >>
  qexistsl [`[]`, `idom_of (dom_analyze (cfg_analyze fn) fn)`, `entry`] >>
  simp[rooted_parent_path_def, actual_dom_children_distinct,
    actual_dom_children]
QED
