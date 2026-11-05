(* Query and strict-rank slice from the proved MakeSSA reference. *)
Theory makeSsaRfDomQuery
Ancestors dominatorProofs dominatorAnalysisProps dominatorDefs cfgDefs
  venomWf finite_map list pred_set

Theorem fmap_insert_list_mem:
  MEM c (fmap_lookup_list
    (m |+ (k,set_insert v (fmap_lookup_list m k))) n) <=>
  MEM c (fmap_lookup_list m n) \/ (n = k /\ c = v)
Proof
  Cases_on `n = k` >>
  simp[fmap_lookup_list_def, FLOOKUP_UPDATE, set_insert_def] >>
  Cases_on `FLOOKUP m k` >> simp[] >>
  Cases_on `MEM v x` >> simp[] >> metis_tac[]
QED

Theorem compute_dominated_fold_mem:
  !labels (idom:'a |-> 'b) (m:'b |-> 'a list) n c.
    MEM c (fmap_lookup_list
      (FOLDL (\m lbl. case FLOOKUP idom lbl of
          NONE => m
        | SOME parent => m |+ (parent,
             set_insert lbl (fmap_lookup_list m parent))) m labels) n) <=>
    MEM c (fmap_lookup_list m n) \/
    (MEM c labels /\ FLOOKUP idom c = SOME n)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `FLOOKUP idom h` >> simp[fmap_insert_list_mem] >>
  Cases_on `c = h` >> gvs[] >> metis_tac[]
QED

Theorem compute_dominated_membership:
  MEM c (fmap_lookup_list (compute_dominated idom labels) n) <=>
  MEM c labels /\ FLOOKUP idom c = SOME n
Proof
  simp[compute_dominated_def] >>
  once_rewrite_tac[compute_dominated_fold_mem] >>
  simp[fmap_lookup_list_def]
QED

Theorem compute_dominated_fold_distinct:
  !labels (idom:'a |-> 'b) (m:'b |-> 'a list).
    (!n. ALL_DISTINCT (fmap_lookup_list m n)) ==>
    !n. ALL_DISTINCT (fmap_lookup_list
      (FOLDL (\m lbl. case FLOOKUP idom lbl of
          NONE => m
        | SOME parent => m |+ (parent,
             set_insert lbl (fmap_lookup_list m parent))) m labels) n)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP idom h` >> simp[] >>
  first_x_assum irule >>
  gen_tac >> simp[fmap_lookup_list_def, FLOOKUP_UPDATE] >>
  IF_CASES_TAC >> gvs[] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  simp[fmap_lookup_list_def, set_insert_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem compute_dominated_distinct:
  ALL_DISTINCT (fmap_lookup_list (compute_dominated idom labels) n)
Proof
  simp[compute_dominated_def] >>
  irule compute_dominated_fold_distinct >> simp[fmap_lookup_list_def]
QED

Theorem dominated_query_membership:
  MEM c (dominated_of (dom_analyze cfg fn) n) <=>
  MEM c (fn_labels fn) /\ idom_of (dom_analyze cfg fn) c = SOME n
Proof
  simp[dominated_of_def, idom_of_def, dom_analyze_def,
       compute_dominated_membership]
QED

Theorem dominated_query_distinct:
  ALL_DISTINCT (dominated_of (dom_analyze cfg fn) n)
Proof
  simp[dominated_of_def, dom_analyze_def, compute_dominated_distinct]
QED

Definition dominator_query_rank_def:
  dominator_query_rank fn p =
    CARD (set (fmap_lookup_list
      (dom_analyze (cfg_analyze fn) fn).da_dominators p)) - 1
End

Theorem dominator_query_card_positive:
  wf_function fn /\ MEM p (fn_labels fn) ==>
  0 < CARD (set (fmap_lookup_list
    (dom_analyze (cfg_analyze fn) fn).da_dominators p))
Proof
  strip_tac >>
  `dominates (dom_analyze (cfg_analyze fn) fn) p p` by metis_tac[dom_self] >>
  gvs[dominates_def] >>
  `set (fmap_lookup_list
    (dom_analyze (cfg_analyze fn) fn).da_dominators p) <> {}` by
    metis_tac[MEMBER_NOT_EMPTY] >>
  metis_tac[CARD_EQ_0, FINITE_LIST_TO_SET, arithmeticTheory.NOT_ZERO_LT_ZERO]
QED

Theorem dominator_query_strict_subset:
  wf_function fn /\ MEM c (fn_labels fn) /\
  cfg_reachable_of (cfg_analyze fn) p /\
  cfg_reachable_of (cfg_analyze fn) c /\
  strict_dominates (dom_analyze (cfg_analyze fn) fn) p c ==>
  set (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators p)
    PSUBSET
  set (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators c)
Proof
  strip_tac >>
  `dominates (dom_analyze (cfg_analyze fn) fn) c c` by metis_tac[dom_self] >>
  `~dominates (dom_analyze (cfg_analyze fn) fn) c p` by
    (gvs[strict_dominates_def] >> metis_tac[dominates_antisym]) >>
  simp[PSUBSET_DEF] >> conj_tac
  >- (simp[SUBSET_DEF] >> rpt strip_tac >>
      fs[strict_dominates_def] >>
      metis_tac[dominates_trans, dominates_def]) >>
  simp[EXTENSION] >> qexists_tac `c` >> gvs[dominates_def]
QED

Theorem dominator_query_rank_strict:
  wf_function fn /\ MEM p (fn_labels fn) /\ MEM c (fn_labels fn) /\
  cfg_reachable_of (cfg_analyze fn) p /\
  cfg_reachable_of (cfg_analyze fn) c /\
  strict_dominates (dom_analyze (cfg_analyze fn) fn) p c ==>
  dominator_query_rank fn p < dominator_query_rank fn c
Proof
  strip_tac >> drule_all dominator_query_strict_subset >> strip_tac >>
  `CARD (set (fmap_lookup_list
      (dom_analyze (cfg_analyze fn) fn).da_dominators p)) <
   CARD (set (fmap_lookup_list
      (dom_analyze (cfg_analyze fn) fn).da_dominators c))` by
    (irule CARD_PSUBSET >> simp[]) >>
  `0 < CARD (set (fmap_lookup_list
      (dom_analyze (cfg_analyze fn) fn).da_dominators p))` by
    (irule dominator_query_card_positive >> simp[]) >>
  simp[dominator_query_rank_def] >> decide_tac
QED
