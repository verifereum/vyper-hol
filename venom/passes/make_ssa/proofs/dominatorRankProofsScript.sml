(* Bounded ranks for concrete dominator queries. *)
Theory dominatorRankProofs
Ancestors
  dominatorProofs dominatorDefs cfgDefs venomWf list pred_set

Theorem dominator_query_subset:
  wf_function fn /\ MEM p (fn_labels fn) ==>
  set (fmap_lookup_list
    (dom_analyze (cfg_analyze fn) fn).da_dominators p) SUBSET set (fn_labels fn)
Proof
  simp[SUBSET_DEF] >> rpt strip_tac >>
  metis_tac[dom_labels_bounded_proof]
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

Theorem dominator_query_rank_bound:
  wf_function fn /\ MEM p (fn_labels fn) ==>
  dominator_query_rank fn p < LENGTH (fn_labels fn)
Proof
  strip_tac >> drule_all dominator_query_subset >> strip_tac >>
  `CARD (set (fmap_lookup_list
      (dom_analyze (cfg_analyze fn) fn).da_dominators p)) <=
    CARD (set (fn_labels fn))` by
    (irule CARD_SUBSET >> simp[]) >>
  drule_all dominator_query_card_positive >>
  `CARD (set (fn_labels fn)) <= LENGTH (fn_labels fn)` by simp[CARD_LIST_TO_SET] >>
  simp[dominator_query_rank_def] >> decide_tac
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
