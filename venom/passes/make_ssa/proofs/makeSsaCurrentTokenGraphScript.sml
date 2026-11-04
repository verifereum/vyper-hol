Theory makeSsaCurrentTokenGraph
Ancestors
  makeSsaCurrentTokens makeSsaCurrentAnalysis makeSsaCurrentTree
  dominatorAnalysisProps dominatorRankProofs dominatorDefs pred_set

Theorem current_token_root_idom:
  wf_function fn /\ entry_block fn = SOME eb ==>
  idom_of (dom_analyze (cfg_analyze fn) fn) eb.bb_label = NONE
Proof
  metis_tac[idom_entry_none]
QED

Theorem current_actual_token_chain:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM l (fn_labels fn) ==>
  ?ps. current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps l
Proof
  completeInduct_on `dominator_query_rank fn l` >> rpt strip_tac >>
  Cases_on `l = eb.bb_label`
  >- (qexists_tac `[]` >> simp[current_token_chain_def]) >>
  drule_all current_dom_parent_exists >> strip_tac >>
  `dominator_query_rank fn p < dominator_query_rank fn l` by
    metis_tac[current_dom_child_rank] >>
  first_x_assum (qspec_then `dominator_query_rank fn p` mp_tac) >>
  simp[] >> disch_then (qspecl_then [`fn`, `p`] mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `p::ps` >> irule current_token_chain_parent >>
  gvs[current_tree_edge_def, dominatorQueryProofsTheory.dominated_query_membership]
QED

Theorem current_actual_token_chain_unique:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM l (fn_labels fn) ==>
  ?!ps. current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps l
Proof
  strip_tac >> simp[EXISTS_UNIQUE_THM] >> conj_tac
  >- metis_tac[current_actual_token_chain] >>
  metis_tac[current_token_chain_unique, current_token_root_idom]
QED

Theorem current_actual_root_chain:
  wf_function fn /\ entry_block fn = SOME eb ==>
  (current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps
     eb.bb_label <=> ps = [])
Proof
  metis_tac[current_token_root_idom, current_token_chain_root]
QED

Theorem current_actual_root_token:
  wf_function fn /\ entry_block fn = SOME eb /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps eb.bb_label ==>
  current_inherited_token fn ins v (REVERSE ps) = CurrentDefault v
Proof
  strip_tac >> `ps = []` by metis_tac[current_actual_root_chain] >>
  simp[current_inherited_token_root]
QED

Theorem current_single_pred_dominates:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM b (fn_labels fn) /\ b <> eb.bb_label /\
  set (cfg_preds_of (cfg_analyze fn) b) = {a} ==>
  !d. dominates (dom_analyze (cfg_analyze fn) fn) d b <=>
      d = b \/ dominates (dom_analyze (cfg_analyze fn) fn) d a
Proof
  strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) b` by
    metis_tac[current_all_labels_reachable] >>
  `cfg_preds_of (cfg_analyze fn) b <> []` by
    (strip_tac >> gvs[]) >>
  qspecl_then [`fn`, `cfg_analyze fn`, `eb`, `b`] mp_tac dom_fixpoint_equation >>
  simp[] >> strip_tac >>
  simp[dominates_def] >> metis_tac[IN_UNION, IN_SING, listTheory.MEM]
QED

Theorem current_single_pred_idom:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM a (fn_labels fn) /\ MEM b (fn_labels fn) /\
  b <> eb.bb_label /\ a <> b /\
  set (cfg_preds_of (cfg_analyze fn) b) = {a} ==>
  idom_of (dom_analyze (cfg_analyze fn) fn) b = SOME a
Proof
  strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) a /\
   cfg_reachable_of (cfg_analyze fn) b` by
    metis_tac[current_all_labels_reachable] >>
  `?d. idom_of (dom_analyze (cfg_analyze fn) fn) b = SOME d` by
    metis_tac[idom_exists] >>
  `strict_dominates (dom_analyze (cfg_analyze fn) fn) a b` by
    (simp[strict_dominates_def] >>
     drule_all current_single_pred_dominates >>
     disch_then (qspec_then `a` mp_tac) >> metis_tac[dom_self]) >>
  `strict_dominates (dom_analyze (cfg_analyze fn) fn) d b /\
   (!c. strict_dominates (dom_analyze (cfg_analyze fn) fn) c b /\ c <> d ==>
     dominates (dom_analyze (cfg_analyze fn) fn) c d)` by
    metis_tac[idom_is_immediate] >>
  Cases_on `a = d` >- gvs[] >>
  `dominates (dom_analyze (cfg_analyze fn) fn) a d` by metis_tac[] >>
  `dominates (dom_analyze (cfg_analyze fn) fn) d a` by
    (drule_all current_single_pred_dominates >>
     disch_then (qspec_then `d` mp_tac) >> gvs[strict_dominates_def]) >>
  `cfg_reachable_of (cfg_analyze fn) d` by metis_tac[dominates_reachable] >>
  metis_tac[dominates_antisym]
QED

Theorem current_single_pred_token:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM a (fn_labels fn) /\ MEM b (fn_labels fn) /\
  b <> eb.bb_label /\ a <> b /\
  set (cfg_preds_of (cfg_analyze fn) b) = {a} /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b ==>
  current_block_token fn ins v a (current_inherited_token fn ins v (REVERSE ps)) =
  current_inherited_token fn ins v (REVERSE qs)
Proof
  strip_tac >> sym_tac >> irule current_token_parent_edge >>
  metis_tac[current_single_pred_idom, current_token_root_idom]
QED
