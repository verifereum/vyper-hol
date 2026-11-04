Theory makeSsaCurrentTokenGraph
Ancestors
  makeSsaCurrentTokens makeSsaCurrentAnalysis makeSsaCurrentTree
  dominatorAnalysisProps dominatorRankProofs

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
