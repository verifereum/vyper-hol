Theory makeSsaCurrentSingletonCut
Ancestors
  makeSsaCurrentCutTokens makeSsaCurrentLastSite makeSsaCurrentTokens
  makeSsaCurrentAnalysis dominatorDefs dominatorAnalysisProps venomWf list

Theorem current_single_site_edge_tokens:
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn a b /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b /\
  MEM d (fn_labels fn) /\
  strict_dominates (dom_analyze (cfg_analyze fn) fn) d b /\
  current_changing_site fn ins v d /\
  (!l. current_changing_site fn ins v l ==> l = d) ==>
  current_block_token fn ins v a (current_inherited_token fn ins v (REVERSE ps)) =
  current_inherited_token fn ins v (REVERSE qs)
Proof
  strip_tac >>
  `dominates (dom_analyze (cfg_analyze fn) fn) d a` by
    metis_tac[current_strict_dom_cfg_pred] >>
  `!e. current_changing_site fn ins v e /\
    dominates (dom_analyze (cfg_analyze fn) fn) e a ==>
    dominates (dom_analyze (cfg_analyze fn) fn) e d` by
    metis_tac[dom_self, current_all_labels_reachable] >>
  drule_all current_nearest_site_common_scans >> strip_tac >>
  pure_rewrite_tac[GSYM current_inherited_token_step, current_inherited_token_def] >>
  irule current_common_last_site_tokens >> simp[] >> metis_tac[]
QED
