Theory makeSsaCurrentMergeSeed
Ancestors makeSsaCurrentTokenOwnership makeSsaCurrentGraphCut
  makeSsaCurrentTokens makeSsaCurrentAnalysis dominatorProofs
  dominatorAnalysisProps dominatorDefs cfgDefs list

Theorem current_output_inserted_origin[local]:
  !xs j t. current_output_token v l i j xs t = CurrentInserted w h ==>
    t = CurrentInserted w h
Proof
  Induct >> simp[current_output_token_def] >> rpt gen_tac >>
  Cases_on `h' = v` >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem current_scan_inserted_origin[local]:
  !insts i t. current_original_scan v l i insts t = CurrentInserted w h ==>
    t = CurrentInserted w h
Proof
  Induct >> simp[current_original_scan_def] >>
  metis_tac[current_output_inserted_origin]
QED

Theorem current_block_inserted_origin[local]:
  current_block_token fn ins v l t = CurrentInserted w h ==>
    t = CurrentInserted w h \/ l = h
Proof
  simp[current_block_token_def] >>
  Cases_on `lookup_block l fn.fn_blocks` >> simp[] >>
  strip_tac >> drule current_scan_inserted_origin >>
  Cases_on `ins v l` >> simp[]
QED

Theorem current_chain_inserted_origin:
  !path t. current_chain_token fn ins v path t = CurrentInserted w h ==>
    t = CurrentInserted w h \/ MEM h path
Proof
  Induct >> simp[current_chain_token_def] >>
  metis_tac[current_block_inserted_origin]
QED

Theorem current_exit_inserted_origin:
  current_block_token fn ins v p
    (current_inherited_token fn ins v (REVERSE ps)) = CurrentInserted w h ==>
  MEM h (p::ps)
Proof
  strip_tac >> drule current_block_inserted_origin >>
  simp[current_inherited_token_def] >> strip_tac >> simp[] >>
  drule current_chain_inserted_origin >> simp[]
QED

Theorem current_exit_inserted_dominates:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM p (fn_labels fn) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps p /\
  current_block_token fn ins v p
    (current_inherited_token fn ins v (REVERSE ps)) = CurrentInserted w h ==>
  dominates (dom_analyze (cfg_analyze fn) fn) h p
Proof
  strip_tac >> drule current_exit_inserted_origin >> simp[] >> strip_tac
  >- (gvs[] >> metis_tac[dom_self, current_all_labels_reachable]) >>
  drule_all current_actual_chain_membership >>
  metis_tac[strict_dominates_def]
QED

Theorem current_nonentry_nonself_predecessor:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM h (fn_labels fn) /\ h <> eb.bb_label ==>
  ?p. MEM p (cfg_preds_of (cfg_analyze fn) h) /\
    cfg_reachable_of (cfg_analyze fn) p /\
    ~dominates (dom_analyze (cfg_analyze fn) fn) h p /\
    (!ps. MEM p (fn_labels fn) /\
      current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps p ==>
      current_block_token fn ins v p
        (current_inherited_token fn ins v (REVERSE ps)) <> CurrentInserted v h)
Proof
  strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) h` by
    metis_tac[current_all_labels_reachable] >>
  drule_all exists_pred_not_dominated >> strip_tac >>
  goal_assum $ drule_at Any >> simp[] >>
  metis_tac[current_exit_inserted_dominates]
QED
