Theory loadElimActionPlacement
Ancestors
  loadElimJoinPlacement loadElimOccurrence loadElimOccurrenceCoverage
  loadElimActualGeneration loadElimOriginHelpers loadElimPhiCapture
  loadElimDefs venomWf venomInst list rich_list

Theorem le_valid_route_blocks:
  !es. EVERY (le_occ_valid C fn) es ==>
  EVERY (\l. ?bb. MEM bb fn.fn_blocks /\ bb.bb_label = l) (le_occ_route es)
Proof
  Induct >> simp[le_occ_route_def] >> Cases_on `h` >>
  simp[le_occ_route_def, le_occ_valid_def] >>
  metis_tac[livenessTransferProofsTheory.lookup_block_mem]
QED

Theorem le_occ_prefix_route_blocks:
  le_occ_prefix C fn s0 es i s ==>
  EVERY (\l. ?bb. MEM bb fn.fn_blocks /\ bb.bb_label = l) (le_occ_route es)
Proof
  metis_tac[le_occ_prefix_valid, le_valid_route_blocks]
QED

Theorem le_route_phi_split:
  !es. MEM lbl (le_occ_route es) ==>
  ?before after bb u v.
    es = before ++ [PhiOcc bb u v] ++ after /\ bb.bb_label = lbl
Proof
  Induct >- simp[le_occ_route_def] >> Cases_on `h` >>
  simp[le_occ_route_def] >> metis_tac[APPEND, APPEND_ASSOC]
QED

Theorem le_collected_action_occurrence:
  le_occ_prefix C fn s0 es i s /\ wf_function fn /\ fn_inst_wf fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  MEM pa (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) /\
  pa.pa_load_lbl = s.vs_current_bb ==>
  ?before after bb u v.
    es = before ++ [PhiOcc bb u v] ++ after /\ bb.bb_label = pa.pa_join_lbl
Proof
  strip_tac >>
  drule_all le_occ_prefix_pred_route >> strip_tac >>
  drule_all le_occ_prefix_dfs >> strip_tac >>
  drule le_occ_prefix_route_blocks >> strip_tac >>
  drule collect_phi_actions_member >> strip_tac >>
  drule compute_phi_action_origin >> strip_tac >>
  drule le_compute_phi_action_certificate >> strip_tac >>
  `MEM pa.pa_join_lbl (le_occ_route es)` by
    (`lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
       metis_tac[venomExecPropsTheory.MEM_lookup_block, wf_function_def, fn_labels_def] >>
     `pa.pa_join_lbl = find_join_block (cfg_analyze fn) {} (LAST (le_occ_route es))` by
       metis_tac[] >>
     qpat_x_assum `pa.pa_join_lbl = find_join_block _ _ (LAST _)`
       (fn th => pure_once_rewrite_tac[th]) >>
     irule le_multivalue_point_find_join >>
     gvs[] >> qexists_tac `ctx` >>
     goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[le_route_phi_split]
QED
