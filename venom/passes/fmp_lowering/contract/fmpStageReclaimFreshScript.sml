(*
 * Freshness of a DALLOCA's output on the reclaim analysis stack: the
 * accepted reclaim analysis has a state at the entry block's start, at
 * every point of a block whose entry has one, and at the entry of every
 * successor of a block with an exit state.
 *
 * TOP-LEVEL:
 *   reclaim_fresh_entry       - the entry block starts with an empty stack
 *   reclaim_fresh_index_some  - a state at a block's entry gives one at each
 *                               point of the block
 *   reclaim_fresh_edge        - a predecessor's exit state gives the
 *                               successor an entry state
 *)
Theory fmpStageReclaimFresh
Ancestors
  fmpLowerReclaimPlan fmpReclaimDefs dfAnalyzeDefs cfgAnalysisProps
  venomWf venomWfProps venomExecProps venomInst cfgDefs list arithmetic

Theorem reclaim_fresh_entry:
  wf_function fn /\ fmp_reclaim_states infos fn = SOME states /\
  entry_block fn = SOME ebb ==>
  ?s. df_at NONE states ebb.bb_label 0 = SOME s /\ s.frs_stack = []
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  `MEM ebb fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >> gvs[entry_block_def]) >>
  drule_all fmp_reclaim_states_df_at_entry >> strip_tac >>
  metis_tac[fmp_joined_entry_some, fmp_joined_entry_empty]
QED

Theorem reclaim_fresh_index_some:
  !n. wf_function fn /\ fmp_reclaim_states infos fn = SOME states /\
  MEM pb fn.fn_blocks /\ n <= LENGTH pb.bb_instructions /\
  df_at NONE states pb.bb_label 0 = SOME s ==>
  ?t. df_at NONE states pb.bb_label n = SOME t
Proof
  Induct >> rpt strip_tac >- metis_tac[] >>
  `n <= LENGTH pb.bb_instructions /\ n < LENGTH pb.bb_instructions` by simp[] >>
  first_x_assum drule_all >> strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  drule fmp_reclaim_states_populate >> strip_tac >>
  drule_all fmp_reclaim_states_df_at_suc >> strip_tac >>
  metis_tac[fmp_transfer_some]
QED

Theorem reclaim_fresh_edge:
  wf_function fn /\ fmp_reclaim_states infos fn = SOME states /\
  MEM pb fn.fn_blocks /\ MEM sb fn.fn_blocks /\
  MEM sb.bb_label (cfg_succs_of (cfg_analyze fn) pb.bb_label) /\
  df_at NONE states pb.bb_label (LENGTH pb.bb_instructions) = SOME t ==>
  ?s ks. df_at NONE states sb.bb_label 0 = SOME s /\
    t.frs_stack = s.frs_stack ++ ks
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  drule fmp_reclaim_states_populate >> strip_tac >>
  `fmp_process_block (fmp_transfer infos fn (liveness_analyze fn) env)
    (SOME (ebb.bb_label,SOME fmp_empty_reclaim_state)) (cfg_analyze fn)
    fn.fn_blocks pb.bb_label states = states` by
    (irule fmp_reclaim_states_stable >> simp[] >> metis_tac[]) >>
  `MEM pb.bb_label (cfg_preds_of (cfg_analyze fn) sb.bb_label)` by
    metis_tac[cfg_edge_symmetry_uncond] >>
  `df_at NONE states pb.bb_label (LENGTH pb.bb_instructions) =
    FST (fmp_fold_at (fmp_transfer infos fn (liveness_analyze fn) env)
      (SOME (ebb.bb_label,SOME fmp_empty_reclaim_state)) (cfg_analyze fn)
      fn.fn_blocks states pb.bb_label)` by
    (irule fmp_reclaim_states_df_at_exit >> simp[] >> metis_tac[]) >>
  drule_all fmp_reclaim_states_df_at_entry >> strip_tac >>
  `?s. fmp_joined (SOME (ebb.bb_label,SOME fmp_empty_reclaim_state))
       (cfg_analyze fn) states sb.bb_label = SOME s` by
    metis_tac[fmp_joined_pred_some] >>
  metis_tac[fmp_joined_pred_prefix]
QED
