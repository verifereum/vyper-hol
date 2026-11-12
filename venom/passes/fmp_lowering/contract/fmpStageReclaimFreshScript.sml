Theory fmpStageReclaimFresh
Ancestors
  fmpLowerReclaimPlan fmpReclaimDefs dfAnalyzeDefs cfgAnalysisProps
  venomWf venomWfProps venomExecProps venomInst cfgDefs list arithmetic

(* These join facts are local interfaces of fmpStepReclaimDefined and are
   restated here because that theory deliberately does not export them. *)
Theorem fmp_join_fold_none[local]:
  !vs acc. FOLDL fmp_reclaim_option_join acc vs = NONE ==>
    acc = NONE /\ EVERY IS_NONE vs
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> Cases_on `acc` >> Cases_on `h` >>
  simp[fmp_reclaim_option_join_def]
QED

Theorem fmp_option_join_some[local]:
  y <> NONE ==> ?st. fmp_reclaim_option_join x y = SOME st
Proof
  Cases_on `x` >> Cases_on `y` >> simp[fmp_reclaim_option_join_def]
QED

Theorem fmp_case_foldl[local]:
  (case xs of [] => NONE | v2::v3 => FOLDL fmp_reclaim_option_join NONE xs) =
  FOLDL fmp_reclaim_option_join NONE xs
Proof
  Cases_on `xs` >> simp[]
QED

Theorem fmp_joined_some[local]:
  FOLDL fmp_reclaim_option_join NONE
    (MAP (\nbr. df_boundary NONE states nbr) (cfg_preds_of cfg lbl)) <> NONE ==>
  ?st. fmp_joined entry cfg states lbl = SOME st
Proof
  strip_tac >> Cases_on `entry` >>
  simp[fmp_joined_def, df_joined_val_def, fmp_case_foldl]
  >- metis_tac[optionTheory.option_CASES] >>
  PairCases_on `x` >> rw[] >>
  metis_tac[fmp_option_join_some, optionTheory.option_CASES]
QED

Theorem fmp_joined_entry_some[local]:
  ?st. fmp_joined (SOME (lbl,SOME fmp_empty_reclaim_state)) cfg states lbl =
       SOME st
Proof
  simp[fmp_joined_def, df_joined_val_def, fmp_case_foldl] >>
  qmatch_goalsub_abbrev_tac `fmp_reclaim_option_join _ b` >>
  Cases_on `b` >> simp[fmp_reclaim_option_join_def]
QED

Theorem fmp_joined_pred_some[local]:
  fmp_process_block transfer entry cfg bbs pred states = states /\
  MEM pred (cfg_preds_of cfg succ) /\
  FST (fmp_fold_at transfer entry cfg bbs states pred) = SOME exit_st ==>
  ?entry_st. fmp_joined entry cfg states succ = SOME entry_st
Proof
  strip_tac >> drule_all fmp_process_block_stable >> strip_tac >>
  irule fmp_joined_some >> strip_tac >>
  drule fmp_join_fold_none >>
  simp[EXISTS_MEM, MEM_MAP, PULL_EXISTS] >>
  qexists `pred` >> simp[]
QED

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
