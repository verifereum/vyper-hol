Theory fmpStepAnalysis
Ancestors
  fmpStepStack fmpReclaimDefs dfAnalyzeDefs worklistDefs venomExecProps
  finite_map list pair

Definition fmp_map_valid_def:
  fmp_map_valid P m <=> !k v. FLOOKUP m k = SOME v ==> fmp_stack_valid P v
End

Theorem fmp_map_valid_empty[simp]:
  fmp_map_valid P FEMPTY
Proof
  simp[fmp_map_valid_def]
QED

Theorem fmp_map_valid_update:
  fmp_map_valid P m /\ fmp_stack_valid P v ==>
  fmp_map_valid P (m |+ (k,v))
Proof
  simp[fmp_map_valid_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `k = k'` >> gvs[] >> metis_tac[]
QED

Theorem fmp_map_valid_union:
  fmp_map_valid P a /\ fmp_map_valid P b ==>
  fmp_map_valid P (FUNION a b)
Proof
  simp[fmp_map_valid_def, FLOOKUP_FUNION] >> rpt strip_tac >>
  Cases_on `FLOOKUP a k` >> gvs[] >> metis_tac[]
QED

Theorem fmp_fold_forward_valid:
  !insts idx acc m.
  fmp_stack_valid P acc /\ fmp_map_valid P m /\
  (!p inst s. MEM inst insts /\ fmp_stack_valid P s ==>
    fmp_stack_valid P (transfer p inst s)) ==>
  fmp_stack_valid P (FST (fmp_fold_forward transfer lbl insts idx acc m)) /\
  fmp_map_valid P (SND (fmp_fold_forward transfer lbl insts idx acc m))
Proof
  Induct >> simp[fmp_fold_forward_def, fmp_map_valid_update] >>
  rpt strip_tac >> first_x_assum irule >>
  simp[fmp_map_valid_update] >> metis_tac[]
QED

Definition fmp_df_valid_def:
  fmp_df_valid P st <=>
    fmp_map_valid P st.ds_boundary /\ fmp_map_valid P st.ds_inst
End

Theorem fmp_boundary_valid:
  fmp_df_valid P st ==> fmp_stack_valid P (df_boundary NONE st lbl)
Proof
  simp[fmp_df_valid_def, df_boundary_def, fmp_map_valid_def] >>
  rpt strip_tac >> Cases_on `FLOOKUP st.ds_boundary lbl` >>
  simp[fmp_stack_valid_def] >> metis_tac[]
QED

Theorem fmp_join_fold_valid:
  !xs acc. EVERY (fmp_stack_valid P) xs /\ fmp_stack_valid P acc ==>
    fmp_stack_valid P (FOLDL fmp_reclaim_option_join acc xs)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[fmp_stack_valid_join]
QED

Theorem fmp_joined_valid:
  fmp_df_valid P st /\
  (!l v. entry = SOME (l,v) ==> fmp_stack_valid P v) ==>
  fmp_stack_valid P (fmp_joined entry cfg st lbl)
Proof
  strip_tac >> simp[fmp_joined_def, df_joined_val_def] >>
  qmatch_goalsub_abbrev_tac `case vals of [] => NONE | _ => _` >>
  `EVERY (fmp_stack_valid P) vals` by
    (simp[Abbr `vals`, EVERY_MAP, EVERY_MEM, fmp_boundary_valid]) >>
  `fmp_stack_valid P (case vals of [] => NONE | _ =>
      FOLDL fmp_reclaim_option_join NONE vals)` by
    (Cases_on `vals` >- simp[fmp_stack_valid_def] >>
     gvs[] >> irule fmp_join_fold_valid >>
     simp[fmp_stack_valid_join, fmp_stack_valid_def]) >>
  Cases_on `entry` >> simp[] >> PairCases_on `x` >> simp[] >>
  IF_CASES_TAC >> simp[] >> irule fmp_stack_valid_join >> metis_tac[]
QED

Theorem fmp_fold_at_valid:
  fmp_df_valid P st /\
  (!l v. entry = SOME (l,v) ==> fmp_stack_valid P v) /\
  (!p inst s. MEM inst (fn_insts_blocks bbs) /\ fmp_stack_valid P s ==>
    fmp_stack_valid P (transfer p inst s)) ==>
  fmp_stack_valid P (FST (fmp_fold_at transfer entry cfg bbs st lbl)) /\
  fmp_map_valid P (SND (fmp_fold_at transfer entry cfg bbs st lbl))
Proof
  strip_tac >> simp[fmp_fold_at_def] >> irule fmp_fold_forward_valid >>
  simp[fmp_joined_valid] >> Cases_on `lookup_block lbl bbs` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  `MEM x bbs` by metis_tac[lookup_block_MEM] >>
  qpat_x_assum `MEM x bbs` mp_tac >>
  qid_spec_tac `bbs` >> Induct >> simp[venomInstTheory.fn_insts_blocks_def] >>
  metis_tac[]
QED

Theorem fmp_process_block_valid:
  fmp_df_valid P st /\
  (!l v. entry = SOME (l,v) ==> fmp_stack_valid P v) /\
  (!p inst s. MEM inst (fn_insts_blocks bbs) /\ fmp_stack_valid P s ==>
    fmp_stack_valid P (transfer p inst s)) ==>
  fmp_df_valid P (fmp_process_block transfer entry cfg bbs lbl st)
Proof
  strip_tac >> drule_all fmp_fold_at_valid >> strip_tac >>
  simp[fmp_process_block_def] >> IF_CASES_TAC >> simp[] >>
  fs[fmp_df_valid_def] >> irule fmp_map_valid_update >>
  simp[] >> irule fmp_stack_valid_join >>
  metis_tac[fmp_boundary_valid, fmp_df_valid_def]
QED

Theorem fmp_populate_valid:
  fmp_df_valid P st /\
  (!l v. entry = SOME (l,v) ==> fmp_stack_valid P v) /\
  (!p inst s. MEM inst (fn_insts_blocks bbs) /\ fmp_stack_valid P s ==>
    fmp_stack_valid P (transfer p inst s)) ==>
  fmp_df_valid P (fmp_populate transfer entry cfg bbs st)
Proof
  strip_tac >> drule_all fmp_fold_at_valid >> strip_tac >>
  simp[fmp_populate_def] >>
  `!ls acc. fmp_df_valid P acc ==>
    fmp_df_valid P (FOLDL (\acc lbl. acc with ds_inst := FUNION
      (SND (fmp_fold_at transfer entry cfg bbs st lbl)) acc.ds_inst) acc ls)`
    suffices_by metis_tac[] >>
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  fs[fmp_df_valid_def] >> irule fmp_map_valid_union >> simp[]
QED

Theorem fmp_worklist_valid:
  (!lbl st. Q st ==> Q (process lbl st)) ==>
  !fuel wl st. Q st ==> Q (SND (wl_iterate_fuel fuel changed process deps wl st))
Proof
  strip_tac >> Induct >> simp[wl_iterate_fuel_def] >>
  Cases_on `wl` >> simp[wl_iterate_fuel_def, wl_step_def] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem fmp_init_valid:
  fmp_df_valid P (init_df_state NONE lbls)
Proof
  simp[init_df_state_def, fmp_df_valid_def] >>
  `!ls (m : string |-> fmp_reclaim_state option). fmp_map_valid P m ==>
    fmp_map_valid P (FOLDL (\m lbl. m |+ (lbl,NONE)) m ls)`
    suffices_by metis_tac[fmp_map_valid_empty] >>
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[fmp_map_valid_update, fmp_stack_valid_def]
QED

Theorem fmp_df_boundary_update_valid:
  fmp_df_valid P st /\ fmp_stack_valid P v ==>
  fmp_df_valid P (st with ds_boundary := st.ds_boundary |+ (lbl,v))
Proof
  simp[fmp_df_valid_def, fmp_map_valid_update]
QED

Theorem fmp_analyze_fuel_valid:
  fmp_reclaim_analyze_fuel fuel infos fn live env = SOME states ==>
  fmp_df_valid (fmp_dalloca_output fn) states
Proof
  simp[fmp_reclaim_analyze_fuel_def] >>
  Cases_on `entry_block fn` >> simp[] >> strip_tac >> gvs[] >>
  irule fmp_populate_valid >>
  simp[fmp_stack_valid_def, fmp_empty_reclaim_state_def] >>
  reverse conj_tac
  >- (irule fmp_worklist_valid >> reverse conj_tac
      >- (rpt strip_tac >> irule fmp_process_block_valid >>
          simp[fmp_stack_valid_def, fmp_empty_reclaim_state_def] >>
          metis_tac[fmp_transfer_dalloca_output, venomInstTheory.fn_insts_def]) >>
      irule fmp_df_boundary_update_valid >>
      simp[fmp_init_valid, fmp_stack_valid_def, fmp_empty_reclaim_state_def]) >>
  metis_tac[fmp_transfer_dalloca_output, venomInstTheory.fn_insts_def]
QED

Theorem fmp_reclaim_states_valid:
  fmp_reclaim_states infos fn = SOME states ==>
  fmp_df_valid (fmp_dalloca_output fn) states
Proof
  simp[fmp_reclaim_states_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> metis_tac[fmp_analyze_fuel_valid]
QED

Theorem fmp_reclaim_states_stack:
  fmp_reclaim_states infos fn = SOME states /\
  df_at NONE states lbl idx = SOME st ==>
  EVERY (fmp_dalloca_output fn) st.frs_stack
Proof
  strip_tac >> drule fmp_reclaim_states_valid >>
  simp[fmp_df_valid_def, fmp_map_valid_def, df_at_def] >>
  Cases_on `FLOOKUP states.ds_inst (lbl,idx)` >> gvs[df_at_def] >>
  metis_tac[fmp_stack_valid_def]
QED
