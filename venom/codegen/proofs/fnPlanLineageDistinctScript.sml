Theory fnPlanLineageDistinct
Ancestors
  list finite_map dfHelperDefs dfAnalyzeDefs
  fnPlanLineagePhiClasses fnPlanLineagePhiMaps livenessDefs
  livenessTerminationProofs venomExecProps
  livenessInvariantProofs livenessRankProofs worklistDefs

Theorem list_union_all_distinct:
  ALL_DISTINCT xs /\ ALL_DISTINCT ys ==>
  ALL_DISTINCT (list_union xs ys)
Proof
  simp[list_union_def, ALL_DISTINCT_APPEND, FILTER_ALL_DISTINCT,
       MEM_FILTER] >> metis_tac[]
QED

Theorem foldl_list_union_all_distinct:
  !xss acc. ALL_DISTINCT acc /\ EVERY ALL_DISTINCT xss ==>
    ALL_DISTINCT (FOLDL list_union acc xss)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[list_union_all_distinct]
QED

Definition lineage_map_values_def:
  lineage_map_values P m <=>
    !k v. FLOOKUP m k = SOME v ==> P v
End

Theorem lineage_map_values_empty[simp]:
  lineage_map_values P FEMPTY
Proof
  simp[lineage_map_values_def]
QED

Theorem lineage_map_values_update:
  lineage_map_values P m /\ P v ==>
  lineage_map_values P (m |+ (k,v))
Proof
  rw[lineage_map_values_def, FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem lineage_map_values_union:
  lineage_map_values P m /\ lineage_map_values P n ==>
  lineage_map_values P (FUNION m n)
Proof
  rw[lineage_map_values_def, FLOOKUP_FUNION] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem df_fold_backward_map_values:
  !insts idx acc m entry m'.
    (!inst v. P v ==> P (transfer inst v)) /\
    P acc /\ lineage_map_values P m /\
    df_fold_backward transfer lbl insts idx acc m = (entry,m') ==>
    P entry /\ lineage_map_values P m'
Proof
  Induct >> rpt gen_tac
  >- (simp[df_fold_backward_def] >> rpt strip_tac >>
      gvs[] >> irule lineage_map_values_update >> simp[]) >>
  strip_tac >>
  Cases_on `df_fold_backward transfer lbl insts (idx + 1) acc m` >>
  gvs[df_fold_backward_def] >>
  qpat_x_assum `!idx' acc' m'' entry' m3. _` drule_all >> strip_tac >>
  `P (transfer h q)` by metis_tac[] >>
  simp[] >> irule lineage_map_values_update >> simp[]
QED

Theorem df_fold_block_backward_map_values:
  (!inst v. P v ==> P (transfer inst v)) /\ P acc /\
  df_fold_block Backward transfer lbl insts acc = (entry,m) ==>
  P entry /\ lineage_map_values P m
Proof
  simp[df_fold_block_def] >> strip_tac >>
  irule df_fold_backward_map_values >>
  simp[] >>
  goal_assum (drule_at (Pat `df_fold_backward _ _ _ _ _ _ = _`)) >> simp[]
QED

Definition lineage_live_distinct_def:
  lineage_live_distinct st <=> lineage_map_values ALL_DISTINCT st.ds_inst
End

Theorem lineage_live_distinct_init[simp]:
  lineage_live_distinct (init_df_state [] labels)
Proof
  simp[lineage_live_distinct_def, init_df_state_def]
QED

Theorem lineage_live_distinct_at:
  lineage_live_distinct st ==> ALL_DISTINCT (df_at [] st lbl i)
Proof
  rw[lineage_live_distinct_def, lineage_map_values_def, df_at_def] >>
  Cases_on `FLOOKUP st.ds_inst (lbl,i)` >> simp[] >> metis_tac[]
QED

Theorem lineage_edge_transfer_distinct:
  (!bb. MEM bb bbs ==> phi_uses_disjoint (collect_phis bb.bb_instructions)) /\
  ALL_DISTINCT live ==>
  ALL_DISTINCT (liveness_edge_transfer bbs succ pred live)
Proof
  strip_tac >> simp[liveness_edge_transfer_def] >>
  Cases_on `lookup_block succ bbs` >> simp[] >>
  irule input_vars_from_distinct >> simp[] >>
  metis_tac[lookup_block_MEM]
QED

Theorem lineage_liveness_block_distinct:
  (!bb. MEM bb bbs ==> phi_uses_disjoint (collect_phis bb.bb_instructions)) /\
  lineage_live_distinct st ==>
  lineage_live_distinct (liveness_block bbs cfg lbl st)
Proof
  strip_tac >>
  `ALL_DISTINCT (FOLDL list_union []
    (MAP (\s. liveness_edge_transfer bbs s lbl (df_at [] st s 0))
      (cfg_succs_of cfg lbl)))` by
    (irule foldl_list_union_all_distinct >> simp[EVERY_MAP, EVERY_MEM] >>
     rpt strip_tac >> irule lineage_edge_transfer_distinct >>
     simp[lineage_live_distinct_at]) >>
  simp[liveness_block_def] >> pairarg_tac >>
  `!inst v. ALL_DISTINCT v ==>
      ALL_DISTINCT (liveness_transfer bbs inst v)` by
    simp[liveness_transfer_def, live_update_ALL_DISTINCT] >>
  `ALL_DISTINCT entry /\ lineage_map_values ALL_DISTINCT inst_map` by
    metis_tac[df_fold_block_backward_map_values] >>
  gvs[lineage_live_distinct_def] >>
  irule lineage_map_values_union >> gvs[lineage_live_distinct_def]
QED

Theorem lineage_live_distinct_step:
  (!bb. MEM bb bbs ==> phi_uses_disjoint (collect_phis bb.bb_instructions)) /\
  lineage_live_distinct (SND p) ==>
  lineage_live_distinct (SND
    (wl_step (liveness_changed bbs) (liveness_block bbs cfg)
       (cfg_preds_of cfg) p))
Proof
  PairCases_on `p` >> simp[] >> strip_tac >>
  Cases_on `p0` >- simp[wl_step_def] >> simp[wl_step_def] >>
  Cases_on `liveness_changed bbs h p1 (liveness_block bbs cfg h p1)` >>
  simp[] >> irule lineage_liveness_block_distinct >> simp[]
QED

Theorem lineage_live_distinct_recompute:
  (!bb. MEM bb fn.fn_blocks ==>
    phi_uses_disjoint (collect_phis bb.bb_instructions)) ==>
  lineage_live_distinct (liveness_recompute fn)
Proof
  strip_tac >> simp[liveness_recompute_def] >>
  irule (lv_iteration_rule |>
    Q.INST [`Q` |-> `\p. lineage_live_distinct (SND p)`] |>
    SRULE [] |> cj 3) >>
  simp[lv_inv_init, lv_labels_initial] >> rpt strip_tac >>
  irule lineage_live_distinct_step >> simp[]
QED

Theorem ready_liveness_analyze_distinct:
  codegen_ready_fn fn ==> lineage_live_distinct (liveness_analyze fn)
Proof
  strip_tac >> simp[liveness_analyze_def] >>
  irule lineage_live_distinct_recompute >>
  metis_tac[ready_block_phi_uses_disjoint]
QED

Theorem ready_live_vars_at_distinct:
  codegen_ready_fn fn ==>
  ALL_DISTINCT (live_vars_at (liveness_analyze fn) lbl i)
Proof
  strip_tac >> simp[live_vars_at_def] >>
  irule lineage_live_distinct_at >> simp[ready_liveness_analyze_distinct]
QED
