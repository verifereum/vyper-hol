Theory makeSsaCurrentPlacementCut
Ancestors
  makeSsaCurrentPlacement makeSsaCurrentPhiLocality makeSsaCurrentAnalysis
  makeSsaCurrentLastSite makeSsaCurrentFrontier cfgAnalysisProps
  makeSsaCurrentCutTokens makeSsaDefs venomInst list alist

Definition current_actual_inserted_def:
  current_actual_inserted fn v l <=>
    ?roots. ALOOKUP (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))))
      v = SOME roots /\
      current_pruned_reach (current_frontier_map fn)
        (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
          (liveness_analyze fn) fn) v roots l
End

Definition current_exact_prefix_def:
  current_exact_prefix df pm li defs old new <=>
    ?pre. new = old with bb_instructions := pre ++ old.bb_instructions /\
      EVERY (\i. ?id v. MEM v (MAP FST defs) /\
        i = build_phi_inst_supply id v
          (case ALOOKUP pm old.bb_label of SOME ps => ps | NONE => [])) pre /\
      (!v. (?i. MEM i pre /\ MEM v i.inst_outputs) <=>
        ?roots. ALOOKUP defs v = SOME roots /\
          current_pruned_reach df li v roots old.bb_label)
End

Theorem current_exact_prefix_nil:
  current_exact_prefix df pm li [] b b
Proof
  simp[current_exact_prefix_def] >> qexists_tac `[]` >> simp[]
QED

Theorem current_exact_prefix_cons:
  ~MEM v (MAP FST defs) /\
  current_var_prefix pm li v [] a b /\
  (a <> b <=> current_pruned_reach df li v roots a.bb_label) /\
  current_exact_prefix df pm li defs b c ==>
  current_exact_prefix df pm li ((v,roots)::defs) a c
Proof
  simp[current_var_prefix_def, current_exact_prefix_def] >>
  rpt strip_tac >> gvs[] >>
  qexists_tac `pre' ++ pre` >>
  simp[EVERY_APPEND] >>
  conj_tac >- (gvs[EVERY_MEM] >> metis_tac[]) >>
  qx_gen_tac `w` >>
  `!i. MEM i pre ==> i.inst_outputs = [v]` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[build_phi_inst_supply_def]) >>
  `(?i. MEM i pre /\ MEM w i.inst_outputs) <=> w = v /\ pre <> []` by
    (Cases_on `pre` >> gvs[] >> metis_tac[MEM]) >>
  `a <> a with bb_instructions := pre ++ a.bb_instructions <=> pre <> []` by
    (simp[basic_block_component_equality] >>
     metis_tac[LENGTH_APPEND, LENGTH_NIL, DECIDE ``!n m:num. n + m = m <=> n = 0``, APPEND]) >>
  simp[GSYM LEFT_EXISTS_AND_THM, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  `ALOOKUP defs v = NONE` by
    (Cases_on `ALOOKUP defs v` >> simp[] >>
     imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP] >> metis_tac[pairTheory.FST]) >>
  Cases_on `w = v` >> gvs[]
QED

Theorem current_defs_placement_exact_prefix:
  !defs bbs bbs'. ALL_DISTINCT (MAP FST defs) /\
    current_defs_placement df pm li defs bbs bbs' ==>
    LIST_REL (current_exact_prefix df pm li defs) bbs bbs'
Proof
  Induct >- simp[current_defs_placement_def, LIST_REL_EL_EQN,
                 current_exact_prefix_nil] >>
  Cases_on `h` >> simp[current_defs_placement_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  irule current_exact_prefix_cons >> goal_assum $ drule_at Any >>
  metis_tac[]
QED

Theorem current_add_phi_nodes_exact_prefix:
  add_phi_nodes_supply s df pm li bbs (compute_defs ordered) = (bbs',s') ==>
  LIST_REL (current_exact_prefix df pm li (compute_defs ordered)) bbs bbs'
Proof
  strip_tac >> irule current_defs_placement_exact_prefix >>
  simp[compute_defs_all_distinct] >>
  metis_tac[current_add_phi_nodes_placement]
QED

Theorem current_actual_insertion_prefix:
  add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
    (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) fn.fn_blocks
    (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))))
    = (bbs',s') ==>
  LIST_REL (\old new. ?pre.
    new = old with bb_instructions := pre ++ old.bb_instructions /\
    EVERY (\i. ?id v. i = build_phi_inst_supply id v
      (case ALOOKUP (current_pred_map fn) old.bb_label of
        SOME ps => ps | NONE => [])) pre /\
    (!v. current_actual_inserted fn v old.bb_label <=>
      ?i. MEM i pre /\ MEM v i.inst_outputs)) fn.fn_blocks bbs'
Proof
  strip_tac >> drule current_add_phi_nodes_exact_prefix >>
  simp[LIST_REL_EL_EQN, current_exact_prefix_def, current_actual_inserted_def] >>
  rpt strip_tac >> `n < LENGTH fn.fn_blocks` by metis_tac[] >>
  first_x_assum drule >> strip_tac >>
  goal_assum $ drule_at Any >> simp[] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem current_actual_inserted_single_local:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME entry /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 /\
  blocks_have_leading_phi fn.fn_blocks /\ current_actual_inserted fn v y ==>
  y = db.bb_label
Proof
  simp[current_actual_inserted_def] >> strip_tac >> gvs[] >>
  drule_all current_compute_defs_pruned_reach_local >> simp[]
QED

Theorem current_actual_inserted_step:
  current_actual_inserted fn v d /\
  current_frontier_edge (current_frontier_map fn) d y /\
  current_placement_live
    (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) v y ==>
  current_actual_inserted fn v y
Proof
  simp[current_actual_inserted_def] >>
  metis_tac[current_pruned_reach_rules]
QED

Theorem current_actual_inserted_seed:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME entry /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs /\
  current_frontier_edge (current_frontier_map fn) db.bb_label y /\
  current_placement_live
    (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) v y ==>
  current_actual_inserted fn v y
Proof
  strip_tac >>
  `MEM v (block_assignments db)` by
    (simp[block_assignments_def, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  drule_all current_compute_defs_complete >> strip_tac >>
  simp[current_actual_inserted_def] >>
  metis_tac[current_pruned_reach_rules]
QED

Theorem current_frontier_edge_target_label:
  wf_function fn /\ current_frontier_edge (current_frontier_map fn) d y ==>
  MEM y (fn_labels fn)
Proof
  simp[current_frontier_edge_def] >> strip_tac >>
  `MEM d (fn_labels fn)` by
    (imp_res_tac ALOOKUP_MEM >>
     gvs[current_frontier_map_def, current_query_map_def, MEM_MAP] >> metis_tac[]) >>
  drule_all current_frontier_target_count >> strip_tac >>
  metis_tac[dfAnalyzeProofsTheory.cfg_dfs_post_subset_fn_labels]
QED

Theorem current_pruned_reach_target_label:
  wf_function fn ==> !y. current_pruned_reach (current_frontier_map fn) li v roots y ==>
  MEM y (fn_labels fn)
Proof
  strip_tac >> ho_match_mp_tac current_pruned_reach_ind >>
  metis_tac[current_frontier_edge_target_label]
QED

Theorem current_actual_inserted_label:
  wf_function fn /\ current_actual_inserted fn v y ==> MEM y (fn_labels fn)
Proof
  simp[current_actual_inserted_def] >>
  metis_tac[current_pruned_reach_target_label]
QED

Theorem current_actual_inserted_closed:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME entry /\
  current_changing_site fn (current_actual_inserted fn) v d /\
  MEM y (frontier_of (dom_analyze (cfg_analyze fn) fn) d) /\
  current_placement_live
    (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) v y ==>
  current_actual_inserted fn v y
Proof
  strip_tac >>
  `MEM d (fn_labels fn)` by
    (gvs[current_changing_site_def]
     >- metis_tac[current_actual_inserted_label] >>
     simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `current_frontier_edge (current_frontier_map fn) d y` by
    simp[current_frontier_edge_def, ALOOKUP_current_frontier_map] >>
  gvs[current_changing_site_def] >>
  metis_tac[current_actual_inserted_seed, current_actual_inserted_step]
QED
