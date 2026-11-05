Theory o1MakeSsaFrontier
Ancestors
  unitShapeDefs finite_map dominatorDefs cfgDefs cfgHelpers list
  makeSsaCurrentDefs venomInst venomWf

(* Weak frontier support: no definite assignment or all_reachable premise.
   Adapted from the proved makeSsaCurrentFrontier reference theory. *)
Theorem walk_to_idom_target_support:
  !fuel idom target runner df n y.
    MEM y (fmap_lookup_list (walk_to_idom idom target runner df fuel) n) ==>
    MEM y (fmap_lookup_list df n) \/ y = target
Proof
  Induct >> simp[walk_to_idom_def] >> rpt gen_tac >>
  Cases_on `FLOOKUP idom target` >> simp[] >>
  Cases_on `runner = x` >> simp[] >>
  Cases_on `FLOOKUP idom runner` >> simp[]
  >- (gvs[fmap_lookup_list_def, FLOOKUP_UPDATE] >>
      Cases_on `n = runner` >> gvs[mem_set_insert] >> metis_tac[]) >>
  strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
  gvs[fmap_lookup_list_def, FLOOKUP_UPDATE] >>
  Cases_on `n = runner` >> gvs[mem_set_insert] >> metis_tac[]
QED

Theorem walk_to_idom_fold_support:
  !preds df idom target fuel n y.
    MEM y (fmap_lookup_list
      (FOLDL (\acc pred. walk_to_idom idom target pred acc fuel) df preds) n) ==>
    MEM y (fmap_lookup_list df n) \/ y = target
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum drule >>
  strip_tac >> gvs[] >> metis_tac[walk_to_idom_target_support]
QED

Theorem compute_df_acc_support:
  !order df cfg idom fuel n y.
    MEM y (fmap_lookup_list
      (FOLDL (\acc lbl.
        if LENGTH (cfg_preds_of cfg lbl) <= 1 then acc
        else FOLDL (\a pred. walk_to_idom idom lbl pred a fuel)
          acc (cfg_preds_of cfg lbl)) df order) n) ==>
    MEM y (fmap_lookup_list df n) \/
    (MEM y order /\ LENGTH (cfg_preds_of cfg y) > 1)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `LENGTH (cfg_preds_of cfg h) <= 1` >> simp[] >>
  strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
  drule walk_to_idom_fold_support >> strip_tac >> gvs[]
QED

Theorem compute_df_target_support:
  MEM y (fmap_lookup_list (compute_df cfg idom order fuel) n) ==>
  MEM y order /\ LENGTH (cfg_preds_of cfg y) > 1
Proof
  simp[compute_df_def] >> strip_tac >>
  drule compute_df_acc_support >> simp[fmap_lookup_list_fempty]
QED

Theorem current_frontier_target_count:
  MEM n (fn_labels fn) /\
  ALOOKUP (current_frontier_map fn) n = SOME fs /\ MEM y fs ==>
  MEM y (cfg_analyze fn).cfg_dfs_post /\
  LENGTH (cfg_preds_of (cfg_analyze fn) y) > 1
Proof
  strip_tac >>
  `fs = frontier_of (dom_analyze (cfg_analyze fn) fn) n` by
    metis_tac[ALOOKUP_current_frontier_map, optionTheory.THE_DEF] >>
  qpat_x_assum `MEM y fs` mp_tac >>
  simp[Once frontier_of_def, dom_analyze_def] >>
  metis_tac[compute_df_target_support]
QED

Theorem current_cfg_edge_preds:
  wf_function fn ==>
  (MEM p (cfg_preds_of (cfg_analyze fn) y) <=> fn_cfg_edge fn p y)
Proof
  strip_tac >> simp[cfg_analyze_preds, mem_build_preds, fn_cfg_edge_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  eq_tac >> strip_tac >> qexists `bb` >>
  drule_all cfg_succs_of_build_succs >> strip_tac >> gvs[]
QED

Theorem current_entry_preds_empty:
  wf_function fn /\ first_block_no_preds fn /\ fn_entry_label fn = SOME y ==>
  cfg_preds_of (cfg_analyze fn) y = []
Proof
  strip_tac >>
  `!p. ~MEM p (cfg_preds_of (cfg_analyze fn) y)` suffices_by
    (Cases_on `cfg_preds_of (cfg_analyze fn) y` >> simp[] >> metis_tac[MEM]) >>
  simp[current_cfg_edge_preds, fn_cfg_edge_def] >>
  gvs[first_block_no_preds_def, EVERY_MEM, fn_entry_label_def,
      entry_block_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem current_frontier_not_entry:
  wf_function fn /\ first_block_no_preds fn /\
  MEM n (fn_labels fn) /\
  ALOOKUP (current_frontier_map fn) n = SOME fs /\ MEM y fs ==>
  fn_entry_label fn <> SOME y
Proof
  strip_tac >> drule_all current_frontier_target_count >> strip_tac >>
  strip_tac >> drule_all current_entry_preds_empty >> strip_tac >> gvs[]
QED

Theorem phi_pairs_build_phi_inst_supply:
  !preds. phi_pairs (build_phi_inst_supply id var preds).inst_operands =
    MAP (\l. (l,var)) preds
Proof
  Induct >> gvs[build_phi_inst_supply_def, phi_pairs_def]
QED

Theorem build_phi_inst_supply_shape:
  !preds. 2 <= LENGTH preds /\ ALL_DISTINCT preds ==>
  inst_shape_ok (build_phi_inst_supply id var preds)
Proof
  simp[inst_shape_ok_def, phi_pairs_build_phi_inst_supply,
       build_phi_inst_supply_def, label_positions_ok_def, is_read0_opcode_def,
       MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem ordered_set_insert_distinct:
  ALL_DISTINCT xs ==> ALL_DISTINCT (ordered_set_insert x xs)
Proof
  simp[ordered_set_insert_def] >> IF_CASES_TAC >> simp[ALL_DISTINCT_APPEND]
QED

Theorem preds_foldr_distinct[local]:
  !targets m source.
  (!k. ALL_DISTINCT (fmap_lookup_list m k)) ==>
  !k. ALL_DISTINCT (fmap_lookup_list
    (FOLDR (\succ m2. m2 |+ (succ,
      ordered_set_insert source (fmap_lookup_list m2 succ))) m targets) k)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  simp[fmap_lookup_list_update] >> IF_CASES_TAC >>
  simp[ordered_set_insert_distinct]
QED

Theorem preds_foldl_distinct[local]:
  !bbs m succs.
  (!k. ALL_DISTINCT (fmap_lookup_list m k)) ==>
  !k. ALL_DISTINCT (fmap_lookup_list
    (FOLDL (\m bb.
      FOLDR (\succ m2. m2 |+ (succ,
        ordered_set_insert bb.bb_label (fmap_lookup_list m2 succ)))
        m (fmap_lookup_list succs bb.bb_label)) m bbs) k)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  irule preds_foldr_distinct >> simp[]
QED

Theorem init_preds_distinct:
  !bbs. !k. ALL_DISTINCT (fmap_lookup_list (init_preds bbs) k)
Proof
  qsuff_tac `!bbs m. (!k. ALL_DISTINCT (fmap_lookup_list m k)) ==>
    !k. ALL_DISTINCT (fmap_lookup_list
      (FOLDL (\m bb. m |+ (bb.bb_label, [])) m bbs) k)`
  >- (strip_tac >> simp[init_preds_def] >> first_x_assum irule >>
      simp[fmap_lookup_list_fempty]) >>
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[fmap_lookup_list_update] >> gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem cfg_preds_distinct:
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) lbl)
Proof
  simp[cfg_analyze_preds, build_preds_def] >>
  irule preds_foldl_distinct >> simp[init_preds_distinct]
QED
