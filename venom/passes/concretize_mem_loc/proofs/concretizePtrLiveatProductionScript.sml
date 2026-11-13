Theory concretizePtrLiveatProduction
Ancestors
  concretizePtrLiveatDemand concretizeAnalysisLivenessClosure concretizeAnalysisLivenessTransfer
  concretizeMemLocDefs singleWriterScan finite_map list pred_set relation indexedLists

Theorem ptr_liveat_descriptor_budget[local]:
  CARD (IMAGE sw_out (set (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
    (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)))) + 2 <= concretize_memloc_fuel fn
Proof
  `CARD (IMAGE sw_out (set (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
    (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)))) <= LENGTH fn.fn_blocks` by
    (irule ml_scan_blocks_card_bound >> simp[ml_boundary_desc_out]) >>
  simp[concretize_memloc_fuel_def] >> decide_tac
QED

Theorem ptr_liveat_production_records:
  EVERY (\b. b.bb_instructions <> []) fn.fn_blocks /\
  (!nm. OL alloc_to (mems nm)) /\
  MEM bb (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post) /\
  i < LENGTH bb.bb_instructions /\
  ml_liveat_record_bit a bp mems sizes bb.bb_label (bb.bb_label,i)
    (MAPi (\j inst. (j,inst)) bb.bb_instructions)
    (?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\
      T IN sw_rounds (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
        (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) n lbl) F ==>
  MEM a (ml_lookup
    (FST (ml_iterate_fuel (concretize_memloc_fuel fn) bp mems sizes pallocas cfg fn FEMPTY FEMPTY))
    (bb.bb_label,i))
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `sw_rounds ds n` >>
  `sw_consistent ds` by
    (simp[Abbr `ds`] >> irule ml_scan_blocks_consistent >> simp[ml_boundary_desc_out]) >>
  `sw_le (sw_rounds ds n) (sw_rounds ds (CARD (IMAGE sw_out (set ds))))` by
    (irule sw_rounds_bound >> simp[]) >>
  `ml_liveat_record_bit a bp mems sizes bb.bb_label (bb.bb_label,i)
    (MAPi (\j inst. (j,inst)) bb.bb_instructions)
    (?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\
      T IN sw_rounds ds (CARD (IMAGE sw_out (set ds))) lbl) F` by
    (`!lbl. T IN sw_rounds ds n lbl ==>
        T IN sw_rounds ds (CARD (IMAGE sw_out (set ds))) lbl` by
      metis_tac[sw_le_def, SUBSET_DEF] >>
     qpat_x_assum `ml_liveat_record_bit _ _ _ _ _ _ _ _ _` mp_tac >>
     once_rewrite_tac[ml_liveat_record_bit_affine] >> metis_tac[]) >>
  irule ptr_liveat_fuel_records >> simp[] >>
  qexists_tac `CARD (IMAGE sw_out (set ds))` >>
  simp[] >> simp[Abbr `ds`, ptr_liveat_descriptor_budget]
QED

Theorem ptr_liveat_production_reachable:
  EVERY (\b. b.bb_instructions <> []) fn.fn_blocks /\
  (!nm. OL alloc_to (mems nm)) /\
  sw_seed (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
    (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) T x /\
  RTC (sw_edge (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
    (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post))) x lbl ==>
  MEM a (ml_lookup
    (FST (ml_iterate_fuel (concretize_memloc_fuel fn) bp mems sizes pallocas cfg fn FEMPTY FEMPTY))
    (lbl,0))
Proof
  strip_tac >>
  simp[ptr_liveat_fuel_endpoints] >>
  qmatch_goalsub_abbrev_tac `sw_rounds ds` >>
  `sw_consistent ds` by
    (simp[Abbr `ds`] >> irule ml_scan_blocks_consistent >> simp[ml_boundary_desc_out]) >>
  `T IN sw_rounds ds (CARD (IMAGE sw_out (set ds))) lbl` by
    (irule sw_rounds_reachable >> simp[] >> metis_tac[]) >>
  `sw_le (sw_rounds ds (CARD (IMAGE sw_out (set ds))))
      (sw_rounds ds (concretize_memloc_fuel fn))` by
    (irule sw_rounds_mono >> simp[] >>
     simp[Abbr `ds`] >> mp_tac ptr_liveat_descriptor_budget >> decide_tac) >>
  metis_tac[sw_le_def, SUBSET_DEF]
QED

Theorem ptr_liveat_production_reachable_records:
  EVERY (\b. b.bb_instructions <> []) fn.fn_blocks /\
  (!nm. OL alloc_to (mems nm)) /\
  MEM bb (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post) /\
  i < LENGTH bb.bb_instructions /\
  ml_liveat_record_bit a bp mems sizes bb.bb_label (bb.bb_label,i)
    (MAPi (\j inst. (j,inst)) bb.bb_instructions)
    (?lbl x. MEM lbl (cfg_succs_of cfg bb.bb_label) /\
      sw_seed (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
        (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post)) T x /\
      RTC (sw_edge (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
        (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post))) x lbl) F ==>
  MEM a (ml_lookup
    (FST (ml_iterate_fuel (concretize_memloc_fuel fn) bp mems sizes pallocas cfg fn FEMPTY FEMPTY))
    (bb.bb_label,i))
Proof
  strip_tac >>
  irule ptr_liveat_production_records >> simp[] >>
  qexists_tac `CARD (IMAGE sw_out (set (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
    (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post))))` >>
  `sw_consistent (MAP (ml_liveat_boundary_desc a bp mems sizes cfg)
    (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_post))` by
    (irule ml_scan_blocks_consistent >> simp[ml_boundary_desc_out]) >>
  qpat_x_assum `ml_liveat_record_bit _ _ _ _ _ _ _ _ _` mp_tac >>
  once_rewrite_tac[ml_liveat_record_bit_affine] >>
  metis_tac[sw_rounds_reachable]
QED
