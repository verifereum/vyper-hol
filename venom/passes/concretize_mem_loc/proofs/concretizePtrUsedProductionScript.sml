Theory concretizePtrUsedProduction
Ancestors
  concretizePtrUsedDemand concretizeMemLocDefs concretizeAnalysisLivenessClosure
  finite_map list irSupply

Theorem ptr_used_path_suffix[local]:
  !b. ptr_used_path cfg b (pre ++ h::rest) c ==>
    ptr_used_path cfg h rest c
Proof
  Induct_on `pre` >> simp[ptr_used_path_def] >> metis_tac[]
QED

Theorem ptr_used_path_cycle_erasure:
  !b. ptr_used_path cfg b path c ==>
    ?short. ptr_used_path cfg b short c /\ ALL_DISTINCT short /\
      (!lbl. MEM lbl short ==> MEM lbl path)
Proof
  Induct_on `path`
  >- (simp[ptr_used_path_def] >> qexists_tac `[]` >> simp[ptr_used_path_def]) >>
  simp[ptr_used_path_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `MEM h short`
  >- (`?pre rest. short = pre ++ h::rest` by metis_tac[listTheory.MEM_SPLIT] >>
      gvs[] >> qexists_tac `h::rest` >>
      simp[ptr_used_path_def] >>
      drule ptr_used_path_suffix >>
      fs[listTheory.ALL_DISTINCT_APPEND] >> metis_tac[listTheory.MEM_APPEND, listTheory.MEM]) >>
  qexists_tac `h::short` >> simp[ptr_used_path_def] >> metis_tac[]
QED

Theorem ptr_used_production_path_records:
  EVERY (\b. b.bb_instructions <> []) fn.fn_blocks /\
  MEM seed (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre) /\
  i < LENGTH seed.bb_instructions /\
  ml_used_gen a bp mems (EL i seed.bb_instructions) /\
  ptr_used_path cfg seed.bb_label path pred /\
  (!lbl. MEM lbl path ==> ?b. MEM b (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre) /\
    b.bb_label = lbl /\ b.bb_instructions <> []) /\
  FIND (\b. b.bb_label = bb.bb_label) fn.fn_blocks = SOME bb /\
  MEM bb.bb_label cfg.cfg_dfs_pre /\
  FIND (\b. b.bb_label = pred) fn.fn_blocks = SOME pbb /\
  MEM pred (cfg_preds_of cfg bb.bb_label) /\ j < LENGTH bb.bb_instructions ==>
  MEM a (ml_lookup
    (SND (ml_iterate_fuel (concretize_memloc_fuel fn) bp mems sizes pallocas cfg fn FEMPTY FEMPTY))
    (bb.bb_label,j))
Proof
  strip_tac >> drule ptr_used_path_cycle_erasure >> strip_tac >>
  `LENGTH short <= LENGTH fn.fn_blocks` by
    (`LENGTH short <= LENGTH (MAP (\b. b.bb_label) fn.fn_blocks)` suffices_by simp[] >>
     irule distinct_members_length_le >> simp[EVERY_MEM] >>
     rpt strip_tac >>
     `?b. MEM b (ml_scan_blocks fn.fn_blocks cfg.cfg_dfs_pre) /\
       b.bb_label = x /\ b.bb_instructions <> []` by metis_tac[] >>
     drule ml_scan_blocks_mem >> strip_tac >>
     simp[MEM_MAP] >> metis_tac[]) >>
  `concretize_memloc_fuel fn = SUC (PRE (concretize_memloc_fuel fn))` by
    simp[concretize_memloc_fuel_def] >>
  qpat_x_assum `concretize_memloc_fuel fn = _` (fn th => once_rewrite_tac[th]) >>
  irule ptr_used_fuel_path_records >> simp[] >>
  qexistsl_tac [`i`, `short`, `pbb`, `pred`, `seed`] >>
  simp[concretize_memloc_fuel_def] >> decide_tac
QED

Theorem ptr_used_production_seed_records:
  !la us.
  MEM bb.bb_label cfg.cfg_dfs_pre /\
  FIND (\b. b.bb_label = bb.bb_label) fn.fn_blocks = SOME bb /\
  i <= j /\ j < LENGTH bb.bb_instructions /\
  ml_used_gen a bp mems (EL i bb.bb_instructions) ==>
  MEM a (ml_lookup
    (SND (ml_iterate_fuel (concretize_memloc_fuel fn) bp mems sizes pallocas cfg fn la us))
    (bb.bb_label,j))
Proof
  rpt strip_tac >>
  `concretize_memloc_fuel fn = SUC (PRE (concretize_memloc_fuel fn))` by
    simp[concretize_memloc_fuel_def] >>
  qpat_x_assum `concretize_memloc_fuel fn = _` (fn th => once_rewrite_tac[th]) >>
  irule ptr_used_fuel_seed_records >> simp[] >> metis_tac[]
QED
